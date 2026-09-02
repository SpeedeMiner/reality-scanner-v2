// reality-scanner-sni-v6
package main

import (
	"context"
	"crypto/tls"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"net/netip"
	"os"
	"os/signal"
	"regexp"
	"sort"
	"strings"
	"sync"
	"syscall"
	"time"

	mdns "github.com/miekg/dns"
	utls "github.com/refraction-networking/utls"
)

const (
	maxIPs        = 262144
	tlsTimeout    = 3000 * time.Millisecond
	workerDefault = 30

	DNSQueryTimeoutDefault = 1500 * time.Millisecond
	DNSCooldownBase        = 2 * time.Second
	DNSCooldownMax         = 30 * time.Second
	DNSMaxAttemptsA        = 4
	DNSResolutionBudgetA   = 4500 * time.Millisecond
	DNSWarmupTimeout       = 900 * time.Millisecond
	DNSAdaptiveTimeoutMin  = 700 * time.Millisecond
	DNSAdaptiveTimeoutMax  = 1500 * time.Millisecond
	DNSHealthWindowSize    = 32
	DNSHealthWindowMin     = 8
	DNSHealthBadRate       = 0.90
	DNSHealthDegradedRate  = 0.20
	DNSHealthHardBadRate   = 1.0
	DNSHealthBadCooldown   = 10 * time.Second
	DNSDoHTimeout          = 1200 * time.Millisecond

	DefaultDNSResolvers = "1.1.1.1,1.0.0.1,8.8.8.8,8.8.4.4,9.9.9.9,149.112.112.112,208.67.222.222,208.67.220.220,94.140.14.140,94.140.14.141,84.200.69.80,84.200.70.40,77.88.8.8,77.88.8.1,9.9.9.10,149.112.112.10,9.9.9.11,149.112.112.11,185.222.222.222,185.184.222.222,156.154.70.1,156.154.71.1,185.228.168.9,185.228.169.9,223.5.5.5,223.6.6.6"
)

var (
	bannedTLDs = map[string]bool{
		"crl": true, "ocsp": true, "der": true, "crt": true, "cer": true, "pem": true,
		"arpa": true, "local": true, "internal": true, "invalid": true, "example": true, "test": true, "localhost": true,
	}
	domainRe         = regexp.MustCompile(`^[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(\.[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+$`)
	dnsDoHHTTPClient = &http.Client{Timeout: 1500 * time.Millisecond}
)

type DNSResolverStat struct {
	Attempts int
	Answers  int
	Failures int
	Timeouts int
	IPv4s    int
	RTTMs    float64
}

type DNSHealthWindow struct {
	Samples  [DNSHealthWindowSize]bool
	Head     int
	Count    int
	Failures int
}

type DNSPool struct {
	mu                  sync.Mutex
	stats               map[string]*DNSResolverStat
	health              map[string]*DNSHealthWindow
	cooldown            map[string]time.Time
	disabled            map[string]bool
	inflight            map[string]int
	consecutiveFailures map[string]int
	cursor              int
}

func NewDNSPool(resolvers []string) *DNSPool {
	_ = resolvers
	return &DNSPool{
		stats:               make(map[string]*DNSResolverStat),
		health:              make(map[string]*DNSHealthWindow),
		cooldown:            make(map[string]time.Time),
		disabled:            make(map[string]bool),
		inflight:            make(map[string]int),
		consecutiveFailures: make(map[string]int),
	}
}

func dnsHealthState(hw *DNSHealthWindow) string {
	if hw == nil || hw.Count < DNSHealthWindowMin {
		return "unknown"
	}
	rate := float64(hw.Failures) / float64(hw.Count)
	switch {
	case rate >= DNSHealthHardBadRate:
		return "disabled"
	case rate >= DNSHealthBadRate:
		return "cooldown"
	case rate >= DNSHealthDegradedRate:
		return "degraded"
	default:
		return "healthy"
	}
}

func (p *DNSPool) order(resolvers []string) []string {
	p.mu.Lock()
	defer p.mu.Unlock()
	if len(resolvers) == 0 {
		return nil
	}
	now := time.Now()
	type choice struct {
		name   string
		score  float64
		offset int
	}
	good := make([]choice, 0, len(resolvers))
	degraded := make([]choice, 0, len(resolvers))
	start := p.cursor % len(resolvers)
	p.cursor = (start + 1) % len(resolvers)
	for i := 0; i < len(resolvers); i++ {
		r := resolvers[(start+i)%len(resolvers)]
		if p.disabled[r] {
			continue
		}
		if until := p.cooldown[r]; !until.IsZero() && now.Before(until) {
			continue
		}
		rtt := 250.0
		attempts := 0.0
		if st := p.stats[r]; st != nil {
			if st.RTTMs > 0 {
				rtt = st.RTTMs
			}
			attempts = float64(st.Attempts)
		}
		score := float64(p.inflight[r])*2000.0 + attempts*0.02 + rtt
		c := choice{r, score, i}
		if dnsHealthState(p.health[r]) == "degraded" || dnsHealthState(p.health[r]) == "cooldown" {
			degraded = append(degraded, c)
		} else {
			good = append(good, c)
		}
	}
	less := func(a, b choice) bool {
		if a.score == b.score {
			return a.offset < b.offset
		}
		return a.score < b.score
	}
	sort.SliceStable(good, func(i, j int) bool { return less(good[i], good[j]) })
	sort.SliceStable(degraded, func(i, j int) bool { return less(degraded[i], degraded[j]) })
	out := make([]string, 0, len(good)+len(degraded))
	for _, c := range good {
		out = append(out, c.name)
	}
	for _, c := range degraded {
		out = append(out, c.name)
	}
	return out
}

func (p *DNSPool) begin(r string) { p.mu.Lock(); p.inflight[r]++; p.mu.Unlock() }
func (p *DNSPool) end(r string) {
	p.mu.Lock()
	if n := p.inflight[r]; n <= 1 {
		delete(p.inflight, r)
	} else {
		p.inflight[r] = n - 1
	}
	p.mu.Unlock()
}

func (p *DNSPool) record(r string, err error, elapsed time.Duration, ipv4 int) {
	p.mu.Lock()
	defer p.mu.Unlock()
	st := p.stats[r]
	if st == nil {
		st = &DNSResolverStat{}
		p.stats[r] = st
	}
	st.Attempts++
	ms := float64(elapsed.Microseconds()) / 1000.0
	if st.RTTMs == 0 {
		st.RTTMs = ms
	} else {
		st.RTTMs = st.RTTMs*0.8 + ms*0.2
	}
	if err == nil {
		st.Answers++
		st.IPv4s += ipv4
		p.recordHealthLocked(r, false)
		p.consecutiveFailures[r] = 0
		delete(p.cooldown, r)
		return
	}
	var rcodeErr *DNSRCODEError
	if errors.Is(err, errDNSNXDomain) || errors.As(err, &rcodeErr) {
		p.recordHealthLocked(r, false)
		p.consecutiveFailures[r] = 0
		delete(p.cooldown, r)
		return
	}
	st.Failures++
	if errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err) {
		st.Timeouts++
	}
	hwRate := p.recordHealthLocked(r, true)
	p.consecutiveFailures[r]++
	n := p.consecutiveFailures[r]
	if hwRate >= DNSHealthHardBadRate && len(p.health[r].Samples) > 0 {
		p.disabled[r] = true
		delete(p.cooldown, r)
		return
	}
	if hwRate >= DNSHealthBadRate {
		p.cooldown[r] = time.Now().Add(DNSHealthBadCooldown)
		return
	}
	cool := DNSCooldownBase
	for i := 1; i < n; i++ {
		cool *= 2
		if cool >= DNSCooldownMax {
			cool = DNSCooldownMax
			break
		}
	}
	if cool > DNSCooldownMax {
		cool = DNSCooldownMax
	}
	if !errors.Is(err, context.DeadlineExceeded) && cool > 5*time.Second {
		cool = 5 * time.Second
	}
	p.cooldown[r] = time.Now().Add(cool)
}

func (p *DNSPool) recordHealthLocked(r string, failed bool) float64 {
	hw := p.health[r]
	if hw == nil {
		hw = &DNSHealthWindow{}
		p.health[r] = hw
	}
	if hw.Count == DNSHealthWindowSize {
		if hw.Samples[hw.Head] {
			hw.Failures--
		}
	} else {
		hw.Count++
	}
	hw.Samples[hw.Head] = failed
	if failed {
		hw.Failures++
	}
	hw.Head = (hw.Head + 1) % DNSHealthWindowSize
	if hw.Count >= DNSHealthWindowMin {
		return float64(hw.Failures) / float64(hw.Count)
	}
	return 0
}

func (p *DNSPool) timeout(r string, fallback time.Duration) time.Duration {
	p.mu.Lock()
	defer p.mu.Unlock()
	if st := p.stats[r]; st != nil && st.RTTMs > 0 {
		d := time.Duration(st.RTTMs*4) * time.Millisecond
		if d < DNSAdaptiveTimeoutMin {
			d = DNSAdaptiveTimeoutMin
		}
		if d > DNSAdaptiveTimeoutMax {
			d = DNSAdaptiveTimeoutMax
		}
		return d
	}
	if fallback < DNSAdaptiveTimeoutMin {
		return DNSAdaptiveTimeoutMin
	}
	if fallback > DNSAdaptiveTimeoutMax {
		return DNSAdaptiveTimeoutMax
	}
	return fallback
}

type Config struct {
	Workers   int
	MaxIPs    int
	TargetIP  string
	TargetASN string
	Country   string
	Seed      int64
	JSON      bool
}

type SNIResult struct {
	IP   string   `json:"ip"`
	SNI  []string `json:"sni"`
	CN   []string `json:"certificate_cn,omitempty"`
	Sans int      `json:"certificate_sans"`
}

func isPublicDomainSNI(s string) bool {
	s = strings.ToLower(strings.TrimSpace(strings.TrimSuffix(s, ".")))
	if !isDomainSNI(s) {
		return false
	}
	if strings.HasSuffix(s, ".local") || strings.HasSuffix(s, ".invalid") ||
		s == "localhost" || strings.HasPrefix(s, "localhost.") {
		return false
	}
	return true
}

func isDomainSNI(s string) bool {
	s = strings.TrimSpace(strings.TrimSuffix(s, "."))
	if s == "" || net.ParseIP(s) != nil {
		return false
	}
	if !strings.Contains(s, ".") {
		return false
	}
	for _, r := range s {
		if r == ' ' || r == '/' || r == ':' || r == '\\' || r == '@' {
			return false
		}
	}
	return true
}

func cleanDomain(s string) string {
	return strings.ToLower(strings.TrimSpace(strings.TrimSuffix(s, ".")))
}

func uniqueStrings(in []string) []string {
	set := make(map[string]struct{}, len(in))
	out := make([]string, 0, len(in))
	for _, s := range in {
		if _, ok := set[s]; ok {
			continue
		}
		set[s] = struct{}{}
		out = append(out, s)
	}
	return out
}

func uniqueSorted(in []string) []string {
	set := make(map[string]struct{}, len(in))
	for _, s := range in {
		s = cleanDomain(s)
		if !isDomainSNI(s) {
			continue
		}
		set[s] = struct{}{}
	}
	out := make([]string, 0, len(set))
	for s := range set {
		out = append(out, s)
	}
	sort.Strings(out)
	return out
}

type dnsSNIClass uint8

const (
	dnsSNIUnknown dnsSNIClass = iota
	dnsSNIMatchesTarget
	dnsSNIDoesNotMatchTarget
)

var errDNSNXDomain = errors.New("NXDOMAIN")
var errDNSTruncated = errors.New("DNS truncated response")

type DNSRCODEError struct {
	Code int
	Name string
}

func (e *DNSRCODEError) Error() string { return fmt.Sprintf("DNS RCODE=%s", e.Name) }

func normalizeDNSResolvers(values []string) []string {
	seen := make(map[string]struct{})
	out := make([]string, 0, len(values))
	for _, v := range values {
		v = strings.TrimSpace(v)
		if v == "" {
			continue
		}
		if h, _, err := net.SplitHostPort(v); err == nil {
			v = h
		}
		ip := net.ParseIP(v)
		if ip == nil || ip.To4() == nil {
			continue
		}
		v = ip.To4().String()
		if _, ok := seen[v]; ok {
			continue
		}
		seen[v] = struct{}{}
		out = append(out, v)
	}
	return out
}

func buildDNSMessage(domain string, qtype uint16) *mdns.Msg {
	m := new(mdns.Msg)
	m.SetQuestion(mdns.Fqdn(domain), qtype)
	m.RecursionDesired = true
	m.SetEdns0(1232, true)
	return m
}

func dnsExchange(ctx context.Context, resolver, domain string, qtype uint16, timeout time.Duration, network string) ([]string, error) {
	msg := buildDNSMessage(domain, qtype)
	client := &mdns.Client{Net: network, Timeout: timeout}
	resp, _, err := client.ExchangeContext(ctx, msg, net.JoinHostPort(resolver, "53"))
	if err != nil {
		return nil, err
	}
	if resp == nil {
		return nil, fmt.Errorf("nil DNS response")
	}
	if resp.Truncated && network == "udp" {
		return nil, errDNSTruncated
	}
	if resp.Rcode == mdns.RcodeNameError {
		return nil, errDNSNXDomain
	}
	if resp.Rcode != mdns.RcodeSuccess {
		return nil, &DNSRCODEError{Code: resp.Rcode, Name: mdns.RcodeToString[resp.Rcode]}
	}
	ips := make([]string, 0, len(resp.Answer))
	for _, rr := range resp.Answer {
		a, ok := rr.(*mdns.A)
		if !ok || a == nil || a.A == nil {
			continue
		}
		if ip := a.A.To4(); ip != nil {
			ips = append(ips, ip.String())
		}
	}
	return uniqueStrings(ips), nil
}

func warmDNSPool(ctx context.Context, resolvers []string, p *DNSPool) int {
	var wg sync.WaitGroup
	var mu sync.Mutex
	healthy := 0
	for _, r := range resolvers {
		r := r
		wg.Add(1)
		go func() {
			defer wg.Done()
			qctx, cancel := context.WithTimeout(ctx, DNSWarmupTimeout)
			start := time.Now()
			p.begin(r)
			ips, err := dnsExchange(qctx, r, "example.com", mdns.TypeA, DNSWarmupTimeout, "udp")
			if errors.Is(err, errDNSTruncated) {
				ips, err = dnsExchange(qctx, r, "example.com", mdns.TypeA, DNSWarmupTimeout, "tcp")
			}
			p.end(r)
			p.record(r, err, time.Since(start), len(ips))
			cancel()
			if err == nil && len(ips) > 0 {
				mu.Lock()
				healthy++
				mu.Unlock()
			}
		}()
	}
	wg.Wait()
	return healthy
}

func resolveADoHSNI(ctx context.Context, domain string, timeout time.Duration) ([]string, error) {
	bctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	endpoints := []string{"https://dns.google/resolve", "https://cloudflare-dns.com/dns-query", "https://dns.mullvad.net/dns-query", "https://freedns.controld.com/p0"}
	type result struct {
		ips []string
		err error
		nx  bool
	}
	ch := make(chan result, len(endpoints))
	for _, ep := range endpoints {
		ep := ep
		go func() {
			u := ep + "?name=" + urlQueryEscape(domain) + "&type=A"
			req, err := http.NewRequestWithContext(bctx, http.MethodGet, u, nil)
			if err != nil {
				ch <- result{err: err}
				return
			}
			req.Header.Set("Accept", "application/dns-json")
			resp, err := dnsDoHHTTPClient.Do(req)
			if err != nil {
				ch <- result{err: err}
				return
			}
			defer resp.Body.Close()
			if resp.StatusCode < 200 || resp.StatusCode >= 300 {
				ch <- result{err: fmt.Errorf("DoH status=%d", resp.StatusCode)}
				return
			}
			var payload struct {
				Status int `json:"Status"`
				Answer []struct {
					Type int    `json:"type"`
					Data string `json:"data"`
				} `json:"Answer"`
			}
			if err := json.NewDecoder(io.LimitReader(resp.Body, 1<<20)).Decode(&payload); err != nil {
				ch <- result{err: err}
				return
			}
			if payload.Status == 3 {
				ch <- result{nx: true}
				return
			}
			if payload.Status != 0 {
				ch <- result{err: fmt.Errorf("DoH DNS status=%d", payload.Status)}
				return
			}
			ips := make([]string, 0, len(payload.Answer))
			for _, a := range payload.Answer {
				if a.Type == 1 {
					if ip := net.ParseIP(strings.TrimSpace(a.Data)); ip != nil && ip.To4() != nil {
						ips = append(ips, ip.To4().String())
					}
				}
			}
			ch <- result{ips: uniqueStrings(ips)}
		}()
	}
	var lastErr error
	nx := 0
	for range endpoints {
		select {
		case r := <-ch:
			if len(r.ips) > 0 {
				return r.ips, nil
			}
			if r.nx {
				nx++
			} else if r.err != nil {
				lastErr = r.err
			}
		case <-bctx.Done():
			lastErr = bctx.Err()
		}
	}
	if nx == len(endpoints) {
		return nil, errDNSNXDomain
	}
	if lastErr == nil {
		lastErr = fmt.Errorf("DoH fallback failed")
	}
	return nil, lastErr
}

func urlQueryEscape(s string) string { return (&urlEscapeHelper{}).escape(s) }

type urlEscapeHelper struct{}

func (*urlEscapeHelper) escape(s string) string {
	var b strings.Builder
	const hex = "0123456789ABCDEF"
	for i := 0; i < len(s); i++ {
		c := s[i]
		if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || strings.ContainsRune("-_.~", rune(c)) {
			b.WriteByte(c)
		} else {
			b.WriteByte('%')
			b.WriteByte(hex[c>>4])
			b.WriteByte(hex[c&15])
		}
	}
	return b.String()
}

func resolveASystemSNI(ctx context.Context, domain string) ([]string, error) {
	qctx, cancel := context.WithTimeout(ctx, 1200*time.Millisecond)
	defer cancel()
	addrs, err := net.DefaultResolver.LookupIPAddr(qctx, domain)
	if err != nil {
		return nil, err
	}
	ips := make([]string, 0, len(addrs))
	for _, a := range addrs {
		if ip := a.IP.To4(); ip != nil {
			ips = append(ips, ip.String())
		}
	}
	return uniqueStrings(ips), nil
}

func resolveSNIHostA(ctx context.Context, domain string, targetIP string, resolvers []string, p *DNSPool) ([]string, error) {
	rctx, cancel := context.WithTimeout(ctx, DNSResolutionBudgetA)
	defer cancel()
	ordered := p.order(resolvers)
	if len(ordered) > DNSMaxAttemptsA {
		ordered = ordered[:DNSMaxAttemptsA]
	}
	var lastErr error
	for _, r := range ordered {
		start := time.Now()
		timeout := p.timeout(r, DNSQueryTimeoutDefault)
		p.begin(r)
		ips, err := dnsExchange(rctx, r, domain, mdns.TypeA, timeout, "udp")
		if errors.Is(err, errDNSTruncated) {
			ips, err = dnsExchange(rctx, r, domain, mdns.TypeA, timeout, "tcp")
		}
		p.end(r)
		p.record(r, err, time.Since(start), len(ips))
		if err == nil && len(ips) > 0 {
			return ips, nil
		}
		if err != nil && !errors.Is(err, errDNSNXDomain) {
			lastErr = err
		}
		if rctx.Err() != nil {
			break
		}
	}
	if ips, err := resolveADoHSNI(rctx, domain, DNSDoHTimeout); err == nil && len(ips) > 0 {
		return ips, nil
	} else if err != nil {
		lastErr = err
	}
	if ips, err := resolveASystemSNI(rctx, domain); err == nil && len(ips) > 0 {
		return ips, nil
	} else if err != nil {
		lastErr = err
	}
	if lastErr != nil {
		return nil, lastErr
	}
	return nil, fmt.Errorf("DNS no A data")
}

func classifySNIByDNS(ctx context.Context, host, targetIP string, resolvers []string, pool *DNSPool) dnsSNIClass {
	ips, err := resolveSNIHostA(ctx, host, targetIP, resolvers, pool)
	if err != nil || len(ips) == 0 {
		return dnsSNIUnknown
	}
	target, err := netip.ParseAddr(targetIP)
	if err != nil {
		return dnsSNIUnknown
	}
	hasIPv4 := false
	for _, ip := range ips {
		addr, err := netip.ParseAddr(ip)
		if err != nil || !addr.Is4() {
			continue
		}
		hasIPv4 = true
		if addr == target {
			return dnsSNIMatchesTarget
		}
	}
	if hasIPv4 {
		return dnsSNIDoesNotMatchTarget
	}
	return dnsSNIUnknown
}

func fakeSNINames(ctx context.Context, ip string, names []string, resolvers []string, pool *DNSPool) []string {
	out := make([]string, 0, len(names))
	for _, name := range uniqueSorted(names) {
		name = cleanDomain(name)
		if !isPublicDomainSNI(name) {
			continue
		}
		if classifySNIByDNS(ctx, name, ip, resolvers, pool) != dnsSNIDoesNotMatchTarget {
			continue
		}
		out = append(out, name)
	}
	return out
}

func getASN(ip string) string {
	client := &http.Client{Timeout: 6 * time.Second}
	resp, err := client.Get(fmt.Sprintf("https://stat.ripe.net/data/network-info/data.json?resource=%s", ip))
	if err == nil {
		defer resp.Body.Close()
		if resp.StatusCode == http.StatusOK {
			var v struct {
				Data struct {
					ASNs []interface{} `json:"asns"`
				} `json:"data"`
			}
			if json.NewDecoder(io.LimitReader(resp.Body, 1<<20)).Decode(&v) == nil && len(v.Data.ASNs) > 0 {
				asn := fmt.Sprintf("%v", v.Data.ASNs[0])
				if !strings.HasPrefix(strings.ToUpper(asn), "AS") {
					asn = "AS" + asn
				}
				return strings.ToUpper(asn)
			}
		}
	}
	return "UNKNOWN_ASN"
}

func getCountry(ip string) string {
	client := &http.Client{Timeout: 4 * time.Second}
	resp, err := client.Get(fmt.Sprintf("http://ip-api.com/json/%s?fields=countryCode", ip))
	if err != nil {
		return "UNKNOWN"
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "UNKNOWN"
	}
	var v struct {
		CountryCode string `json:"countryCode"`
	}
	if err := json.NewDecoder(io.LimitReader(resp.Body, 1<<20)).Decode(&v); err != nil || v.CountryCode == "" {
		return "UNKNOWN"
	}
	return strings.ToUpper(v.CountryCode)
}

func getPrefixes(asn string) []string {
	if asn == "UNKNOWN_ASN" {
		return nil
	}
	client := &http.Client{Timeout: 6 * time.Second}
	resp, err := client.Get(fmt.Sprintf("https://stat.ripe.net/data/announced-prefixes/data.json?resource=%s", asn))
	if err != nil {
		return nil
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil
	}
	var v struct {
		Data struct {
			Prefixes []struct {
				Prefix string `json:"prefix"`
			} `json:"prefixes"`
		} `json:"data"`
	}
	if err := json.NewDecoder(io.LimitReader(resp.Body, 2<<20)).Decode(&v); err != nil {
		return nil
	}
	out := make([]string, 0, len(v.Data.Prefixes))
	for _, p := range v.Data.Prefixes {
		if !strings.Contains(p.Prefix, ":") {
			out = append(out, p.Prefix)
		}
	}
	return out
}

func sampleIPs(prefixes []string, max int) []string {
	set := make(map[string]struct{})
	for _, p := range prefixes {
		ip, n, err := net.ParseCIDR(p)
		if err != nil || ip.To4() == nil {
			continue
		}
		start := ip.To4()
		if max <= 0 {
			max = maxIPs
		}
		for cur := append(net.IP(nil), start...); n.Contains(cur); incIPv4(cur) {
			set[cur.String()] = struct{}{}
			if len(set) >= max {
				break
			}
		}
		if len(set) >= max {
			break
		}
	}
	out := make([]string, 0, len(set))
	for ip := range set {
		out = append(out, ip)
	}
	sort.Strings(out)
	return out
}

func incIPv4(ip net.IP) {
	for i := len(ip) - 1; i >= len(ip)-4; i-- {
		ip[i]++
		if ip[i] != 0 {
			return
		}
	}
}

func discoverSNI(ctx context.Context, ip string, resolvers []string, pool *DNSPool) *SNIResult {
	res := &SNIResult{IP: ip}
	d := &net.Dialer{Timeout: tlsTimeout}
	conn, err := d.DialContext(ctx, "tcp", net.JoinHostPort(ip, "443"))
	if err != nil {
		return res
	}
	defer conn.Close()

	u := utls.UClient(conn, &utls.Config{
		ServerName:         ip,
		InsecureSkipVerify: true,
		MinVersion:         tls.VersionTLS13,
		MaxVersion:         tls.VersionTLS13,
	}, utls.HelloChrome_Auto)
	if err := u.SetDeadline(time.Now().Add(tlsTimeout)); err != nil {
		return res
	}
	if err := u.HandshakeContext(ctx); err != nil {
		return res
	}
	st := u.ConnectionState()
	if len(st.PeerCertificates) == 0 {
		return res
	}
	cert := st.PeerCertificates[0]
	rawNames := append(append([]string{}, cert.DNSNames...), cert.Subject.CommonName)
	res.CN = uniqueSorted([]string{cert.Subject.CommonName})
	res.Sans = len(cert.DNSNames)
	res.SNI = fakeSNINames(ctx, ip, rawNames, resolvers, pool)
	return res
}

func runDiscovery(ctx context.Context, ips []string, workers int, resolvers []string, pool *DNSPool) []SNIResult {
	if workers < 1 {
		workers = 1
	}
	if workers > len(ips) {
		workers = len(ips)
	}
	jobs := make(chan string)
	results := make(chan SNIResult, workers)
	var wg sync.WaitGroup
	for i := 0; i < workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for ip := range jobs {
				if ctx.Err() != nil {
					return
				}
				r := discoverSNI(ctx, ip, resolvers, pool)
				if len(r.SNI) > 0 {
					results <- *r
				}
			}
		}()
	}
	go func() {
		for _, ip := range ips {
			select {
			case jobs <- ip:
			case <-ctx.Done():
				close(jobs)
				return
			}
		}
		close(jobs)
	}()

	go func() {
		wg.Wait()
		close(results)
	}()

	byIP := make(map[string][]string)
	for r := range results {
		byIP[r.IP] = append(byIP[r.IP], r.SNI...)
	}
	out := make([]SNIResult, 0, len(byIP))
	for ip, names := range byIP {
		names = uniqueSorted(names)
		if len(names) == 0 {
			continue
		}
		out = append(out, SNIResult{IP: ip, SNI: names})
	}
	sort.Slice(out, func(i, j int) bool { return out[i].IP < out[j].IP })
	return out
}

func main() {
	cfg := Config{Workers: workerDefault, MaxIPs: 6144}
	flag.IntVar(&cfg.Workers, "w", workerDefault, "Worker pool size")
	flag.IntVar(&cfg.MaxIPs, "max-ips", 6144, "Maximum sampled IPv4 addresses")
	flag.StringVar(&cfg.TargetIP, "vps-ip", "", "VPS IPv4")
	flag.BoolVar(&cfg.JSON, "json", false, "JSONL output")
	flag.Parse()
	if cfg.Workers < 1 {
		cfg.Workers = 1
	}
	if cfg.MaxIPs < 1 || cfg.MaxIPs > maxIPs {
		cfg.MaxIPs = 6144
	}
	parsed := net.ParseIP(strings.TrimSpace(cfg.TargetIP)).To4()
	if parsed == nil {
		log.Fatal("[-] Нужен корректный IPv4 через -vps-ip")
	}
	cfg.TargetIP = parsed.String()
	cfg.TargetASN = getASN(cfg.TargetIP)
	if cfg.TargetASN == "UNKNOWN_ASN" {
		log.Fatalf("[-] Не удалось определить ASN для %s", cfg.TargetIP)
	}
	cfg.Country = getCountry(cfg.TargetIP)
	prefixes := getPrefixes(cfg.TargetASN)
	if len(prefixes) == 0 {
		log.Fatalf("[-] Не удалось получить announced prefixes для %s", cfg.TargetASN)
	}
	ips := sampleIPs(prefixes, cfg.MaxIPs)
	if len(ips) == 0 {
		log.Fatal("[-] Пул IP пуст")
	}

	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()

	resolverParts := strings.Split(DefaultDNSResolvers, ",")
	resolvers := normalizeDNSResolvers(resolverParts)
	dnsPool := NewDNSPool(resolvers)
	healthyResolvers := warmDNSPool(ctx, resolvers, dnsPool)
	fmt.Printf("[*] DNS pool:           %d resolvers (%d warm)\n", len(resolvers), healthyResolvers)

	fmt.Printf("[*] Режим: SNI discovery\n")
	fmt.Printf("[*] Целевой VPS IP:     %s\n", cfg.TargetIP)
	fmt.Printf("[*] Announcing ASN:     %s\n", cfg.TargetASN)
	fmt.Printf("[*] Страна сервера:     %s\n", cfg.Country)
	fmt.Printf("[*] IP в активном пуле: %d\n", len(ips))
	fmt.Printf("[*] Workers:            %d\n", cfg.Workers)
	fmt.Printf("[*] Проверка сертификата: ОТКЛЮЧЕНА\n")
	fmt.Printf("[*] DNS:                 пул resolvers из v98\n\n")

	results := runDiscovery(ctx, ips, cfg.Workers, resolvers, dnsPool)
	if cfg.JSON {
		for _, r := range results {
			b, _ := json.Marshal(r)
			fmt.Println(string(b))
		}
		return
	}

	fmt.Printf("[+] Найдено IP с доменными SNI: %d\n\n", len(results))
	fmt.Printf("%-15s | %s\n", "IP адрес", "SNI")
	fmt.Println(strings.Repeat("-", 110))
	for _, r := range results {
		fmt.Printf("%-15s | %s\n", r.IP, strings.Join(r.SNI, ", "))
	}
}
