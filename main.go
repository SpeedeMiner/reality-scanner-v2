package main

import (
	"context"
	"crypto/tls"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"os"
	"os/signal"
	"sort"
	"strings"
	"sync"
	"syscall"
	"time"

	utls "github.com/refraction-networking/utls"
)

const (
	maxIPs        = 262144
	tlsTimeout    = 3000 * time.Millisecond
	workerDefault = 30
)

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

func discoverSNI(ctx context.Context, ip string) *SNIResult {
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
	res.CN = uniqueSorted([]string{cert.Subject.CommonName})
	res.Sans = len(cert.DNSNames)
	res.SNI = uniqueSorted(append(append([]string{}, cert.DNSNames...), cert.Subject.CommonName))
	return res
}

func runDiscovery(ctx context.Context, ips []string, workers int) []SNIResult {
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
				r := discoverSNI(ctx, ip)
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

	fmt.Printf("[*] Режим: SNI discovery\n")
	fmt.Printf("[*] Целевой VPS IP:     %s\n", cfg.TargetIP)
	fmt.Printf("[*] Announcing ASN:     %s\n", cfg.TargetASN)
	fmt.Printf("[*] Страна сервера:     %s\n", cfg.Country)
	fmt.Printf("[*] IP в активном пуле: %d\n", len(ips))
	fmt.Printf("[*] Workers:            %d\n", cfg.Workers)
	fmt.Printf("[*] Проверка сертификата: ОТКЛЮЧЕНА\n")
	fmt.Printf("[*] OSINT/DNS/H2 validation: ОТКЛЮЧЕНЫ\n\n")

	results := runDiscovery(ctx, ips, cfg.Workers)
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
