package main

// reality-scanner-active-v92: modular active scanner

import (
	"bufio"
	"bytes"
	"context"
	"crypto/tls"
	"crypto/x509"
	"encoding/binary"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log"
	"math"
	"math/rand"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	mdns "github.com/miekg/dns"
	utls "github.com/refraction-networking/utls"
	"golang.org/x/net/http2"
	"golang.org/x/net/http2/hpack"
	"golang.org/x/sync/singleflight"

	discovery "reality-scanner/internal/discovery"
	output "reality-scanner/internal/output"
	ratelimit "reality-scanner/internal/ratelimit"
	scanning "reality-scanner/internal/scanning"
)

var progressJSON bool

func progressf(format string, args ...any) {
	w := io.Writer(os.Stdout)
	if progressJSON {
		w = os.Stderr
	}
	fmt.Fprintf(w, format, args...)
}

func progressln(args ...any) {
	w := io.Writer(os.Stdout)
	if progressJSON {
		w = os.Stderr
	}
	fmt.Fprintln(w, args...)
}

// ================= CONFIG & CONSTANTS =================

const (
	FrameData         = 0x00
	FrameHeaders      = 0x01
	FrameRSTStream    = 0x03
	FrameSettings     = 0x04
	FrameGoAway       = 0x07
	FrameWindowUpdate = 0x08
	FrameContinuation = 0x09

	LimitMaxIPs     = 262144
	LimitValidPairs = 10000
	ChaosMaxNames   = 10000

	DNSQueryTimeoutDefault = 1500 * time.Millisecond
	PTRQueryTimeoutDefault = 1000 * time.Millisecond
	DNSCooldownBase        = 2 * time.Second
	DNSCooldownMax         = 30 * time.Second
	DNSMaxAttemptsA        = 4
	DNSMaxAttemptsPTR      = 6
	DNSResolutionBudgetA   = 4500 * time.Millisecond
	DNSResolutionBudgetPTR = 6000 * time.Millisecond
	DNSWarmupTimeout       = 900 * time.Millisecond
	DNSAdaptiveTimeoutMin  = 700 * time.Millisecond
	DNSAdaptiveTimeoutMax  = 1500 * time.Millisecond
	DNSHealthWindowSize    = 32
	DNSHealthWindowMin     = 8
	DNSHealthWindowBadRate = 0.90
	DNSHealthDegradedRate  = 0.20
	DNSHealthHardBadRate   = 1.0
	DNSHealthBadCooldown   = 10 * time.Second
	PTRDoHTimeout          = 1200 * time.Millisecond
	DefaultECSIPv4Prefix   = 24
	MaxH2BufferedBytes     = 9 + 16384
	MaxH2HeaderBlockBytes  = 64 * 1024
	MaxSNIPairsPerIP       = 25

	DefaultDNSResolvers = "1.1.1.1,1.0.0.1,8.8.8.8,8.8.4.4,9.9.9.9,149.112.112.112,208.67.222.222,208.67.220.220,94.140.14.140,94.140.14.141,84.200.69.80,84.200.70.40,77.88.8.8,77.88.8.1,9.9.9.10,149.112.112.10,9.9.9.11,149.112.112.11,185.222.222.222,185.184.222.222,156.154.70.1,156.154.71.1,185.228.168.9,185.228.169.9,223.5.5.5,223.6.6.6"
)

var (
	bannedTLDs = map[string]bool{
		"crl": true, "ocsp": true, "der": true, "crt": true, "cer": true, "pem": true,
		"arpa": true, "local": true, "internal": true, "invalid": true, "example": true, "test": true, "localhost": true,
	}

	cdnStrong = []string{"cloudflare", "fastly", "akamai", "ddos-guard", "qrator", "sucuri"}
	cdnWeak   = []string{"x-cache", "x-served-by", "x-edge"}
	junkTLDs  = []string{".xyz", ".top", ".site", ".fun", ".online", ".space", ".pw", ".cc", ".icu", ".click", ".win", ".bid", ".date"}
	dynDNS    = []string{"duckdns.org", "mooo.com", "ddns.net", "freeddns.org", "crabdance.com", "eu.org", "cloudns.cc", "hopto.org", "zapto.org", "sytes.net", "dyn.com", "no-ip.org"}

	domainRe = regexp.MustCompile(`^[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(\.[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+$`)
	numRe    = regexp.MustCompile(`(?i)(^|\.)\d+\.[a-z]{2,}$`)

	ErrDNSNXDomain  = errors.New("NXDOMAIN")
	ErrDNSNoData    = errors.New("DNS no data")
	ErrDNSTruncated = errors.New("DNS truncated response")

	uaRng        *rand.Rand
	uaMu         sync.Mutex
	probeLimiter *ratelimit.Limiter

	dnsDoHHTTPClient = &http.Client{
		Transport: &http.Transport{
			MaxIdleConns:          64,
			MaxIdleConnsPerHost:   16,
			IdleConnTimeout:       30 * time.Second,
			TLSHandshakeTimeout:   900 * time.Millisecond,
			ResponseHeaderTimeout: 1200 * time.Millisecond,
		},
	}
	ipOSINTHTTPClient = &http.Client{
		Transport: &http.Transport{
			MaxIdleConns:        32,
			MaxIdleConnsPerHost: 16,
			IdleConnTimeout:     30 * time.Second,
			TLSHandshakeTimeout: 2 * time.Second,
		},
	}
	shodanOSINTSem  = make(chan struct{}, 10)
	vtOSINTSem      = make(chan struct{}, 2)
	shodanOSINTRate = ratelimit.New(10)
	vtOSINTRate     = ratelimit.New(1)
)

type Config struct {
	Workers           int
	IPOSINTLimit      int
	VTKey             string
	ChaosKey          string
	MaxIPs            int
	DNSWorkers        int
	DNSQueryTimeoutMs int
	ECSIP             string
	ECSPrefix         int
	DNSResolvers      []string
	TCPTimeoutMs      int
	TLSTimeoutMs      int
	H2ReadTimeoutMs   int
	H2WriteTimeoutMs  int
	Seed              int64
	TargetASN         string
	TargetCountry     string
	TargetIP          string
	Rate              float64
	JSON              bool
	Checkpoint        string
	Resume            bool
}

// ================= EVIDENCE =================

type DomainSource uint32

const (
	SourceSeed DomainSource = 1 << iota
	SourcePTR
	SourceDirectTLS
	SourceShodan
	SourceVirusTotalIP
)

func (s DomainSource) Has(flag DomainSource) bool { return s&flag != 0 }

func (e Evidence) Combined() DomainSource { return e.Direct | e.Inherited }

type Evidence struct {
	Direct    DomainSource
	Inherited DomainSource
}

type Timings struct {
	TCP          time.Duration
	TLS          time.Duration
	H2FirstFrame time.Duration
	H2Headers    time.Duration
}

func (t Timings) TotalProbeLatency() time.Duration { return t.TCP + t.TLS + t.H2Headers }

type PeerSettingsProfile struct {
	HeaderTableSize         uint32
	MaxConcurrentStreams    uint32
	InitialWindowSize       uint32
	MaxFrameSize            uint32
	MaxHeaderListSize       uint32
	HasHeaderTableSize      bool
	HasMaxConcurrentStreams bool
	HasInitialWindowSize    bool
	HasMaxFrameSize         bool
	HasMaxHeaderListSize    bool
}

type RealityScore struct {
	TLSQuality     float64
	Certificate    float64
	H2Profile      float64
	ServerProfile  float64
	HTTPBehavior   float64
	DiscoveryScore float64
	Latency        float64
	Total          float64
}

type CDNStatus string

const (
	CDNConfirmed     CDNStatus = "Confirmed"
	CDNLikely        CDNStatus = "Likely"
	CDNStatusUnknown CDNStatus = "Unknown"
)

type Candidate struct {
	IP                    string
	SNI                   string
	ALPN                  string
	TLSCurve              string
	X25519                bool
	RealityFeasible       bool
	CertExpiry            time.Time
	H2HeadersReceived     bool
	ResponseHeadersParsed bool
	ResponseTrailersSeen  bool
	H2ProtocolConfirmed   bool
	TLS13                 bool
	HTTPStatus            int
	Location              string
	BodyBytes             int
	Server                string
	ContentType           string
	Timings               Timings
	CDNProvider           string
	CDNStatus             CDNStatus
	Score                 float64
	DomainPenalty         float64
	RealityScore          RealityScore
	CertChainValid        bool
	EndStreamSeen         bool
	StreamReset           bool
	GoAwaySeen            bool
	Evidence              Evidence
	DomainQuality         string
	CertIssuer            string
	CertValidTime         bool
	CertSNIMatch          bool
	SettingsAckCount      int
	SettingsChanges       int
	H2SettingsReceived    bool
	H2SettingsAckSent     bool
	H2SettingsAckReceived bool
	InitialPeerSettings   PeerSettingsProfile
	LatestPeerSettings    PeerSettingsProfile
	H2DataFrames          int
	HPACKErrors           bool
	MissingStatus         bool
	ReadTimeout           bool
}

type TargetPair struct {
	IP       string
	SNI      string
	Evidence Evidence
}

// ================= TELEMETRY & CACHES =================

type PipelineStats struct {
	mu                    sync.Mutex
	IPSampled             int
	PTRFound              int
	PTRSystemFallbacks    int
	PTRDoHFallbacks       int
	PTRNegativeResponses  int
	DNSQueries            int
	DNSSuccess            int
	DNSFailed             int
	DNSNXDomain           int
	DNSTimeout            int
	DNSTemporary          int
	DNSNoIPv4             int
	DNSOtherErr           int
	DNSRCODEErrors        int
	DNSOtherNetworkErr    int
	DNSOtherMalformed     int
	DNSOtherShortResponse int
	DNSOtherTxIDMismatch  int
	DNSOtherUnsupported   int
	DNSOtherNotFound      int
	DNSOtherUnknown       int
	DNSResolvedIPs        int
	DNSUniqueResolvedIPs  int
	DNSUniqueTargetIPs    int
	DNSTargetRangeMatches int
	DNSTargetDomains      int
	DNSValidPairs         int
	PairLimitDrops        int

	TCPConnected int
	TCPTimeouts  int
	TCPRefused   int
	TCPOtherErrs int

	TLSHandshake          int
	TLSTimeouts           int
	TLSValidationFailures int
	NoPeerCertificates    int
	TLSHandshakeFailure   int
	TLSUnrecognizedName   int
	TLSConnectionReset    int
	TLSEOF                int
	TLSOtherErrs          int

	H2NoALPN                 int
	H2ProtocolOK             int
	H2TimeoutNoFrames        int
	H2ConnectionReset        int
	H2BrokenPipe             int
	H2BadRequest             int
	H2GoAway                 int
	H2EOF                    int
	H2TLSAlerts              int
	H2OtherErrs              int
	H2InvalidFrame           int
	H2InvalidFrameLength     int
	H2FrameHeaderImplausible int
	H2InvalidFrameRSTLength  int
	H2InvalidFrameStreamID   int
	H2InvalidFramePadding    int
	H2InvalidFramePreface    int
	H2BadContinuation        int
	H2HPACKDecode            int
	H2MissingSettings        int
	H2HeadersWithoutStatus   int
	H2HeadersOK              int
	H2Timeouts               int
	H2HPACKErrors            int
	H2StatusOK               int
	H2InvalidStatus          int
	EndStreamOK              int

	ScoreRejected             int
	LowScoreCandidates        int
	CandidatesAccepted        int
	RealityFeasibleCandidates int
	ASNFiltered               int
}

func NewPipelineStats() *PipelineStats { return &PipelineStats{} }

func (s *PipelineStats) incH2Reason(kind string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.H2OtherErrs++
	switch kind {
	case "invalid-frame":
		s.H2InvalidFrame++
	case "bad-continuation":
		s.H2BadContinuation++
	case "hpack-decode":
		s.H2HPACKDecode++
	case "missing-settings":
		s.H2MissingSettings++
	case "headers-without-status":
		s.H2HeadersWithoutStatus++
	}
}

type DNSResolverStat struct {
	Attempts    int
	Answers     int
	NXDomain    int
	RCODEErrors int
	Failures    int
	Timeouts    int
	IPv4s       int
	RTTMs       float64
}

type DNSHealthWindow struct {
	Samples  [DNSHealthWindowSize]bool
	Head     int
	Count    int
	Failures int
}

type RuntimeCaches struct {
	DNSCache               *SafeDNSCache
	DNSGroup               *singleflight.Group
	DNSStatsMu             sync.Mutex
	DNSResolverStats       map[string]*DNSResolverStat
	DNSRoundRobinCursor    int
	DNSCooldownUntil       map[string]time.Time
	DNSConsecutiveFailures map[string]int
	DNSDisabledForRun      map[string]bool
	DNSHealthWindows       map[string]*DNSHealthWindow

	// It prevents one root cancellation from aborting a request shared by other roots.

	// PTR fallback telemetry. Access under DNSStatsMu.
	PTRSystemFallbacks     int
	PTRDoHFallbacks        int
	PTRNegativeResponses   int
	PTRResolverNXResponses int
	PTRNegativeIPs         map[string]struct{}
	DNSDoHFallbacks        int
	DNSSystemFallbacks     int
}

func NewRuntimeCaches() *RuntimeCaches {
	return &RuntimeCaches{
		DNSCache:               NewSafeDNSCache(),
		DNSGroup:               &singleflight.Group{},
		DNSResolverStats:       make(map[string]*DNSResolverStat),
		PTRNegativeIPs:         make(map[string]struct{}),
		DNSCooldownUntil:       make(map[string]time.Time),
		DNSConsecutiveFailures: make(map[string]int),
		DNSDisabledForRun:      make(map[string]bool),
		DNSHealthWindows:       make(map[string]*DNSHealthWindow),
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
	case rate >= DNSHealthWindowBadRate:
		return "cooldown"
	case rate >= DNSHealthDegradedRate:
		return "degraded"
	default:
		return "healthy"
	}
}

func (r *RuntimeCaches) dnsResolverOrder(resolvers []string) []string {
	if len(resolvers) == 0 {
		return nil
	}
	now := time.Now()
	r.DNSStatsMu.Lock()
	defer r.DNSStatsMu.Unlock()

	start := r.DNSRoundRobinCursor % len(resolvers)
	if start < 0 {
		start = 0
	}
	r.DNSRoundRobinCursor = (start + 1) % len(resolvers)

	var healthy, degraded []string
	for i := 0; i < len(resolvers); i++ {
		resolver := resolvers[(start+i)%len(resolvers)]
		if r.DNSDisabledForRun[resolver] {
			continue
		}
		until := r.DNSCooldownUntil[resolver]
		if !until.IsZero() && now.Before(until) {
			continue
		}
		switch dnsHealthState(r.DNSHealthWindows[resolver]) {
		case "degraded", "cooldown":
			degraded = append(degraded, resolver)
		default:
			healthy = append(healthy, resolver)
		}
	}

	if len(healthy)+len(degraded) == 0 {
		// Do not immediately reuse a resolver that is still in cooldown. Returning
		// nil lets the caller use its bounded fallback transports instead of
		// defeating the cooldown and recreating the failure spiral.
		return nil
	}

	// Prefer healthy resolvers exclusively while enough healthy capacity exists.
	// The old interleaving policy deliberately injected degraded resolvers into
	// every lookup, which caused avoidable timeout amplification even when many
	// healthy resolvers were available. Degraded resolvers remain a bounded
	// reserve and are used only after the healthy set is exhausted.
	order := make([]string, 0, len(healthy)+len(degraded))
	order = append(order, healthy...)
	order = append(order, degraded...)
	return order
}

func (r *RuntimeCaches) recordDNSHealthLocked(resolver string, transportFailure bool) float64 {
	hw := r.DNSHealthWindows[resolver]
	if hw == nil {
		hw = &DNSHealthWindow{}
		r.DNSHealthWindows[resolver] = hw
	}
	if hw.Count == DNSHealthWindowSize {
		if hw.Samples[hw.Head] {
			hw.Failures--
		}
	} else {
		hw.Count++
	}
	hw.Samples[hw.Head] = transportFailure
	if transportFailure {
		hw.Failures++
	}
	hw.Head = (hw.Head + 1) % DNSHealthWindowSize
	if hw.Count >= DNSHealthWindowMin {
		return float64(hw.Failures) / float64(hw.Count)
	}
	return 0
}

func (r *RuntimeCaches) recordDNSResult(resolver string, err error, elapsed time.Duration, ipv4Count int) {
	r.DNSStatsMu.Lock()
	defer r.DNSStatsMu.Unlock()

	stat, ok := r.DNSResolverStats[resolver]
	if !ok {
		stat = &DNSResolverStat{}
		r.DNSResolverStats[resolver] = stat
	}

	stat.Attempts++
	elapsedMs := float64(elapsed.Microseconds()) / 1000.0
	if stat.RTTMs == 0 {
		stat.RTTMs = elapsedMs
	} else {
		stat.RTTMs = stat.RTTMs*0.8 + elapsedMs*0.2
	}

	if err == nil {
		stat.Answers++
		if ipv4Count > 0 {
			stat.IPv4s += ipv4Count
		}
		// A received DNS response proves transport health even when it has no A records.
		r.recordDNSHealthLocked(resolver, false)
		r.DNSConsecutiveFailures[resolver] = 0
		delete(r.DNSCooldownUntil, resolver)
		return
	}
	if errors.Is(err, ErrDNSNXDomain) {
		stat.NXDomain++
		// NXDOMAIN is a valid DNS response and MUST NOT count as transport failure.
		r.recordDNSHealthLocked(resolver, false)
		r.DNSConsecutiveFailures[resolver] = 0
		delete(r.DNSCooldownUntil, resolver)
		return
	}
	var rcodeErr *DNSRCODEError
	if errors.As(err, &rcodeErr) {
		// FORMERR/SERVFAIL/REFUSED/etc. proves that the resolver answered.
		// Count it separately, but never quarantine the transport for a DNS-layer RCODE.
		stat.RCODEErrors++
		r.recordDNSHealthLocked(resolver, false)
		r.DNSConsecutiveFailures[resolver] = 0
		delete(r.DNSCooldownUntil, resolver)
		return
	}

	stat.Failures++
	isTimeout := errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err)
	if isTimeout {
		stat.Timeouts++
	}

	n := r.DNSConsecutiveFailures[resolver] + 1
	r.DNSConsecutiveFailures[resolver] = n

	// Use only a bounded recent transport-health window for run quarantine.
	// Historical cumulative failure ratios must never re-quarantine a resolver
	// immediately after its cooldown expires.
	healthFailureRate := r.recordDNSHealthLocked(resolver, true)
	hw := r.DNSHealthWindows[resolver]
	if hw != nil && hw.Count >= DNSHealthWindowMin {
		if healthFailureRate >= DNSHealthHardBadRate {
			r.DNSDisabledForRun[resolver] = true
			delete(r.DNSCooldownUntil, resolver)
			return
		}
		if healthFailureRate >= DNSHealthWindowBadRate {
			cooldownUntil := time.Now().Add(DNSHealthBadCooldown)
			r.DNSCooldownUntil[resolver] = cooldownUntil
			return
		}
	}

	cooldown := DNSCooldownBase
	for i := 1; i < n; i++ {
		cooldown *= 2
		if cooldown >= DNSCooldownMax {
			cooldown = DNSCooldownMax
			break
		}
	}
	if !isTimeout && cooldown > 5*time.Second {
		cooldown = 5 * time.Second
	}
	if cooldown > DNSCooldownMax {
		cooldown = DNSCooldownMax
	}
	cooldownUntil := time.Now().Add(cooldown)
	r.DNSCooldownUntil[resolver] = cooldownUntil
}

type DNSCacheEntry struct {
	IPs      []string
	NXDomain bool
	Expires  time.Time
}

type SafeDNSCache struct {
	mu   sync.RWMutex
	data map[string]*DNSCacheEntry
}

func NewSafeDNSCache() *SafeDNSCache {
	return &SafeDNSCache{data: make(map[string]*DNSCacheEntry)}
}
func (c *SafeDNSCache) Get(key string) (*DNSCacheEntry, bool) {
	c.mu.RLock()
	v, ok := c.data[key]
	c.mu.RUnlock()
	if !ok {
		return nil, false
	}
	if time.Now().After(v.Expires) {
		c.mu.Lock()
		if v2, ok2 := c.data[key]; ok2 && time.Now().After(v2.Expires) {
			delete(c.data, key)
		}
		c.mu.Unlock()
		return nil, false
	}
	var ips []string
	if v.IPs != nil {
		ips = append([]string(nil), v.IPs...)
	}
	return &DNSCacheEntry{IPs: ips, NXDomain: v.NXDomain}, true
}
func (c *SafeDNSCache) Put(key string, entry *DNSCacheEntry, ttl time.Duration) {
	c.mu.Lock()
	defer c.mu.Unlock()
	var ips []string
	if entry.IPs != nil {
		ips = append([]string(nil), entry.IPs...)
	}
	c.data[key] = &DNSCacheEntry{IPs: ips, NXDomain: entry.NXDomain, Expires: time.Now().Add(ttl)}
}

// ================= DNS TRANSPORT =================
// Raw UDP/53 with EDNS Client Subnet is the fast path; TCP is used only for
// genuinely truncated responses. DoH and the system resolver are bounded fallbacks.
// Resolver health is based only on the recent sliding window and never on lifetime ratios.

// ================= RAW UDP DNS + EDNS CLIENT SUBNET =================

// Raw DNS resolver used for both passive PTR discovery and ECS A lookups.
// No net.LookupHost and no DNSCrypt are used in the pipeline.

func normalizeDNSResolvers(values []string) []string {
	var out []string
	seen := make(map[string]struct{})
	for _, v := range values {
		v = strings.TrimSpace(v)
		if v == "" {
			continue
		}
		if host, _, err := net.SplitHostPort(v); err == nil {
			v = host
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

func buildMiekgDNSMessage(domain string, qtype uint16, ecsIP string, ecsPrefix int) (*mdns.Msg, error) {
	m := new(mdns.Msg)
	m.SetQuestion(mdns.Fqdn(domain), qtype)
	m.RecursionDesired = true
	// Keep UDP payload conservative; fall back to TCP on truncation.
	m.SetEdns0(1232, true)
	if qtype == mdns.TypeA && ecsIP != "" {
		ip := net.ParseIP(ecsIP)
		if ip == nil || ip.To4() == nil {
			return nil, fmt.Errorf("invalid ECS IPv4: %q", ecsIP)
		}
		if ecsPrefix < 0 || ecsPrefix > 32 {
			return nil, fmt.Errorf("invalid ECS IPv4 prefix length: %d", ecsPrefix)
		}
		ip4 := ip.To4()
		subnet := &mdns.EDNS0_SUBNET{
			Code:          mdns.EDNS0SUBNET,
			Family:        1,
			SourceNetmask: uint8(ecsPrefix),
			SourceScope:   0,
			Address:       ip4,
		}
		opt := m.IsEdns0()
		if opt == nil {
			return nil, fmt.Errorf("failed to create EDNS0 OPT")
		}
		opt.Option = append(opt.Option, subnet)
	}
	return m, nil
}

type DNSRCODEError struct {
	Code int
	Name string
}

func (e *DNSRCODEError) Error() string {
	if e == nil {
		return "DNS server returned RCODE"
	}
	if e.Name != "" {
		return fmt.Sprintf("DNS server returned RCODE=%s", e.Name)
	}
	return fmt.Sprintf("DNS server returned RCODE=%d", e.Code)
}

func parseDNSAResponse(msg *mdns.Msg) ([]string, error) {
	if msg == nil {
		return nil, fmt.Errorf("nil DNS response")
	}
	if msg.Rcode == mdns.RcodeNameError {
		return nil, ErrDNSNXDomain
	}
	if msg.Rcode != mdns.RcodeSuccess {
		return nil, &DNSRCODEError{Code: msg.Rcode, Name: mdns.RcodeToString[msg.Rcode]}
	}
	ips := make([]string, 0, len(msg.Answer))
	for _, rr := range msg.Answer {
		a, ok := rr.(*mdns.A)
		if !ok || a == nil || a.A == nil {
			continue
		}
		ip := a.A.To4()
		if ip != nil {
			ips = append(ips, ip.String())
		}
	}
	return uniqueStrings(ips), nil
}

func parseDNSPTRResponse(msg *mdns.Msg) ([]string, error) {
	if msg == nil {
		return nil, fmt.Errorf("nil DNS response")
	}
	if msg.Rcode == mdns.RcodeNameError {
		return nil, ErrDNSNXDomain
	}
	if msg.Rcode != mdns.RcodeSuccess {
		return nil, &DNSRCODEError{Code: msg.Rcode, Name: mdns.RcodeToString[msg.Rcode]}
	}
	names := make([]string, 0, len(msg.Answer))
	for _, rr := range msg.Answer {
		ptr, ok := rr.(*mdns.PTR)
		if !ok || ptr == nil {
			continue
		}
		if d := CleanDomain(ptr.Ptr); d != "" {
			names = append(names, d)
		}
	}
	return uniqueStrings(names), nil
}

func dnsExchange(ctx context.Context, resolver, domain string, qtype uint16, ecsIP string, ecsPrefix int, timeout time.Duration, network string) ([]string, error) {
	msg, err := buildMiekgDNSMessage(domain, qtype, ecsIP, ecsPrefix)
	if err != nil {
		return nil, err
	}
	client := &mdns.Client{Net: network, Timeout: timeout}
	resp, _, err := client.ExchangeContext(ctx, msg, net.JoinHostPort(resolver, "53"))
	if err != nil {
		return nil, err
	}
	if resp == nil {
		return nil, fmt.Errorf("nil DNS response")
	}
	if qtype == mdns.TypePTR {
		return parseDNSPTRResponse(resp)
	}
	return parseDNSAResponse(resp)
}

func dnsExchangeTCP(ctx context.Context, resolver, domain string, qtype uint16, ecsIP string, ecsPrefix int, timeout time.Duration) ([]string, error) {
	return dnsExchange(ctx, resolver, domain, qtype, ecsIP, ecsPrefix, timeout, "tcp")
}

func dnsExchangeUDP(ctx context.Context, resolver, domain string, qtype uint16, ecsIP string, ecsPrefix int, timeout time.Duration) ([]string, error) {
	// Build the DNS message exactly once and reuse it for the UDP exchange.
	msg, err := buildMiekgDNSMessage(domain, qtype, ecsIP, ecsPrefix)
	if err != nil {
		return nil, err
	}
	client := &mdns.Client{Net: "udp", Timeout: timeout}
	resp, _, err := client.ExchangeContext(ctx, msg, net.JoinHostPort(resolver, "53"))
	if err != nil {
		return nil, err
	}
	if resp == nil {
		err = fmt.Errorf("nil DNS response")
		return nil, err
	}
	if resp.Truncated {
		return nil, ErrDNSTruncated
	}
	var out []string
	if qtype == mdns.TypePTR {
		out, err = parseDNSPTRResponse(resp)
	} else {
		out, err = parseDNSAResponse(resp)
	}
	return out, err
}

func warmDNSResolvers(ctx context.Context, resolvers []string, ecsIP string, ecsPrefix int, rtCaches *RuntimeCaches) {
	if len(resolvers) == 0 {
		return
	}
	type result struct {
		resolver string
		healthy  bool
	}
	results := make(chan result, len(resolvers))
	var wg sync.WaitGroup

	for _, resolver := range resolvers {
		resolver := resolver
		wg.Add(1)
		go func() {
			defer wg.Done()

			// Warm-up answers one real A query. A resolver is considered healthy
			// when it can complete a normal DNS exchange within the transport
			// budget. We deliberately DO NOT require a particular NXDOMAIN policy:
			// public resolvers legitimately differ in handling reserved/invalid
			// names, and that must not quarantine an otherwise healthy transport.
			healthy := false
			started := time.Now()
			qctx, cancel := context.WithTimeout(ctx, DNSWarmupTimeout)
			ips, err := dnsExchangeUDP(qctx, resolver, "example.com", mdns.TypeA, ecsIP, ecsPrefix, DNSWarmupTimeout)
			if errors.Is(err, ErrDNSTruncated) {
				tcpCtx, tcpCancel := context.WithTimeout(ctx, DNSWarmupTimeout)
				if tcpIPs, tcpErr := dnsExchangeTCP(tcpCtx, resolver, "example.com", mdns.TypeA, ecsIP, ecsPrefix, DNSWarmupTimeout); tcpErr == nil {
					ips, err = tcpIPs, nil
				} else {
					err = tcpErr
				}
				tcpCancel()
			}
			rtCaches.recordDNSResult(resolver, err, time.Since(started), len(ips))
			cancel()

			if err == nil && len(ips) > 0 {
				healthy = true
			} else {
				// One bounded secondary positive query reduces false negatives caused
				// by an ECS-specific answer path for a single name, without adding a
				// blocking delay to Stage C.
				qctx2, cancel2 := context.WithTimeout(ctx, DNSWarmupTimeout)
				started = time.Now()
				ips2, err2 := dnsExchangeUDP(qctx2, resolver, "www.cloudflare.com", mdns.TypeA, ecsIP, ecsPrefix, DNSWarmupTimeout)
				if errors.Is(err2, ErrDNSTruncated) {
					if tcpIPs, tcpErr := dnsExchangeTCP(qctx2, resolver, "www.cloudflare.com", mdns.TypeA, ecsIP, ecsPrefix, DNSWarmupTimeout); tcpErr == nil {
						ips2, err2 = tcpIPs, nil
					}
				}
				rtCaches.recordDNSResult(resolver, err2, time.Since(started), len(ips2))
				cancel2()
				healthy = err2 == nil && len(ips2) > 0
			}

			if !healthy {
				// Warm-up failure is temporary evidence only. Do not permanently
				// disable a resolver before the scan has started; transport failures
				// are handled by recordDNSResult with normal cooldown/backoff.
				rtCaches.DNSStatsMu.Lock()
				if !rtCaches.DNSDisabledForRun[resolver] {
					rtCaches.DNSCooldownUntil[resolver] = time.Now().Add(DNSCooldownBase)
				}
				rtCaches.DNSStatsMu.Unlock()
			}
			results <- result{resolver: resolver, healthy: healthy}
		}()
	}
	wg.Wait()
	close(results)

	healthy := 0
	for res := range results {
		if res.healthy {
			healthy++
		}
	}
	progressf("[DNS] Warm-up: %d/%d resolvers healthy for this run\n", healthy, len(resolvers))
}

func (r *RuntimeCaches) dnsResolverTimeout(resolver string, fallback time.Duration) time.Duration {
	r.DNSStatsMu.Lock()
	defer r.DNSStatsMu.Unlock()
	if st := r.DNSResolverStats[resolver]; st != nil && st.RTTMs > 0 {
		d := time.Duration(st.RTTMs*4.0) * time.Millisecond
		if d < DNSAdaptiveTimeoutMin {
			d = DNSAdaptiveTimeoutMin
		}
		if d > DNSAdaptiveTimeoutMax {
			d = DNSAdaptiveTimeoutMax
		}
		return d
	}
	if fallback <= 0 {
		return DNSQueryTimeoutDefault
	}
	if fallback < DNSAdaptiveTimeoutMin {
		return DNSAdaptiveTimeoutMin
	}
	if fallback > DNSAdaptiveTimeoutMax {
		return DNSAdaptiveTimeoutMax
	}
	return fallback
}

func resolveHostECS(ctx context.Context, domain, ecsIP string, ecsPrefix int, resolvers []string, timeout time.Duration, rtCaches *RuntimeCaches) ([]string, error) {
	resolutionCtx, resolutionCancel := context.WithTimeout(ctx, DNSResolutionBudgetA)
	defer resolutionCancel()
	ctx = resolutionCtx
	domain = CleanDomain(domain)
	if domain == "" {
		return nil, fmt.Errorf("invalid domain")
	}
	if ecsIP == "" {
		return nil, fmt.Errorf("ECS client IP is empty")
	}
	if len(resolvers) == 0 {
		return nil, fmt.Errorf("DNS resolver pool is empty")
	}
	if timeout <= 0 {
		timeout = DNSQueryTimeoutDefault
	}

	ordered := rtCaches.dnsResolverOrder(resolvers)
	if len(ordered) > DNSMaxAttemptsA {
		ordered = ordered[:DNSMaxAttemptsA]
	}
	var lastErr error
	bestErr := error(nil)
	bestPriority := -1
	nxCount := 0
	emptyCount := 0
	rcodeCount := 0

	rememberErr := func(err error) {
		if err == nil {
			return
		}
		pri := dnsErrorPriority(err)
		if pri > bestPriority {
			bestPriority = pri
			bestErr = err
		}
		lastErr = err
	}

	for _, resolver := range ordered {
		started := time.Now()
		resolverTimeout := rtCaches.dnsResolverTimeout(resolver, timeout)
		ips, err := dnsExchangeUDP(ctx, resolver, domain, mdns.TypeA, ecsIP, ecsPrefix, resolverTimeout)

		// TCP is only a truncation fallback. A UDP timeout must not spend another
		// synchronous timeout budget against the same resolver.
		if errors.Is(err, ErrDNSTruncated) {
			tcpIPs, tcpErr := dnsExchangeTCP(ctx, resolver, domain, mdns.TypeA, ecsIP, ecsPrefix, resolverTimeout)
			if tcpErr == nil {
				ips, err = tcpIPs, nil
			} else {
				err = tcpErr
			}
		}
		rtCaches.recordDNSResult(resolver, err, time.Since(started), len(ips))

		if err == nil {
			if len(ips) > 0 {
				return ips, nil
			}
			emptyCount++
			continue
		}
		if errors.Is(err, ErrDNSNXDomain) {
			nxCount++
			continue
		}
		var rcodeErr *DNSRCODEError
		if errors.As(err, &rcodeErr) {
			rcodeCount++
			rememberErr(err)
			continue
		}
		rememberErr(err)
		if ctx.Err() != nil {
			return nil, ctx.Err()
		}
	}

	// DoH is a fallback transport, not a reason to replace the primary DNS
	// error in telemetry. Only a successful fallback changes the result.
	if dohIPs, dohErr := resolveADoH(ctx, domain, ecsIP, ecsPrefix, PTRDoHTimeout); dohErr == nil && len(dohIPs) > 0 {
		rtCaches.DNSStatsMu.Lock()
		rtCaches.DNSDoHFallbacks++
		rtCaches.DNSStatsMu.Unlock()
		return dohIPs, nil
	} else if dohErr != nil {
		// DoH is a fallback transport. Its own failure must not replace the
		// primary raw-UDP diagnostic or turn a transport failure into a bogus
		// name-not-found/unknown telemetry bucket.
	}

	if sysIPs, sysErr := resolveASystem(ctx, domain); sysErr == nil && len(sysIPs) > 0 {
		rtCaches.DNSStatsMu.Lock()
		rtCaches.DNSSystemFallbacks++
		rtCaches.DNSStatsMu.Unlock()
		return sysIPs, nil
	} else if sysErr != nil {
		// The system resolver is also a fallback. Do not let its error mask the
		// raw DNS transport failure that determined the actual lookup outcome.
	}

	if nxCount > 0 && emptyCount+nxCount == len(ordered) {
		return nil, ErrDNSNXDomain
	}
	if bestErr != nil {
		kind := classifyDNSOtherError(bestErr)
		if kind == "unknown" {
			if errors.Is(bestErr, context.DeadlineExceeded) || os.IsTimeout(bestErr) {
				kind = "timeout"
			} else if rcodeCount > 0 {
				kind = "rcode"
			}
		}
		return nil, &DNSAggregateError{Kind: kind, Err: bestErr}
	}
	if lastErr != nil {
		return nil, &DNSAggregateError{Kind: classifyDNSOtherError(lastErr), Err: lastErr}
	}
	return nil, ErrDNSNoData
}

func resolvePTRRaw(ctx context.Context, ip string, resolvers []string, timeout time.Duration, rtCaches *RuntimeCaches) ([]string, error) {
	resolutionCtx, resolutionCancel := context.WithTimeout(ctx, DNSResolutionBudgetPTR)
	defer resolutionCancel()
	ctx = resolutionCtx
	rev, err := reverseIPv4(ip)
	if err != nil {
		return nil, err
	}

	// The old Linux scanner got PTRs through a mature recursive resolver pool.
	// In the raw-UDP build, UDP/53 from a VPS can be selectively filtered while
	// the local/system resolver still has working access to the reverse zone.
	// Try the system resolver first: it is the fastest compatibility path and
	// preserves the old scanner's PTR behavior without giving up raw DNS.
	lookupCtx, cancel := context.WithTimeout(ctx, timeout)
	names, lookupErr := net.DefaultResolver.LookupAddr(lookupCtx, ip)
	cancel()
	if lookupErr == nil && len(names) > 0 {
		clean := make([]string, 0, len(names))
		for _, n := range names {
			if d := CleanDomain(strings.TrimSuffix(strings.TrimSpace(n), ".")); d != "" {
				clean = append(clean, d)
			}
		}
		if len(clean) > 0 {
			rtCaches.DNSStatsMu.Lock()
			rtCaches.PTRSystemFallbacks++
			rtCaches.DNSStatsMu.Unlock()
			return uniqueStrings(clean), nil
		}
	}

	if len(resolvers) == 0 {
		if lookupErr != nil {
			return nil, lookupErr
		}
		return nil, fmt.Errorf("DNS resolver pool is empty")
	}
	if timeout <= 0 {
		timeout = PTRQueryTimeoutDefault
	}

	ordered := rtCaches.dnsResolverOrder(resolvers)
	if len(ordered) > DNSMaxAttemptsPTR {
		ordered = ordered[:DNSMaxAttemptsPTR]
	}
	var lastErr error
	nxCount := 0
	emptyCount := 0
	for _, resolver := range ordered {
		started := time.Now()
		resolverTimeout := rtCaches.dnsResolverTimeout(resolver, timeout)
		names, err := dnsExchangeUDP(ctx, resolver, rev, 12, "", 0, resolverTimeout)
		if errors.Is(err, ErrDNSTruncated) {
			if tcpNames, tcpErr := dnsExchangeTCP(ctx, resolver, rev, 12, "", 0, resolverTimeout); tcpErr == nil {
				names, err = tcpNames, nil
			} else {
				err = tcpErr
			}
		}
		rtCaches.recordDNSResult(resolver, err, time.Since(started), 0)

		if err == nil {
			if len(names) > 0 {
				return names, nil
			}
			emptyCount++
			continue
		}
		if errors.Is(err, ErrDNSNXDomain) {
			nxCount++
			rtCaches.DNSStatsMu.Lock()
			rtCaches.PTRResolverNXResponses++
			rtCaches.DNSStatsMu.Unlock()
			// NXDOMAIN is resolver telemetry, not the final per-IP result. The
			// unique-IP counter is updated only once when all viable fallbacks agree.
			continue
		}
		lastErr = fmt.Errorf("%s: %w", resolver, err)
		if ctx.Err() != nil {
			return nil, ctx.Err()
		}
	}

	if dohNames, dohErr := resolvePTRDoH(ctx, rev, PTRDoHTimeout); dohErr == nil && len(dohNames) > 0 {
		rtCaches.DNSStatsMu.Lock()
		rtCaches.PTRDoHFallbacks++
		rtCaches.DNSStatsMu.Unlock()
		return dohNames, nil
	} else if dohErr != nil && lastErr == nil {
		lastErr = dohErr
	}

	if nxCount == len(ordered) || (nxCount > 0 && emptyCount+nxCount == len(ordered)) {
		rtCaches.DNSStatsMu.Lock()
		rtCaches.PTRNegativeIPs[ip] = struct{}{}
		rtCaches.PTRNegativeResponses = len(rtCaches.PTRNegativeIPs)
		rtCaches.DNSStatsMu.Unlock()
		return nil, ErrDNSNXDomain
	}
	if lastErr == nil {
		lastErr = fmt.Errorf("all DNS resolvers returned no PTR")
	}
	return nil, lastErr
}

func resolveADoH(ctx context.Context, domain, ecsIP string, ecsPrefix int, timeout time.Duration) ([]string, error) {
	if timeout <= 0 {
		timeout = 1200 * time.Millisecond
	}
	budgetCtx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	ecs := ecsIP
	if parsed := net.ParseIP(ecsIP); parsed != nil && parsed.To4() != nil {
		masked := append(net.IP(nil), parsed.To4()...)
		used := (ecsPrefix + 7) / 8
		if used > 0 && ecsPrefix%8 != 0 {
			masked[used-1] &= byte(0xFF << uint(8-(ecsPrefix%8)))
		}
		for i := used; i < 4; i++ {
			masked[i] = 0
		}
		ecs = masked.String() + "/" + strconv.Itoa(ecsPrefix)
	}
	endpoints := []string{"https://dns.google/resolve", "https://cloudflare-dns.com/dns-query", "https://dns.mullvad.net/dns-query", "https://freedns.controld.com/p0"}
	type result struct {
		ips []string
		err error
		nx  bool
	}
	ch := make(chan result, len(endpoints))
	for _, endpoint := range endpoints {
		ep := endpoint
		go func() {
			values := url.Values{}
			values.Set("name", domain)
			values.Set("type", "A")
			if ecs != "" {
				values.Set("edns_client_subnet", ecs)
			}
			req, err := http.NewRequestWithContext(budgetCtx, http.MethodGet, ep+"?"+values.Encode(), nil)
			if err != nil {
				ch <- result{err: err}
				return
			}
			req.Header.Set("Accept", "application/dns-json")
			req.Header.Set("User-Agent", "reality-scanner/1.0")
			resp, err := dnsDoHHTTPClient.Do(req)
			if err != nil {
				ch <- result{err: err}
				return
			}
			defer resp.Body.Close()
			if resp.StatusCode < 200 || resp.StatusCode >= 300 {
				_, _ = io.Copy(io.Discard, io.LimitReader(resp.Body, 4096))
				ch <- result{err: fmt.Errorf("DoH HTTP status=%d", resp.StatusCode)}
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
		case <-budgetCtx.Done():
			if lastErr == nil {
				lastErr = budgetCtx.Err()
			}
		}
	}
	if nx == len(endpoints) {
		return nil, ErrDNSNXDomain
	}
	if lastErr == nil {
		lastErr = fmt.Errorf("DNS A DoH fallback failed")
	}
	return nil, lastErr
}

func resolveASystem(ctx context.Context, domain string) ([]string, error) {
	lookupCtx, cancel := context.WithTimeout(ctx, 1200*time.Millisecond)
	defer cancel()
	addrs, err := net.DefaultResolver.LookupIPAddr(lookupCtx, domain)
	if err != nil {
		return nil, err
	}
	ips := make([]string, 0, len(addrs))
	for _, addr := range addrs {
		if ip := addr.IP.To4(); ip != nil {
			ips = append(ips, ip.String())
		}
	}
	cleanIPs := uniqueStrings(ips)
	return cleanIPs, nil
}

func resolvePTRDoH(ctx context.Context, rev string, timeout time.Duration) ([]string, error) {
	if timeout <= 0 {
		timeout = 1200 * time.Millisecond
	}
	budgetCtx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()

	endpoints := []string{
		"https://dns.google/resolve?name=" + url.QueryEscape(rev) + "&type=PTR",
		"https://cloudflare-dns.com/dns-query?name=" + url.QueryEscape(rev) + "&type=PTR",
	}

	type result struct {
		names []string
		err   error
		nx    bool
	}
	results := make(chan result, len(endpoints))
	for _, endpoint := range endpoints {
		ep := endpoint
		go func() {
			reqCtx, reqCancel := context.WithCancel(budgetCtx)
			defer reqCancel()
			req, err := http.NewRequestWithContext(reqCtx, http.MethodGet, ep, nil)
			if err != nil {
				results <- result{err: err}
				return
			}
			req.Header.Set("Accept", "application/dns-json")
			req.Header.Set("User-Agent", "reality-scanner/1.0")
			resp, err := dnsDoHHTTPClient.Do(req)
			if err != nil {
				results <- result{err: err}
				return
			}
			defer resp.Body.Close()
			if resp.StatusCode < 200 || resp.StatusCode >= 300 {
				_, _ = io.Copy(io.Discard, io.LimitReader(resp.Body, 4096))
				results <- result{err: fmt.Errorf("PTR DoH HTTP status=%d", resp.StatusCode)}
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
				results <- result{err: err}
				return
			}
			if payload.Status == 3 {
				results <- result{nx: true}
				return
			}
			if payload.Status != 0 {
				results <- result{err: fmt.Errorf("DoH DNS status=%d", payload.Status)}
				return
			}

			names := make([]string, 0, len(payload.Answer))
			for _, answer := range payload.Answer {
				if answer.Type != 12 {
					continue
				}
				if d := CleanDomain(strings.TrimSuffix(strings.TrimSpace(answer.Data), ".")); d != "" {
					names = append(names, d)
				}
			}
			results <- result{names: uniqueStrings(names)}
		}()
	}

	var lastErr error
	nxCount := 0
	for remaining := len(endpoints); remaining > 0; remaining-- {
		select {
		case r := <-results:
			if len(r.names) > 0 {
				return r.names, nil
			}
			if r.nx {
				nxCount++
			} else if r.err != nil {
				lastErr = r.err
			}
		case <-budgetCtx.Done():
			if lastErr == nil {
				lastErr = budgetCtx.Err()
			}
			return nil, lastErr
		}
	}
	if nxCount == len(endpoints) {
		return nil, ErrDNSNXDomain
	}
	if lastErr == nil {
		lastErr = fmt.Errorf("PTR DoH fallback failed")
	}
	return nil, lastErr
}

func CleanDomain(d string) string {
	d = strings.ToLower(strings.TrimSpace(strings.TrimPrefix(d, "*.")))
	parts := strings.Split(d, ".")
	if len(parts) < 2 {
		return ""
	}
	tld := parts[len(parts)-1]
	if bannedTLDs[tld] {
		return ""
	}
	if strings.ContainsAny(d, " \t\r\n/\\:*?\"'<>|#%&={}~`!@$^()+[]") {
		return ""
	}
	if !domainRe.MatchString(d) {
		return ""
	}
	return d
}

func limitStr(s string, n int) string {
	if n <= 0 {
		return ""
	}
	r := []rune(s)
	if len(r) <= n {
		return s
	}
	if n <= 3 {
		return string(r[:n])
	}
	return string(r[:n-3]) + "..."
}

func minInt(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func uniqueStrings(values []string) []string {
	seen := make(map[string]bool)
	var result []string
	for _, v := range values {
		if !seen[v] {
			seen[v] = true
			result = append(result, v)
		}
	}
	return result
}

type DNSAggregateError struct {
	Kind string
	Err  error
}

func (e *DNSAggregateError) Error() string {
	if e == nil {
		return "dns aggregate error"
	}
	if e.Err == nil {
		return e.Kind
	}
	return e.Err.Error()
}

func (e *DNSAggregateError) Unwrap() error {
	if e == nil {
		return nil
	}
	return e.Err
}

func dnsErrorPriority(err error) int {
	if err == nil {
		return 0
	}
	if errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err) {
		return 3
	}
	var rcodeErr *DNSRCODEError
	if errors.As(err, &rcodeErr) {
		return 4
	}
	if kind := classifyDNSOtherError(err); kind != "unknown" {
		return 5
	}
	// Unknown final fallback errors are intentionally lowest priority so they
	// cannot overwrite a concrete UDP RCODE/timeout/transport cause.
	return 1
}

func classifyDNSOtherError(err error) string {
	if err == nil {
		return "unknown"
	}
	s := strings.ToLower(err.Error())
	switch {
	case strings.Contains(s, "txid"), strings.Contains(s, "id mismatch"):
		return "txid-mismatch"
	case strings.Contains(s, "short response"), strings.Contains(s, "too short"), strings.Contains(s, "short packet"):
		return "short-response"
	case strings.Contains(s, "invalid packet"), strings.Contains(s, "unpack"), strings.Contains(s, "malformed"), strings.Contains(s, "overflow"), strings.Contains(s, "pack: dns"), strings.Contains(s, "dns: buffer size"):
		return "malformed"
	case strings.Contains(s, "network"), strings.Contains(s, "connection refused"), strings.Contains(s, "no route"), strings.Contains(s, "broken pipe"), strings.Contains(s, "reset by peer"), strings.Contains(s, "connection reset"), strings.Contains(s, "use of closed network connection"):
		return "network"
	case strings.Contains(s, "unexpected eof"), strings.Contains(s, "unexpected end"):
		return "short-response"
	case strings.Contains(s, "unsupported"):
		return "unsupported"
	case strings.Contains(s, "no such host"), strings.Contains(s, "name or service not known"):
		return "name-not-found"
	default:
		return "unknown"
	}
}

func recordDNSPipelineErrorLocked(s *PipelineStats, err error) {
	if s == nil || err == nil {
		return
	}
	if errors.Is(err, ErrDNSNoData) {
		s.DNSSuccess++
		s.DNSNoIPv4++
		return
	}

	// Preserve the aggregate provenance before inspecting the wrapped error.
	// A fallback may wrap a useful primary classification (timeout, RCODE,
	// not-found, malformed, network, ...); unwrapping first used to erase that
	// information and inflate DNS Other/Unknown.
	var aggErr *DNSAggregateError
	if errors.As(err, &aggErr) && aggErr != nil && aggErr.Kind != "" {
		s.DNSFailed++
		switch aggErr.Kind {
		case "timeout":
			s.DNSTimeout++
		case "rcode":
			s.DNSRCODEErrors++
		case "network":
			s.DNSOtherErr++
			s.DNSOtherNetworkErr++
		case "malformed":
			s.DNSOtherErr++
			s.DNSOtherMalformed++
		case "short-response":
			s.DNSOtherErr++
			s.DNSOtherShortResponse++
		case "txid-mismatch":
			s.DNSOtherErr++
			s.DNSOtherTxIDMismatch++
		case "unsupported":
			s.DNSOtherErr++
			s.DNSOtherUnsupported++
		case "name-not-found":
			s.DNSOtherErr++
			s.DNSOtherNotFound++
		default:
			s.DNSOtherErr++
			s.DNSOtherUnknown++
		}
		return
	}

	var rcodeErr *DNSRCODEError
	if errors.As(err, &rcodeErr) {
		s.DNSFailed++
		s.DNSRCODEErrors++
		return
	}
	if errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err) {
		s.DNSFailed++
		s.DNSTimeout++
		return
	}
	var dnsErr *net.DNSError
	if errors.As(err, &dnsErr) {
		s.DNSFailed++
		if dnsErr.Timeout() {
			s.DNSTimeout++
			return
		}
		if dnsErr.Temporary() {
			s.DNSTemporary++
			return
		}
	}

	s.DNSFailed++
	s.DNSOtherErr++
	switch classifyDNSOtherError(err) {
	case "network":
		s.DNSOtherNetworkErr++
	case "malformed":
		s.DNSOtherMalformed++
	case "short-response":
		s.DNSOtherShortResponse++
	case "txid-mismatch":
		s.DNSOtherTxIDMismatch++
	case "unsupported":
		s.DNSOtherUnsupported++
	case "name-not-found":
		s.DNSOtherNotFound++
	default:
		s.DNSOtherUnknown++
	}
}

func classifyDomainQuality(sni string) string {
	sniLower := strings.ToLower(sni)
	for _, tld := range junkTLDs {
		if strings.HasSuffix(sniLower, tld) {
			return "JunkTLD"
		}
	}
	for _, dDNS := range dynDNS {
		if strings.HasSuffix(sniLower, dDNS) {
			return "DynDNS"
		}
	}
	if numRe.MatchString(sniLower) {
		return "Numeric"
	}
	return "Normal"
}

var userAgents = []string{
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
	"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:125.0) Gecko/20100101 Firefox/125.0",
	"Mozilla/5.0 (Macintosh; Intel Mac OS X 10.15; rv:125.0) Gecko/20100101 Firefox/125.0",
}

// ================= CIDR & SAMPLING =================
type ipRange struct{ start, end uint64 }

func MergeCIDRs(cidrs []string) []ipRange {
	var ranges []ipRange
	for _, c := range cidrs {
		_, ipnet, err := net.ParseCIDR(c)
		if err != nil || ipnet.Mask == nil {
			continue
		}
		ones, bits := ipnet.Mask.Size()
		if bits != 32 {
			continue
		}
		var count uint64
		if ones == 0 {
			count = 1 << 32
		} else {
			count = uint64(1) << uint(32-ones)
		}
		startInt := uint64(binary.BigEndian.Uint32(ipnet.IP))
		ranges = append(ranges, ipRange{startInt, startInt + count - 1})
	}
	if len(ranges) == 0 {
		return nil
	}
	sort.Slice(ranges, func(i, j int) bool { return ranges[i].start < ranges[j].start })
	var merged []ipRange
	for _, r := range ranges {
		if len(merged) == 0 {
			merged = append(merged, r)
			continue
		}
		last := &merged[len(merged)-1]
		if r.start <= last.end+1 {
			if r.end > last.end {
				last.end = r.end
			}
		} else {
			merged = append(merged, r)
		}
	}
	return merged
}

func gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func SampleIPs(blocks []ipRange, maxIPs int, seed int64) []string {
	var totalIPs uint64
	for _, b := range blocks {
		totalIPs += (b.end - b.start + 1)
	}
	if totalIPs == 0 {
		return nil
	}
	var sampleSize uint64
	switch {
	case maxIPs < -1:
		return nil
	case maxIPs == -1:
		sampleSize = totalIPs
	case maxIPs == 0:
		sampleSize = 1024
		if sampleSize > totalIPs {
			sampleSize = totalIPs
		}
	default:
		sampleSize = uint64(maxIPs)
		if sampleSize > totalIPs {
			sampleSize = totalIPs
		}
	}
	if sampleSize > LimitMaxIPs {
		sampleSize = LimitMaxIPs
	}
	if sampleSize == 0 {
		return nil
	}
	rng := rand.New(rand.NewSource(seed))
	currIdx := rng.Uint64() % totalIPs
	var step uint64 = 1
	if totalIPs > 1 {
		for {
			step = (rng.Uint64() % (totalIPs - 1)) + 1
			if gcd(step, totalIPs) == 1 {
				break
			}
		}
	}
	var result []string
	for i := uint64(0); i < sampleSize; i++ {
		offset := currIdx
		for _, b := range blocks {
			count := b.end - b.start + 1
			if offset < count {
				ip := make(net.IP, 4)
				binary.BigEndian.PutUint32(ip, uint32(b.start+offset))
				result = append(result, ip.String())
				break
			}
			offset -= count
		}
		currIdx = (currIdx + step) % totalIPs
	}
	return result
}

func ipInRanges(ipStr string, ranges []ipRange) bool {
	parsed := net.ParseIP(ipStr)
	if parsed == nil {
		return false
	}
	ip4 := parsed.To4()
	if ip4 == nil {
		return false
	}
	val := uint64(binary.BigEndian.Uint32(ip4))
	for _, r := range ranges {
		if val >= r.start && val <= r.end {
			return true
		}
	}
	return false
}

func reverseIPv4(ip string) (string, error) {
	parsed := net.ParseIP(ip)
	if parsed == nil {
		return "", fmt.Errorf("invalid IP")
	}
	parsed = parsed.To4()
	if parsed == nil {
		return "", fmt.Errorf("not IPv4")
	}
	return fmt.Sprintf("%d.%d.%d.%d.in-addr.arpa.", parsed[3], parsed[2], parsed[1], parsed[0]), nil
}

func resolveIPv4Cached(ctx context.Context, domain string, rtCaches *RuntimeCaches, cfg Config) ([]string, error) {
	domain = CleanDomain(domain)
	if domain == "" {
		return nil, fmt.Errorf("invalid domain")
	}
	cacheKey := fmt.Sprintf("%s|ecs=%s/%d|dns=%s",
		domain, cfg.ECSIP, cfg.ECSPrefix, strings.Join(cfg.DNSResolvers, ","))

	v, err, _ := rtCaches.DNSGroup.Do(cacheKey, func() (interface{}, error) {
		if cached, ok := rtCaches.DNSCache.Get(cacheKey); ok {
			if cached.NXDomain {
				return nil, ErrDNSNXDomain
			}
			return cached.IPs, nil
		}

		ips, err := resolveHostECS(
			ctx,
			domain,
			cfg.ECSIP,
			cfg.ECSPrefix,
			cfg.DNSResolvers,
			time.Duration(cfg.DNSQueryTimeoutMs)*time.Millisecond,
			rtCaches,
		)
		if err != nil {
			if errors.Is(err, ErrDNSNXDomain) {
				rtCaches.DNSCache.Put(cacheKey, &DNSCacheEntry{NXDomain: true}, 10*time.Second)
			}
			return nil, err
		}

		var valid []string
		for _, ip := range ips {
			if net.ParseIP(ip).To4() != nil {
				valid = append(valid, ip)
			}
		}
		rtCaches.DNSCache.Put(cacheKey, &DNSCacheEntry{IPs: valid}, 10*time.Second)
		return valid, nil
	})
	if err != nil {
		return nil, err
	}
	return v.([]string), nil
}

func buildH2HeadersEncoder(sni string) []byte {
	var buf bytes.Buffer
	enc := hpack.NewEncoder(&buf)
	_ = enc.WriteField(hpack.HeaderField{Name: ":method", Value: "GET"})
	_ = enc.WriteField(hpack.HeaderField{Name: ":scheme", Value: "https"})
	_ = enc.WriteField(hpack.HeaderField{Name: ":path", Value: "/"})
	_ = enc.WriteField(hpack.HeaderField{Name: ":authority", Value: sni})
	_ = enc.WriteField(hpack.HeaderField{Name: "user-agent", Value: "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/151.0.0.0 Safari/537.36"})
	_ = enc.WriteField(hpack.HeaderField{Name: "accept", Value: "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"})
	_ = enc.WriteField(hpack.HeaderField{Name: "accept-encoding", Value: "gzip, deflate, br"})
	return buf.Bytes()
}

func parseResponseHeaders(cand *Candidate, headers []hpack.HeaderField) error {
	weakCount := 0
	hasStatus := false
	finalStatusSeen := cand.ResponseHeadersParsed && cand.HTTPStatus >= 200

	for _, h := range headers {
		hName := strings.ToLower(strings.TrimSpace(h.Name))

		if strings.HasPrefix(hName, ":") && hName != ":status" {
			return fmt.Errorf("unexpected response pseudo-header %q", h.Name)
		}

		if hName == ":status" {
			n, err := strconv.Atoi(strings.TrimSpace(h.Value))
			if err != nil || n < 100 || n > 599 {
				return fmt.Errorf("invalid :status value %q", h.Value)
			}
			if n >= 100 && n < 200 {
				// Interim 1xx responses may repeat across separate HEADERS blocks.
				continue
			}
			if finalStatusSeen || (hasStatus && cand.HTTPStatus >= 200) {
				return fmt.Errorf("duplicate final :status header")
			}
			cand.HTTPStatus = n
			hasStatus = true
			finalStatusSeen = true
			continue
		}

		hValLower := strings.ToLower(h.Value)
		switch hName {
		case "server":
			cand.Server = h.Value
			for _, cdn := range cdnStrong {
				if strings.Contains(hValLower, cdn) {
					cand.CDNStatus = CDNConfirmed
					cand.CDNProvider = cdn
				}
			}
		case "content-type":
			cand.ContentType = h.Value
		case "location":
			cand.Location = h.Value
		case "cf-ray":
			cand.CDNStatus = CDNConfirmed
			cand.CDNProvider = "cloudflare"
		}

		if strings.HasPrefix(hName, "x-amz-cf-") ||
			strings.HasPrefix(hName, "x-sucuri-") ||
			strings.HasPrefix(hName, "x-akamai-") {
			cand.CDNStatus = CDNConfirmed
			if cand.CDNProvider == "" {
				cand.CDNProvider = "headers"
			}
		}

		for _, cdnH := range cdnWeak {
			if hName == cdnH {
				weakCount++
			}
		}
	}

	cand.MissingStatus = !hasStatus
	if cand.CDNStatus == CDNStatusUnknown && weakCount > 0 {
		cand.CDNStatus = CDNLikely
	}
	if cand.HTTPStatus >= 200 {
		cand.ResponseHeadersParsed = true
		cand.MissingStatus = false
	}
	return nil
}

func parseTrailers(cand *Candidate, headers []hpack.HeaderField) error {
	cand.ResponseTrailersSeen = true
	for _, h := range headers {
		if strings.HasPrefix(strings.TrimSpace(h.Name), ":") {
			return fmt.Errorf("pseudo-header %q found in trailers", h.Name)
		}
	}
	return nil
}

type ProbeStage int

const (
	ProbeStageTCP ProbeStage = iota
	ProbeStageTLS
	ProbeStageTLSValidation
	ProbeStageH2
	ProbeStageHeaders
	ProbeStageComplete
)

type H2ErrorCode uint8

const (
	H2ErrUnknown H2ErrorCode = iota
	H2ErrInvalidFrame
	H2ErrInvalidFrameLength
	H2ErrFrameHeaderImplausible
	H2ErrInvalidFrameStreamID
	H2ErrInvalidFramePadding
	H2ErrInvalidFramePreface
	H2ErrBadContinuation
	H2ErrHPACK
	H2ErrSettings
	H2ErrFlowControl
	H2ErrHeaders
	H2ErrTimeout
	H2ErrConnectionReset
	H2ErrBrokenPipe
	H2ErrBadRequest
	H2ErrGoAway
	H2ErrEOF
	H2ErrTLSAlert
	H2ErrRSTStreamLength
)

type ProbeError struct {
	Stage        ProbeStage
	Code         H2ErrorCode
	Err          error
	FrameType    byte
	Flags        byte
	StreamID     uint32
	Length       uint32
	RawHeaderHex string
}

func (c H2ErrorCode) String() string {
	switch c {
	case H2ErrInvalidFrame:
		return "invalid-frame"
	case H2ErrInvalidFrameLength:
		return "frame-size"
	case H2ErrFrameHeaderImplausible:
		return "frame-header-implausible"
	case H2ErrInvalidFrameStreamID:
		return "frame-stream-id"
	case H2ErrInvalidFramePadding:
		return "frame-padding"
	case H2ErrInvalidFramePreface:
		return "frame-preface"
	case H2ErrBadContinuation:
		return "bad-continuation"
	case H2ErrHPACK:
		return "hpack"
	case H2ErrSettings:
		return "settings"
	case H2ErrFlowControl:
		return "flow-control"
	case H2ErrHeaders:
		return "headers"
	case H2ErrTimeout:
		return "timeout"
	case H2ErrConnectionReset:
		return "connection-reset"
	case H2ErrBrokenPipe:
		return "broken-pipe"
	case H2ErrBadRequest:
		return "bad-request"
	case H2ErrGoAway:
		return "goaway"
	case H2ErrEOF:
		return "eof"
	case H2ErrTLSAlert:
		return "tls-alert"
	case H2ErrRSTStreamLength:
		return "rst-stream-length"
	default:
		return "unknown"
	}
}

func normalizeProbeError(pe *ProbeError) *ProbeError {
	if pe == nil || pe.Stage != ProbeStageH2 || pe.Code != H2ErrUnknown {
		return pe
	}
	if errors.Is(pe.Err, io.EOF) {
		pe.Code = H2ErrEOF
	} else if errors.Is(pe.Err, context.DeadlineExceeded) || os.IsTimeout(pe.Err) {
		pe.Code = H2ErrTimeout
	} else if errors.Is(pe.Err, syscall.ECONNRESET) {
		pe.Code = H2ErrConnectionReset
	} else if errors.Is(pe.Err, syscall.EPIPE) {
		pe.Code = H2ErrBrokenPipe
	} else {
		pe.Code = H2ErrUnknown
	}
	return pe
}

func (e *ProbeError) Error() string {
	if e == nil || e.Err == nil {
		return ""
	}
	return e.Err.Error()
}

func h2FrameTypeName(t byte) string {
	switch t {
	case FrameData:
		return "DATA"
	case FrameHeaders:
		return "HEADERS"
	case FrameRSTStream:
		return "RST_STREAM"
	case FrameSettings:
		return "SETTINGS"
	case FrameGoAway:
		return "GOAWAY"
	case FrameWindowUpdate:
		return "WINDOW_UPDATE"
	case FrameContinuation:
		return "CONTINUATION"
	default:
		return fmt.Sprintf("0x%02x", t)
	}
}

func looksLikeHTTP1ResponseHeader(data []byte) bool {
	if len(data) < 4 {
		return false
	}
	return bytes.HasPrefix(data, []byte("HTTP/1.0")) || bytes.HasPrefix(data, []byte("HTTP/1.1"))
}

func ProbeH2(ctx context.Context, ip, sni string, ev Evidence, cfg Config) (cand *Candidate, pErr *ProbeError) {
	if probeLimiter != nil {
		if err := probeLimiter.Wait(ctx); err != nil {
			return nil, &ProbeError{Stage: ProbeStageTCP, Err: err}
		}
	}
	cand = &Candidate{
		IP:            ip,
		SNI:           sni,
		Evidence:      ev,
		DomainQuality: classifyDomainQuality(sni),
		CDNStatus:     CDNStatusUnknown,
		HTTPStatus:    0,
	}

	t0 := time.Now()
	dialer := &net.Dialer{Timeout: time.Duration(cfg.TCPTimeoutMs) * time.Millisecond}
	conn, err := dialer.DialContext(ctx, "tcp", net.JoinHostPort(ip, "443"))
	if err != nil {
		return cand, &ProbeError{Stage: ProbeStageTCP, Err: err}
	}
	defer conn.Close()
	cand.Timings.TCP = time.Since(t0)

	t1 := time.Now()
	uConn := utls.UClient(conn, &utls.Config{
		ServerName:         sni,
		InsecureSkipVerify: true,
		NextProtos:         []string{"h2", "http/1.1"},
		MinVersion:         tls.VersionTLS13,
		MaxVersion:         tls.VersionTLS13,
	}, utls.HelloChrome_Auto)

	uConn.SetDeadline(time.Now().Add(time.Duration(cfg.TLSTimeoutMs) * time.Millisecond))
	if err := uConn.HandshakeContext(ctx); err != nil {
		return cand, &ProbeError{Stage: ProbeStageTLS, Err: err}
	}
	cand.Timings.TLS = time.Since(t1)
	uConn.SetDeadline(time.Time{})

	state := uConn.ConnectionState()

	// utls.ConnectionState does not expose the negotiated TLS key-share/curve.
	// Keep this explicit rather than guessing from the ClientHello.
	cand.TLSCurve = "unavailable (utls)"
	cand.X25519 = false

	if state.Version != tls.VersionTLS13 {
		return cand, &ProbeError{
			Stage: ProbeStageTLS,
			Err:   fmt.Errorf("unexpected TLS version: 0x%x", state.Version),
		}
	}
	cand.TLS13 = true

	if state.NegotiatedProtocol == "h2" {
		cand.ALPN = "h2"
	} else if state.NegotiatedProtocol == "" {
		cand.ALPN = "no ALPN"
	} else {
		cand.ALPN = state.NegotiatedProtocol
	}

	if len(state.PeerCertificates) == 0 {
		return cand, &ProbeError{Stage: ProbeStageTLSValidation, Err: fmt.Errorf("no peer certificates provided")}
	}

	cert := state.PeerCertificates[0]
	cand.CertIssuer = ""
	if len(cert.Issuer.Organization) > 0 {
		cand.CertIssuer = cert.Issuer.Organization[0]
	}
	if cand.CertIssuer == "" {
		cand.CertIssuer = cert.Issuer.CommonName
	}
	now := time.Now()
	cand.CertValidTime = now.After(cert.NotBefore) && now.Before(cert.NotAfter)
	cand.CertExpiry = cert.NotAfter

	opts := x509.VerifyOptions{
		DNSName:       sni,
		Roots:         nil,
		Intermediates: x509.NewCertPool(),
	}
	for _, c := range state.PeerCertificates[1:] {
		opts.Intermediates.AddCert(c)
	}

	if _, err := cert.Verify(opts); err == nil {
		cand.CertSNIMatch = true
		cand.CertChainValid = true
	} else {
		cand.CertChainValid = false
		cand.CertSNIMatch = (cert.VerifyHostname(sni) == nil)
	}

	br := bufio.NewReaderSize(uConn, MaxH2BufferedBytes)
	fr := http2.NewFramer(uConn, br)
	fr.SetMaxReadFrameSize(16384)
	fr.SetReuseFrames()
	fr.ReadMetaHeaders = hpack.NewDecoder(4096, nil)
	fr.MaxHeaderListSize = MaxH2HeaderBlockBytes
	wTo := time.Duration(cfg.H2WriteTimeoutMs) * time.Millisecond
	uConn.SetWriteDeadline(time.Now().Add(wTo))
	if _, err := uConn.Write([]byte("PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n")); err != nil {
		return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
	}
	if err := fr.WriteSettings(); err != nil {
		return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
	}
	if err := fr.WriteHeaders(http2.HeadersFrameParam{StreamID: 1, BlockFragment: buildH2HeadersEncoder(sni), EndHeaders: true, EndStream: true}); err != nil {
		return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
	}
	uConn.SetWriteDeadline(time.Time{})
	requestSent := time.Now()
	uConn.SetReadDeadline(time.Now().Add(time.Duration(cfg.H2ReadTimeoutMs) * time.Millisecond))

	if header, err := br.Peek(9); err == nil {
		length := uint32(header[0])<<16 | uint32(header[1])<<8 | uint32(header[2])
		if length > 16384 {
			frameType, flags := header[3], header[4]
			streamID := binary.BigEndian.Uint32(header[5:9]) & 0x7fffffff
			raw := fmt.Sprintf("%x", header)
			if looksLikeHTTP1ResponseHeader(header) {
				return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrFrameHeaderImplausible, FrameType: frameType, Flags: flags, StreamID: streamID, Length: length, RawHeaderHex: raw, Err: fmt.Errorf("implausible H2 frame header: looks like HTTP/1.x: length=%d stream=%d raw_header=%s", length, streamID, raw)}
			}
			return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrInvalidFrameLength, FrameType: frameType, Flags: flags, StreamID: streamID, Length: length, RawHeaderHex: raw, Err: fmt.Errorf("inbound H2 frame exceeds local limit: type=%s length=%d stream=%d raw_header=%s", h2FrameTypeName(frameType), length, streamID, raw)}
		}
	}

	firstFrameSeen := false
	for {
		if ctx.Err() != nil {
			return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrTimeout, Err: ctx.Err()}
		}
		frame, err := fr.ReadFrame()
		if err != nil {
			if errors.Is(err, http2.ErrFrameTooLarge) {
				return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrInvalidFrameLength, Err: err}
			}
			var netErr net.Error
			if errors.As(err, &netErr) && netErr.Timeout() {
				cand.ReadTimeout = true
				if !cand.H2ProtocolConfirmed {
					return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrTimeout, Err: err}
				}
				break
			}
			if errors.Is(err, io.EOF) {
				return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrEOF, Err: io.EOF}
			}
			if detail := fr.ErrorDetail(); detail != nil {
				return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrSettings, Err: detail}
			}
			return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
		}
		fh := frame.Header()
		if !firstFrameSeen {
			firstFrameSeen = true
			cand.Timings.H2FirstFrame = time.Since(requestSent)
			if fh.Type != http2.FrameSettings || fh.StreamID != 0 {
				return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrInvalidFramePreface, FrameType: byte(fh.Type), Flags: byte(fh.Flags), StreamID: fh.StreamID, Length: fh.Length, Err: fmt.Errorf("invalid first H2 frame: type=%s stream=%d", fh.Type, fh.StreamID)}
			}
		}
		switch f := frame.(type) {
		case *http2.SettingsFrame:
			if f.IsAck() {
				cand.H2SettingsAckReceived = true
				cand.SettingsAckCount++
				break
			}
			if f.HasDuplicates() {
				return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrSettings, Err: fmt.Errorf("duplicate SETTINGS parameters")}
			}
			prof := cand.LatestPeerSettings
			if err := f.ForeachSetting(func(s http2.Setting) error {
				switch s.ID {
				case http2.SettingHeaderTableSize:
					prof.HeaderTableSize = s.Val
					prof.HasHeaderTableSize = true
				case http2.SettingEnablePush:
					if s.Val != 0 {
						return fmt.Errorf("server sent SETTINGS_ENABLE_PUSH=%d", s.Val)
					}
				case http2.SettingMaxConcurrentStreams:
					prof.MaxConcurrentStreams = s.Val
					prof.HasMaxConcurrentStreams = true
				case http2.SettingInitialWindowSize:
					prof.InitialWindowSize = s.Val
					prof.HasInitialWindowSize = true
				case http2.SettingMaxFrameSize:
					prof.MaxFrameSize = s.Val
					prof.HasMaxFrameSize = true
				case http2.SettingMaxHeaderListSize:
					prof.MaxHeaderListSize = s.Val
					prof.HasMaxHeaderListSize = true
				}
				return s.Valid()
			}); err != nil {
				return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrSettings, Err: err}
			}
			if !cand.H2SettingsReceived {
				cand.InitialPeerSettings = prof
				cand.LatestPeerSettings = prof
				cand.H2SettingsReceived = true
				cand.H2ProtocolConfirmed = true
			} else {
				if prof != cand.LatestPeerSettings {
					cand.SettingsChanges++
				}
				cand.LatestPeerSettings = prof
			}
			if err := fr.WriteSettingsAck(); err != nil {
				return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrSettings, Err: err}
			}
			cand.H2SettingsAckSent = true
		case *http2.MetaHeadersFrame:
			if f.Truncated {
				cand.HPACKErrors = true
				return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrHPACK, Err: fmt.Errorf("HTTP/2 header block exceeds configured limit")}
			}
			if f.StreamID != 1 {
				continue
			}
			if !cand.ResponseHeadersParsed {
				was := cand.ResponseHeadersParsed
				if err := parseResponseHeaders(cand, f.Fields); err != nil {
					return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrHeaders, Err: err}
				}
				if cand.ResponseHeadersParsed && !was {
					cand.H2HeadersReceived = true
					cand.Timings.H2Headers = time.Since(requestSent)
				}
			} else if err := parseTrailers(cand, f.Fields); err != nil {
				return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrHeaders, Err: err}
			}
			if cand.H2HeadersReceived {
				break
			}
		case *http2.DataFrame:
			if f.StreamID != 1 {
				continue
			}
			cand.H2DataFrames++
			cand.BodyBytes += len(f.Data())
			if f.StreamEnded() {
				cand.EndStreamSeen = true
			}
			if n := len(f.Data()); n > 0 {
				if err := fr.WriteWindowUpdate(1, uint32(n)); err != nil {
					return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrFlowControl, Err: err}
				}
				if err := fr.WriteWindowUpdate(0, uint32(n)); err != nil {
					return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrFlowControl, Err: err}
				}
			}
		case *http2.RSTStreamFrame:
			if f.StreamID == 1 {
				cand.StreamReset = true
				return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrRSTStreamLength, Err: fmt.Errorf("RST_STREAM on request stream")}
			}
		case *http2.GoAwayFrame:
			cand.GoAwaySeen = true
			return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrGoAway, Err: fmt.Errorf("peer sent GOAWAY")}
		}
		if cand.H2ProtocolConfirmed && cand.H2HeadersReceived {
			break
		}
	}

	if !cand.H2SettingsReceived || !cand.H2ProtocolConfirmed {
		return cand, &ProbeError{Stage: ProbeStageH2, Code: H2ErrSettings, Err: fmt.Errorf("no valid H2 SETTINGS exchange received")}
	}

	cand.RealityFeasible = cand.TLS13 && cand.ALPN == "h2" && cand.CertSNIMatch && cand.CertChainValid && cand.CertValidTime

	return cand, nil
}

func fetchShodanInternetDB(ctx context.Context, ip string, timeout time.Duration) ([]string, error) {
	if err := shodanOSINTRate.Wait(ctx); err != nil {
		return nil, err
	}
	select {
	case shodanOSINTSem <- struct{}{}:
		defer func() { <-shodanOSINTSem }()
	case <-ctx.Done():
		return nil, ctx.Err()
	}
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, "https://internetdb.shodan.io/"+url.QueryEscape(ip), nil)
	if err != nil {
		return nil, err
	}
	req.Header.Set("User-Agent", "reality-scanner/1.0")
	resp, err := ipOSINTHTTPClient.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode == http.StatusNotFound {
		return nil, nil
	}
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("Shodan InternetDB HTTP %d", resp.StatusCode)
	}
	var payload struct {
		Hostnames []string `json:"hostnames"`
	}
	if err := json.NewDecoder(io.LimitReader(resp.Body, 1<<20)).Decode(&payload); err != nil {
		return nil, err
	}
	out := make([]string, 0, len(payload.Hostnames))
	for _, h := range payload.Hostnames {
		if d := CleanDomain(h); d != "" {
			out = append(out, d)
		}
	}
	return uniqueStrings(out), nil
}

func fetchVirusTotalIPResolutions(ctx context.Context, ip, key string, timeout time.Duration) ([]string, error) {
	if strings.TrimSpace(key) == "" {
		return nil, nil
	}
	if err := vtOSINTRate.Wait(ctx); err != nil {
		return nil, err
	}
	select {
	case vtOSINTSem <- struct{}{}:
		defer func() { <-vtOSINTSem }()
	case <-ctx.Done():
		return nil, ctx.Err()
	}
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()

	var out []string
	cursor := ""
	for page := 0; page < 3; page++ {
		u := fmt.Sprintf("https://www.virustotal.com/api/v3/ip_addresses/%s/resolutions?limit=40", url.QueryEscape(ip))
		if cursor != "" {
			u += "&cursor=" + url.QueryEscape(cursor)
		}
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
		if err != nil {
			return out, err
		}
		req.Header.Set("User-Agent", "reality-scanner/1.0")
		req.Header.Set("Accept", "application/json")
		req.Header.Set("x-apikey", key)
		resp, err := ipOSINTHTTPClient.Do(req)
		if err != nil {
			return out, err
		}
		if resp.StatusCode != http.StatusOK {
			body, _ := io.ReadAll(io.LimitReader(resp.Body, 4096))
			resp.Body.Close()
			return out, fmt.Errorf("VirusTotal HTTP %d: %s", resp.StatusCode, strings.TrimSpace(string(body)))
		}
		var payload struct {
			Data []struct {
				Attributes struct {
					HostName string `json:"host_name"`
				} `json:"attributes"`
			} `json:"data"`
			Meta struct {
				Cursor string `json:"cursor"`
			} `json:"meta"`
		}
		err = json.NewDecoder(io.LimitReader(resp.Body, 1<<20)).Decode(&payload)
		resp.Body.Close()
		if err != nil {
			return out, err
		}
		for _, item := range payload.Data {
			if d := CleanDomain(item.Attributes.HostName); d != "" {
				out = append(out, d)
			}
		}
		if payload.Meta.Cursor == "" || payload.Meta.Cursor == cursor {
			break
		}
		cursor = payload.Meta.Cursor
	}
	return uniqueStrings(out), nil
}

func getIPOSINTDomains(ctx context.Context, ip, vtKey string, timeout time.Duration, pipeStats *PipelineStats) (map[string]DomainSource, []string) {
	type result struct {
		provider DomainSource
		domains  []string
		err      error
	}
	ch := make(chan result, 2)
	go func() {
		pipeStats.mu.Lock()
		pipeStats.IPOSINTShodanAttempts++
		pipeStats.mu.Unlock()
		d, err := fetchShodanInternetDB(ctx, ip, timeout)
		pipeStats.mu.Lock()
		if err == nil {
			pipeStats.IPOSINTShodanSuccess++
			pipeStats.IPOSINTShodanNames += len(d)
		}
		pipeStats.mu.Unlock()
		ch <- result{provider: SourceShodan, domains: d, err: err}
	}()
	go func() {
		if strings.TrimSpace(vtKey) == "" {
			ch <- result{provider: SourceVirusTotalIP}
			return
		}
		pipeStats.mu.Lock()
		pipeStats.IPOSINTVTAttempts++
		pipeStats.mu.Unlock()
		d, err := fetchVirusTotalIPResolutions(ctx, ip, vtKey, timeout)
		pipeStats.mu.Lock()
		if err == nil {
			pipeStats.IPOSINTVTSuccess++
			pipeStats.IPOSINTVTNames += len(d)
		}
		pipeStats.mu.Unlock()
		ch <- result{provider: SourceVirusTotalIP, domains: d, err: err}
	}()

	sources := make(map[string]DomainSource)
	for i := 0; i < 2; i++ {
		r := <-ch
		for _, d := range r.domains {
			sources[d] |= r.provider
		}
	}

	ordered := make([]string, 0, len(sources))
	for d := range sources {
		ordered = append(ordered, d)
	}
	sort.Slice(ordered, func(i, j int) bool {
		sourceWeight := func(src DomainSource) int {
			w := 0
			if src.Has(SourceShodan) {
				w += 3
			}
			if src.Has(SourceVirusTotalIP) {
				w += 4
			}
			return w
		}
		qualityPenalty := func(d string) int {
			switch classifyDomainQuality(d) {
			case "Numeric":
				return 30
			case "DynDNS":
				return 20
			case "JunkTLD":
				return 5
			default:
				return 0
			}
		}
		wi := sourceWeight(sources[ordered[i]]) - qualityPenalty(ordered[i])
		wj := sourceWeight(sources[ordered[j]]) - qualityPenalty(ordered[j])
		if wi != wj {
			return wi > wj
		}
		return ordered[i] < ordered[j]
	})
	return sources, ordered
}

func fetchChaosDomain(ctx context.Context, root, key string, timeout time.Duration) ([]string, error) {
	if strings.TrimSpace(key) == "" {
		return nil, nil
	}
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, fmt.Sprintf("https://dns.projectdiscovery.io/dns/%s/subdomains", url.QueryEscape(root)), nil)
	if err != nil {
		return nil, err
	}
	setBrowserHeaders(req)
	req.Header.Set("Authorization", key)
	resp, err := ipOSINTHTTPClient.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(io.LimitReader(resp.Body, 4096))
		return nil, fmt.Errorf("Chaos HTTP %d: %s", resp.StatusCode, strings.TrimSpace(string(body)))
	}
	var payload struct {
		Subdomains []string `json:"subdomains"`
	}
	if err := json.NewDecoder(io.LimitReader(resp.Body, 4<<20)).Decode(&payload); err != nil {
		return nil, err
	}
	out := make([]string, 0, len(payload.Subdomains))
	for _, sub := range payload.Subdomains {
		sub = strings.TrimSpace(strings.TrimSuffix(sub, "."))
		if sub == "" {
			continue
		}
		full := sub
		if !strings.Contains(sub, ".") || !strings.HasSuffix(sub, "."+root) {
			full = sub + "." + root
		}
		if d := CleanDomain(full); d != "" {
			out = append(out, d)
		}
	}
	return uniqueStrings(out), nil
}

func enrichWithChaosDomain(ctx context.Context, allPairs []TargetPair, key string, pipeStats *PipelineStats) []TargetPair {
	if strings.TrimSpace(key) == "" || len(allPairs) == 0 {
		return allPairs
	}
	rootScore := make(map[string]int)
	rootSources := make(map[string]DomainSource)
	for _, p := range allPairs {
		root, err := publicsuffix.EffectiveTLDPlusOne(p.SNI)
		if err != nil || root == "" {
			continue
		}
		rootSources[root] |= p.Evidence.Combined()
		rootScore[root]++
	}
	roots := make([]string, 0, len(rootScore))
	for root := range rootScore {
		roots = append(roots, root)
	}
	sort.Slice(roots, func(i, j int) bool {
		sourceWeight := func(src DomainSource) int {
			w := rankRootSources(src)
			return w
		}
		wi := rootScore[roots[i]]*2 + sourceWeight(rootSources[roots[i]])
		wj := rootScore[roots[j]]*2 + sourceWeight(rootSources[roots[j]])
		if wi != wj {
			return wi > wj
		}
		return roots[i] < roots[j]
	})
	if len(roots) > 100 {
		roots = roots[:100]
	}
	pipeStats.mu.Lock()
	pipeStats.ChaosRootsQueried = len(roots)
	pipeStats.mu.Unlock()
	type res struct {
		root  string
		names []string
		err   error
	}
	jobs := make(chan string, len(roots))
	out := make(chan res, len(roots))
	workers := minInt(2, len(roots))
	var wg sync.WaitGroup
	for i := 0; i < workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for root := range jobs {
				pipeStats.mu.Lock()
				pipeStats.ChaosAttempts++
				pipeStats.mu.Unlock()
				names, err := fetchChaosDomain(ctx, root, key, 8*time.Second)
				if err == nil {
					pipeStats.mu.Lock()
					pipeStats.ChaosSuccess++
					pipeStats.ChaosNames += len(names)
					pipeStats.mu.Unlock()
				}
				out <- res{root: root, names: names, err: err}
			}
		}()
	}
	for _, root := range roots {
		jobs <- root
	}
	close(jobs)
	wg.Wait()
	close(out)

	seenSNI := make(map[string]struct{}, len(allPairs)+ChaosMaxNames)
	for _, p := range allPairs {
		if p.SNI != "" {
			seenSNI[p.SNI] = struct{}{}
		}
	}
	added := 0
	chaosPairs := make([]TargetPair, 0, ChaosMaxNames)
	for r := range out {
		if r.err != nil {
			continue
		}
		for _, d := range r.names {
			if added >= ChaosMaxNames {
				break
			}
			if _, ok := seenSNI[d]; ok {
				continue
			}
			seenSNI[d] = struct{}{}
			chaosPairs = append(chaosPairs, TargetPair{SNI: d, Evidence: Evidence{Direct: SourceChaos}})
			added++
		}
		if added >= ChaosMaxNames {
			break
		}
	}
	return append(allPairs, chaosPairs...)
}

func extractDomainsFromTLS(ctx context.Context, ip, sni string, timeout time.Duration) ([]string, error) {
	if probeLimiter != nil {
		if err := probeLimiter.Wait(ctx); err != nil {
			return nil, err
		}
	}
	dialer := &net.Dialer{Timeout: timeout}
	conn, err := dialer.DialContext(ctx, "tcp", net.JoinHostPort(ip, "443"))
	if err != nil {
		return nil, err
	}
	defer conn.Close()

	uConn := utls.UClient(conn, &utls.Config{
		ServerName:         sni,
		InsecureSkipVerify: true,
	}, utls.HelloChrome_Auto)
	uConn.SetDeadline(time.Now().Add(timeout))
	if err := uConn.HandshakeContext(ctx); err != nil {
		return nil, err
	}
	state := uConn.ConnectionState()
	if len(state.PeerCertificates) == 0 {
		return nil, fmt.Errorf("no peer certificates provided")
	}
	cert := state.PeerCertificates[0]
	doms := make([]string, 0, len(cert.DNSNames)+1)
	for _, d := range cert.DNSNames {
		if cd := CleanDomain(d); cd != "" {
			doms = append(doms, cd)
		}
	}
	if cd := CleanDomain(cert.Subject.CommonName); cd != "" {
		doms = append(doms, cd)
	}
	return uniqueStrings(doms), nil
}

func activeProbeIP(ctx context.Context, ip string, timeout time.Duration, pipeStats *PipelineStats, rtCaches *RuntimeCaches, cfg Config, allowIPOSINT bool) []TargetPair {
	sourceMap := make(map[string]DomainSource)
	addDomain := func(d string, src DomainSource) {
		d = CleanDomain(d)
		if d == "" {
			return
		}
		sourceMap[d] |= src
	}

	// 1. Direct TLS on the IP itself: the certificate is the primary active SNI source.
	if doms, err := extractDomainsFromTLS(ctx, ip, ip, timeout); err == nil {
		if len(doms) > 0 {
			for _, d := range doms {
				addDomain(d, SourceDirectTLS)
			}
		}
	}

	// 2. Resilient PTR: system resolver → raw resolver pool → DoH inside resolvePTRRaw.
	names, err := resolvePTRRaw(ctx, ip, cfg.DNSResolvers, PTRQueryTimeoutDefault, rtCaches)
	if err == nil && len(names) > 0 {
		pipeStats.mu.Lock()
		pipeStats.PTRFound++
		pipeStats.mu.Unlock()
		for _, name := range names {
			ptrDomain := CleanDomain(strings.TrimSuffix(strings.TrimSpace(name), "."))
			if ptrDomain == "" {
				continue
			}
			addDomain(ptrDomain, SourcePTR)
			cDoms, tlsErr := extractDomainsFromTLS(ctx, ip, ptrDomain, timeout)
			if tlsErr == nil {
				for _, cd := range cDoms {
					addDomain(cd, SourceDirectTLS)
				}
			}
		}
	}

	// 3. Bounded IP OSINT enrichment. Only a limited subset of sampled IPs uses
	// external OSINT, and the two historically useful sources are queried in parallel.
	if allowIPOSINT && len(sourceMap) < 5 {
		srcByDomain, domains := getIPOSINTDomains(ctx, ip, cfg.VTKey, 6*time.Second, pipeStats)
		if len(domains) > 20 {
			domains = domains[:20]
		}
		pipeStats.mu.Lock()
		pipeStats.IPOSINTSelectedNames += len(domains)
		pipeStats.mu.Unlock()
		for _, d := range domains {
			src := srcByDomain[d]
			addDomain(d, src)
			cDoms, tlsErr := extractDomainsFromTLS(ctx, ip, d, timeout)
			if tlsErr == nil && len(cDoms) > 0 {
				for _, cd := range cDoms {
					addDomain(cd, SourceDirectTLS)
				}
			}
		}
	}

	pairs := make([]TargetPair, 0, len(sourceMap))
	for d, src := range sourceMap {
		pairs = append(pairs, TargetPair{IP: ip, SNI: d, Evidence: Evidence{Direct: src}})
	}
	sort.Slice(pairs, func(i, j int) bool {
		weight := func(src DomainSource) int {
			w := 0
			if src.Has(SourceDirectTLS) {
				w += 3
			}
			if src.Has(SourcePTR) {
				w += 2
			}
			if src.Has(SourceSeed) {
				w++
			}
			return w
		}
		wi, wj := weight(pairs[i].Evidence.Direct), weight(pairs[j].Evidence.Direct)
		if wi != wj {
			return wi > wj
		}
		return pairs[i].SNI < pairs[j].SNI
	})
	if len(pairs) > MaxSNIPairsPerIP {
		pairs = pairs[:MaxSNIPairsPerIP]
	}
	return pairs
}

// ================= SCORING & ENRICHMENT =================

func scoreH2Profile(c *Candidate) float64 {
	score := 0.0
	if c.H2SettingsReceived {
		score += 5.0
	}
	prof := c.InitialPeerSettings
	if prof.HasMaxConcurrentStreams && prof.MaxConcurrentStreams > 0 && prof.MaxConcurrentStreams <= 1000 {
		score += 3.0
	}
	if prof.HasInitialWindowSize {
		switch {
		case prof.InitialWindowSize == 65535:
			score += 1.0
		case prof.InitialWindowSize > 65535:
			score += 3.0
		}
	}
	if prof.HasMaxFrameSize {
		switch {
		case prof.MaxFrameSize == 16384:
			score += 1.0
		case prof.MaxFrameSize > 16384:
			score += 3.0
		}
	}
	if c.H2DataFrames > 0 {
		score += 3.0
	}
	if c.BodyBytes >= 1024 {
		score += 1.0
	}
	if c.EndStreamSeen {
		score += 2.0
	}
	return math.Min(score, 20.0)
}

func validateAndEnrich(cand *Candidate, pipeStats *PipelineStats) bool {
	if cand == nil || !cand.H2ProtocolConfirmed || !cand.CertChainValid || !cand.CertSNIMatch || !cand.CertValidTime || !cand.TLS13 || cand.ALPN != "h2" {
		return false
	}

	rs := RealityScore{
		TLSQuality:  20.0,
		Certificate: 20.0,
		H2Profile:   scoreH2Profile(cand),
	}

	if cand.Server != "" && cand.Server != "-" {
		srvLower := strings.ToLower(cand.Server)
		if strings.Contains(srvLower, "nginx") || strings.Contains(srvLower, "caddy") || strings.Contains(srvLower, "apache") || strings.Contains(srvLower, "openresty") {
			rs.ServerProfile = 10
		} else {
			rs.ServerProfile = 6
		}
	} else {
		rs.ServerProfile = 3
	}

	switch cand.HTTPStatus {
	case 200:
		rs.HTTPBehavior = 10
	case 301, 302, 307, 308:
		rs.HTTPBehavior = 7
	default:
		if cand.HTTPStatus >= 400 && cand.HTTPStatus < 500 {
			rs.HTTPBehavior = 5
		} else if cand.HTTPStatus >= 500 {
			rs.HTTPBehavior = -5
		}
	}

	discovery := 0.0
	scoreDirect := func(src DomainSource, pts float64) {
		if cand.Evidence.Direct.Has(src) {
			discovery += pts
		} else if cand.Evidence.Inherited.Has(src) {
			discovery += pts / 2.0
		}
	}
	scoreDirect(SourcePTR, 3.0)
	scoreDirect(SourceDirectTLS, 4.0)
	scoreDirect(SourceShodan, 3.0)
	scoreDirect(SourceVirusTotalIP, 4.0)
	scoreDirect(SourceChaos, 4.0)
	scoreDirect(SourceSeed, 1.0)

	combinedSources := cand.Evidence.Combined()
	diversity := 0
	if combinedSources.Has(SourcePTR) {
		diversity++
	}
	if combinedSources.Has(SourceDirectTLS) {
		diversity++
	}
	if combinedSources.Has(SourceSeed) {
		diversity++
	}
	if combinedSources.Has(SourceShodan) {
		diversity++
	}
	if combinedSources.Has(SourceVirusTotalIP) {
		diversity++
	}
	if combinedSources.Has(SourceChaos) {
		diversity++
	}
	if diversity >= 2 {
		discovery += 2.0
	}
	if diversity >= 3 {
		discovery += 2.0
	}
	rs.DiscoveryScore = math.Min(discovery, 10.0)

	rtt := cand.Timings.TotalProbeLatency().Milliseconds()
	switch {
	case rtt <= 50:
		rs.Latency = 10
	case rtt <= 150:
		rs.Latency = 7
	case rtt <= 300:
		rs.Latency = 4
	default:
		rs.Latency = 1
	}

	rs.Total = rs.TLSQuality + rs.Certificate + rs.H2Profile + rs.ServerProfile + rs.HTTPBehavior + rs.DiscoveryScore + rs.Latency
	scorePenalty := 0.0
	switch cand.DomainQuality {
	case "Numeric":
		scorePenalty = 30.0
	case "DynDNS":
		scorePenalty = 20.0
	case "JunkTLD":
		scorePenalty = 5.0
	}
	if cand.CDNStatus == CDNLikely {
		scorePenalty += 10.0
	}

	cand.RealityFeasible = true
	cand.RealityScore = rs
	cand.DomainPenalty = scorePenalty
	cand.Score = rs.Total - scorePenalty
	if cand.Score < 0 && pipeStats != nil {
		pipeStats.mu.Lock()
		pipeStats.LowScoreCandidates++
		pipeStats.mu.Unlock()
	}
	return true
}

// ================= ACTIVE PIPELINE =================

func activePTRStats(rtCaches *RuntimeCaches, s *PipelineStats) {
	rtCaches.DNSStatsMu.Lock()
	s.PTRSystemFallbacks = rtCaches.PTRSystemFallbacks
	s.PTRDoHFallbacks = rtCaches.PTRDoHFallbacks
	s.PTRNegativeResponses = rtCaches.PTRNegativeResponses
	rtCaches.DNSStatsMu.Unlock()
}

func RunPipeline(ctx context.Context, cfg Config, sampledIPs []string, scanRanges []ipRange) []Candidate {
	pipeStats := NewPipelineStats()
	pipeStats.IPSampled = len(sampledIPs)
	rtCaches := NewRuntimeCaches()
	warmDNSResolvers(ctx, cfg.DNSResolvers, cfg.ECSIP, cfg.ECSPrefix, rtCaches)

	var allPairs []TargetPair
	var validPairs []TargetPair
	resumeStage := ""
	if cfg.Resume && cfg.Checkpoint != "" {
		if cp, err := loadCheckpoint(cfg.Checkpoint); err == nil && checkpointMatches(cp, cfg, sampledIPs) {
			switch cp.Stage {
			case "E":
				if len(cp.Final) > 0 {
					return cp.Final
				}
			case "D":
				allPairs = append(allPairs, cp.StageA...)
				validPairs = append(validPairs, cp.StageD...)
				resumeStage = "D"
			case "A":
				allPairs = append(allPairs, cp.StageA...)
				resumeStage = "A"
			}
		}
	}

	if resumeStage == "" {
		progressf("[*] STAGE A: Active certificate/SNI discovery (Direct TLS + resilient PTR + IP OSINT + Chaos Domain)...\n")
		allPairs = make([]TargetPair, 0, len(sampledIPs))
		ipOSINTLimit := cfg.IPOSINTLimit
		if ipOSINTLimit <= 0 || ipOSINTLimit > len(sampledIPs) {
			ipOSINTLimit = len(sampledIPs)
		}
		ipOSINTAllowed := make(map[string]struct{}, ipOSINTLimit)
		osintIPs := append([]string(nil), sampledIPs...)
		osintRand := rand.New(rand.NewSource(cfg.Seed ^ int64(0x49504f53494e54)))
		osintRand.Shuffle(len(osintIPs), func(i, j int) { osintIPs[i], osintIPs[j] = osintIPs[j], osintIPs[i] })
		for _, ip := range osintIPs[:ipOSINTLimit] {
			ipOSINTAllowed[ip] = struct{}{}
		}
		pipeStats.mu.Lock()
		pipeStats.IPOSINTIPsSelected = len(ipOSINTAllowed)
		pipeStats.mu.Unlock()
		for _, pairs := range discovery.Map(ctx, sampledIPs, minInt(cfg.Workers, len(sampledIPs)), func(jobCtx context.Context, ip string) []TargetPair {
			_, allow := ipOSINTAllowed[ip]
			return activeProbeIP(jobCtx, ip, time.Duration(cfg.TLSTimeoutMs)*time.Millisecond, pipeStats, rtCaches, cfg, allow)
		}) {
			allPairs = append(allPairs, pairs...)
		}
	} else {
		progressf("[*] STAGE A: restored from checkpoint (%d IP+SNI pairs)\n", len(allPairs))
	}
	uniqueDomains := make(map[string]struct{}, len(allPairs))
	for _, pair := range allPairs {
		if pair.SNI != "" {
			uniqueDomains[pair.SNI] = struct{}{}
		}
	}
	progressf("[+] Stage A Direct/PTR/IP-OSINT завершён. Уникальных SNI: %d | Пар IP+SNI: %d\n", len(uniqueDomains), len(allPairs))
	if strings.TrimSpace(cfg.ChaosKey) != "" {
		allPairs = enrichWithChaosDomain(ctx, allPairs, cfg.ChaosKey, pipeStats)
		progressf("[+] Chaos Domain enrichment: roots=%d | attempts=%d | success=%d | names=%d\n", pipeStats.ChaosRootsQueried, pipeStats.ChaosAttempts, pipeStats.ChaosSuccess, pipeStats.ChaosNames)
	}
	if cfg.Checkpoint != "" && resumeStage == "" {
		_ = saveCheckpoint(cfg.Checkpoint, checkpointData{Version: "v92", Stage: "A", TargetIP: cfg.TargetIP, TargetASN: cfg.TargetASN, TargetCountry: cfg.TargetCountry, SampledIPs: sampledIPs, StageA: allPairs})
	}
	if len(allPairs) == 0 {
		activePTRStats(rtCaches, pipeStats)
		return nil
	}

	progressf("[*] STAGE D: DNS Validation with ECS (%d IP+SNI pairs)...\n", len(allPairs))
	if resumeStage == "D" {
		progressf("[+] Stage D restored from checkpoint: %d valid pairs\n", len(validPairs))
	} else {
		validPairs = make([]TargetPair, 0, minInt(len(allPairs), LimitValidPairs))
		var validMu sync.Mutex
		var pairSeen sync.Map
		var uniqueResolvedIPs sync.Map
		var uniqueTargetIPs sync.Map

		jobsD := make(chan TargetPair, minInt(len(allPairs), 1024))
		var wg sync.WaitGroup
		workerCountD := scanning.WorkerCount(cfg.DNSWorkers, len(allPairs))
		for i := 0; i < workerCountD; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				for p := range jobsD {
					if ctx.Err() != nil {
						return
					}
					pipeStats.mu.Lock()
					pipeStats.DNSQueries++
					pipeStats.mu.Unlock()
					ips, err := resolveIPv4Cached(ctx, p.SNI, rtCaches, cfg)

					pipeStats.mu.Lock()
					if err != nil {
						if errors.Is(err, ErrDNSNXDomain) {
							pipeStats.DNSSuccess++
							pipeStats.DNSNXDomain++
						} else {
							recordDNSPipelineErrorLocked(pipeStats, err)
						}
						pipeStats.mu.Unlock()
						continue
					}
					pipeStats.DNSSuccess++
					if len(ips) == 0 {
						pipeStats.DNSNoIPv4++
						pipeStats.mu.Unlock()
						continue
					}
					pipeStats.DNSResolvedIPs += len(ips)
					pipeStats.mu.Unlock()

					matched := false
					for _, resolvedIP := range ips {
						uniqueResolvedIPs.Store(resolvedIP, struct{}{})
						if resolvedIP != p.IP && !ipInRanges(resolvedIP, scanRanges) {
							pipeStats.mu.Lock()
							pipeStats.ASNFiltered++
							pipeStats.mu.Unlock()
							continue
						}
						matched = true
						uniqueTargetIPs.Store(resolvedIP, struct{}{})
						pipeStats.mu.Lock()
						pipeStats.DNSTargetRangeMatches++
						pipeStats.mu.Unlock()
						key := resolvedIP + "\x00" + p.SNI
						if _, loaded := pairSeen.LoadOrStore(key, true); loaded {
							continue
						}
						validMu.Lock()
						if len(validPairs) < LimitValidPairs {
							validPairs = append(validPairs, TargetPair{IP: resolvedIP, SNI: p.SNI, Evidence: p.Evidence})
						} else {
							pipeStats.PairLimitDrops++
						}
						validMu.Unlock()
					}
					if matched {
						pipeStats.mu.Lock()
						pipeStats.DNSTargetDomains++
						pipeStats.mu.Unlock()
					}
				}
			}()
		}
		for _, p := range allPairs {
			jobsD <- p
		}
		close(jobsD)
		wg.Wait()
		if ctx.Err() != nil {
			progressln("[-] Выполнение прервано (Stage D).")
			return nil
		}

		uniqueResolvedCount := 0
		uniqueResolvedIPs.Range(func(k, v interface{}) bool { uniqueResolvedCount++; return true })
		uniqueTargetCount := 0
		uniqueTargetIPs.Range(func(k, v interface{}) bool { uniqueTargetCount++; return true })
		pipeStats.mu.Lock()
		pipeStats.DNSUniqueResolvedIPs = uniqueResolvedCount
		pipeStats.DNSUniqueTargetIPs = uniqueTargetCount
		pipeStats.DNSValidPairs = len(validPairs)
		finalDNS := pipeStats.DNSValidPairs
		finalASN := pipeStats.ASNFiltered
		pipeStats.mu.Unlock()
		progressf("[+] Stage D завершён. Подтверждено DNS-пар: %d | ASN filtered: %d\n", finalDNS, finalASN)
		if len(validPairs) == 0 {
			return nil
		}

	}
	if cfg.Checkpoint != "" && resumeStage != "D" {
		_ = saveCheckpoint(cfg.Checkpoint, checkpointData{Version: "v92", Stage: "D", TargetIP: cfg.TargetIP, TargetASN: cfg.TargetASN, TargetCountry: cfg.TargetCountry, SampledIPs: sampledIPs, StageA: allPairs, StageD: validPairs})
	}
	progressf("[*] STAGE E: Active HTTP/2 + TLS validation (%d targets)...\n", len(validPairs))
	var candidates []Candidate
	workerCountE := scanning.WorkerCount(cfg.Workers, len(validPairs))
	h2Jobs := make(chan TargetPair, len(validPairs))
	resultsE := make(chan Candidate, len(validPairs))
	var wgE sync.WaitGroup
	if cfg.TCPTimeoutMs < 3000 {
		cfg.TCPTimeoutMs = 3000
	}
	if cfg.TLSTimeoutMs < 3000 {
		cfg.TLSTimeoutMs = 3000
	}

	for i := 0; i < workerCountE; i++ {
		wgE.Add(1)
		go func() {
			defer wgE.Done()
			for p := range h2Jobs {
				if ctx.Err() != nil {
					return
				}
				cand, pErr := ProbeH2(ctx, p.IP, p.SNI, p.Evidence, cfg)
				pErr = normalizeProbeError(pErr)
				pipeStats.mu.Lock()
				if pErr != nil && pErr.Stage == ProbeStageTCP {
					errStr := pErr.Err.Error()
					if os.IsTimeout(pErr.Err) || strings.Contains(strings.ToLower(errStr), "i/o timeout") || strings.Contains(strings.ToLower(errStr), "deadline") {
						pipeStats.TCPTimeouts++
					} else if strings.Contains(strings.ToLower(errStr), "refused") {
						pipeStats.TCPRefused++
					} else {
						pipeStats.TCPOtherErrs++
					}
					pipeStats.mu.Unlock()
					continue
				}
				pipeStats.TCPConnected++
				if pErr != nil && (pErr.Stage == ProbeStageTLS || pErr.Stage == ProbeStageTLSValidation) {
					errStr := pErr.Err.Error()
					low := strings.ToLower(errStr)
					switch {
					case os.IsTimeout(pErr.Err) || strings.Contains(low, "deadline") || strings.Contains(low, "i/o timeout"):
						pipeStats.TLSTimeouts++
					case strings.Contains(low, "no peer certificates"):
						pipeStats.NoPeerCertificates++
					case strings.Contains(low, "handshake failure"):
						pipeStats.TLSHandshakeFailure++
					case strings.Contains(low, "unrecognized name"):
						pipeStats.TLSUnrecognizedName++
					case strings.Contains(low, "connection reset"):
						pipeStats.TLSConnectionReset++
					case errors.Is(pErr.Err, io.EOF) || strings.Contains(low, "eof"):
						pipeStats.TLSEOF++
					case pErr.Stage == ProbeStageTLSValidation:
						pipeStats.TLSValidationFailures++
					default:
						pipeStats.TLSOtherErrs++
					}
					pipeStats.mu.Unlock()
					continue
				}
				pipeStats.TLSHandshake++
				if cand != nil && cand.ALPN != "h2" {
					pipeStats.H2NoALPN++
				}
				if pErr != nil {
					pipeStats.mu.Unlock()
					switch pErr.Code {
					case H2ErrTimeout:
						pipeStats.H2TimeoutNoFrames++
					case H2ErrConnectionReset:
						pipeStats.H2ConnectionReset++
					case H2ErrBrokenPipe:
						pipeStats.H2BrokenPipe++
					case H2ErrBadRequest:
						pipeStats.H2BadRequest++
					case H2ErrGoAway:
						pipeStats.H2GoAway++
					case H2ErrEOF:
						pipeStats.H2EOF++
					case H2ErrTLSAlert:
						pipeStats.H2TLSAlerts++
					case H2ErrBadContinuation:
						pipeStats.H2BadContinuation++
					case H2ErrRSTStreamLength:
						pipeStats.H2InvalidFrame++
						pipeStats.H2InvalidFrameRSTLength++
					case H2ErrInvalidFrameLength:
						pipeStats.H2InvalidFrame++
						pipeStats.H2InvalidFrameLength++
					case H2ErrFrameHeaderImplausible:
						pipeStats.H2InvalidFrame++
						pipeStats.H2FrameHeaderImplausible++
					case H2ErrInvalidFrameStreamID:
						pipeStats.H2InvalidFrame++
						pipeStats.H2InvalidFrameStreamID++
					case H2ErrInvalidFramePadding:
						pipeStats.H2InvalidFrame++
						pipeStats.H2InvalidFramePadding++
					case H2ErrInvalidFramePreface:
						pipeStats.H2InvalidFrame++
						pipeStats.H2InvalidFramePreface++
					case H2ErrHPACK:
						pipeStats.H2HPACKDecode++
					default:
						pipeStats.H2OtherErrs++
					}
					continue
				}
				if cand == nil || !cand.H2ProtocolConfirmed {
					pipeStats.mu.Unlock()
					pipeStats.incH2Reason("missing-settings")
					continue
				}
				pipeStats.H2ProtocolOK++
				if !cand.H2HeadersReceived {
					if cand.ReadTimeout {
						pipeStats.H2Timeouts++
					} else if cand.HPACKErrors {
						pipeStats.H2HPACKErrors++
					} else {
						pipeStats.H2HeadersWithoutStatus++
					}
					pipeStats.mu.Unlock()
					continue
				}
				pipeStats.H2HeadersOK++
				if cand.MissingStatus || cand.HTTPStatus <= 0 {
					pipeStats.H2InvalidStatus++
					pipeStats.mu.Unlock()
					continue
				}
				pipeStats.H2StatusOK++
				if !cand.CertChainValid || !cand.CertSNIMatch || !cand.CertValidTime {
					pipeStats.TLSValidationFailures++
					pipeStats.mu.Unlock()
					continue
				}
				if cand.EndStreamSeen {
					pipeStats.EndStreamOK++
				}
				pipeStats.mu.Unlock()

				if !validateAndEnrich(cand, pipeStats) {
					pipeStats.mu.Lock()
					pipeStats.ScoreRejected++
					pipeStats.mu.Unlock()
					continue
				}
				if !cand.RealityFeasible {
					continue
				}
				pipeStats.mu.Lock()
				pipeStats.CandidatesAccepted++
				pipeStats.RealityFeasibleCandidates++
				pipeStats.mu.Unlock()
				select {
				case resultsE <- *cand:
				case <-ctx.Done():
					return
				}
			}
		}()
	}
	for _, p := range validPairs {
		h2Jobs <- p
	}
	close(h2Jobs)
	wgE.Wait()
	close(resultsE)
	for cand := range resultsE {
		candidates = append(candidates, cand)
	}
	if ctx.Err() != nil {
		progressln("[-] Выполнение прервано (Stage E).")
		return nil
	}

	clusters := make(map[string][]Candidate)
	for _, c := range candidates {
		clusters[c.IP] = append(clusters[c.IP], c)
	}
	candidateLess := func(a, b Candidate) bool {
		// Final selection is quality-first: Reality feasibility, then the full
		// weighted score. RTT is deliberately only a late tie-breaker so a
		// slightly slower but materially better SNI is not discarded.
		if a.RealityFeasible != b.RealityFeasible {
			return a.RealityFeasible
		}
		if a.Score != b.Score {
			return a.Score > b.Score
		}
		if a.CertSNIMatch != b.CertSNIMatch {
			return a.CertSNIMatch
		}
		if a.CertValidTime != b.CertValidTime {
			return a.CertValidTime
		}
		if a.CertChainValid != b.CertChainValid {
			return a.CertChainValid
		}
		if a.H2ProtocolConfirmed != b.H2ProtocolConfirmed {
			return a.H2ProtocolConfirmed
		}
		if a.H2HeadersReceived != b.H2HeadersReceived {
			return a.H2HeadersReceived
		}
		if a.HTTPStatus != b.HTTPStatus {
			class := func(s int) int {
				switch {
				case s >= 200 && s < 300:
					return 3
				case s >= 300 && s < 400:
					return 2
				case s >= 400 && s < 500:
					return 1
				default:
					return 0
				}
			}
			if class(a.HTTPStatus) != class(b.HTTPStatus) {
				return class(a.HTTPStatus) > class(b.HTTPStatus)
			}
		}
		if a.Timings.TotalProbeLatency() != b.Timings.TotalProbeLatency() {
			return a.Timings.TotalProbeLatency() < b.Timings.TotalProbeLatency()
		}
		return a.SNI < b.SNI
	}
	clustered := make([]Candidate, 0, len(clusters))
	for _, group := range clusters {
		sort.SliceStable(group, func(i, j int) bool { return candidateLess(group[i], group[j]) })
		clustered = append(clustered, group[0])
	}
	sort.SliceStable(clustered, func(i, j int) bool { return candidateLess(clustered[i], clustered[j]) })
	activePTRStats(rtCaches, pipeStats)

	pipeStats.mu.Lock()
	progressln("\n===================================================================================================================")
	progressln("                                   ТЕЛЕМЕТРИЯ АКТИВНОГО СКАНИРОВАНИЯ")
	progressln("===================================================================================================================")
	progressf("[*] IP отобрано для пула:      %d\n", pipeStats.IPSampled)
	progressf("[*] SNI/Domains discovered:    %d\n", len(uniqueDomains))
	progressf("[*] PTR найдено:               %d | system=%d | DoH=%d\n", pipeStats.PTRFound, pipeStats.PTRSystemFallbacks, pipeStats.PTRDoHFallbacks)
	progressf("[*] IP OSINT: IPs=%d | Shodan=%d/%d names=%d | VT=%d/%d names=%d | names-selected=%d\n", pipeStats.IPOSINTIPsSelected, pipeStats.IPOSINTShodanSuccess, pipeStats.IPOSINTShodanAttempts, pipeStats.IPOSINTShodanNames, pipeStats.IPOSINTVTSuccess, pipeStats.IPOSINTVTAttempts, pipeStats.IPOSINTVTNames, pipeStats.IPOSINTSelectedNames)
	progressf("[*] Chaos Domain: roots=%d attempts=%d success=%d names=%d\n", pipeStats.ChaosRootsQueried, pipeStats.ChaosAttempts, pipeStats.ChaosSuccess, pipeStats.ChaosNames)
	progressf("[*] Logical DNS Lookups:       %d (Успех: %d, Ошибок: %d)\n", pipeStats.DNSQueries, pipeStats.DNSSuccess, pipeStats.DNSFailed)
	progressf("    DNS: Resolved=%d, NXDOMAIN=%d, NoIPv4=%d, Timeout=%d, RCODE=%d, Other=%d\n", pipeStats.DNSResolvedIPs, pipeStats.DNSNXDomain, pipeStats.DNSNoIPv4, pipeStats.DNSTimeout, pipeStats.DNSRCODEErrors, pipeStats.DNSOtherErr)
	progressf("[*] DNS target matches:        %d | Valid pairs: %d\n", pipeStats.DNSTargetRangeMatches, pipeStats.DNSValidPairs)
	progressf("[*] TCP connected:              %d | timeout=%d refused=%d other=%d\n", pipeStats.TCPConnected, pipeStats.TCPTimeouts, pipeStats.TCPRefused, pipeStats.TCPOtherErrs)
	progressf("[*] TLS handshake:              %d | timeout=%d certFail=%d other=%d\n", pipeStats.TLSHandshake, pipeStats.TLSTimeouts, pipeStats.TLSValidationFailures, pipeStats.TLSOtherErrs)
	progressf("[*] H2 confirmed:               %d | headers=%d | status=%d\n", pipeStats.H2ProtocolOK, pipeStats.H2HeadersOK, pipeStats.H2StatusOK)
	progressf("    H2 invalid=%d (HeaderImplausible=%d, FrameSize=%d, BadContinuation=%d, HPACK=%d)\n", pipeStats.H2InvalidFrame, pipeStats.H2FrameHeaderImplausible, pipeStats.H2InvalidFrameLength, pipeStats.H2BadContinuation, pipeStats.H2HPACKDecode)
	progressf("[*] Reality-feasible candidates: %d | Unique IPs: %d\n", pipeStats.RealityFeasibleCandidates, len(clustered))
	if pipeStats.PairLimitDrops > 0 {
		progressf("[!] DNS pairs dropped by LimitValidPairs=%d: %d\n", LimitValidPairs, pipeStats.PairLimitDrops)
	}
	pipeStats.mu.Unlock()

	// Resolver telemetry is always useful in this non-debug active scanner.
	rtCaches.DNSStatsMu.Lock()
	progressln("\n[*] DNS resolver health:")
	for _, resolver := range cfg.DNSResolvers {
		st := rtCaches.DNSResolverStats[resolver]
		if st == nil {
			continue
		}
		state := dnsHealthState(rtCaches.DNSHealthWindows[resolver])
		progressf("    %-15s attempts=%d answers=%d nx=%d rcode=%d fail=%d timeout=%d rtt=%.1fms state=%s\n", resolver, st.Attempts, st.Answers, st.NXDomain, st.RCODEErrors, st.Failures, st.Timeouts, st.RTTMs, state)
	}
	rtCaches.DNSStatsMu.Unlock()
	return clustered
}

func getASN(ip string) string {
	client := &http.Client{Timeout: 6 * time.Second}
	var asn string

	resp, err := client.Get(fmt.Sprintf("https://stat.ripe.net/data/network-info/data.json?resource=%s", ip))
	if err == nil {
		defer resp.Body.Close()
		if resp.StatusCode == http.StatusOK {
			var result struct {
				Data struct {
					ASNs []interface{} `json:"asns"`
				} `json:"data"`
			}
			if err := json.NewDecoder(resp.Body).Decode(&result); err == nil {
				if len(result.Data.ASNs) > 0 {
					asn = fmt.Sprintf("%v", result.Data.ASNs[0])
					if !strings.HasPrefix(strings.ToUpper(asn), "AS") {
						asn = "AS" + asn
					}
				}
			}
		}
	}

	if asn == "" {
		resp2, err2 := client.Get(fmt.Sprintf("http://ip-api.com/json/%s?fields=as", ip))
		if err2 == nil {
			if resp2.StatusCode == http.StatusOK {
				var res2 struct {
					AS string `json:"as"`
				}
				if err := json.NewDecoder(resp2.Body).Decode(&res2); err == nil && res2.AS != "" {
					parts := strings.Split(res2.AS, " ")
					if len(parts) > 0 {
						asn = strings.ToUpper(parts[0])
						if !strings.HasPrefix(asn, "AS") {
							asn = "AS" + asn
						}
					}
				}
			}
			resp2.Body.Close()
		}
	}

	if asn == "" {
		asn = "UNKNOWN_ASN"
	}
	return asn
}

func getCountry(ip string) string {
	client := &http.Client{Timeout: 4 * time.Second}
	resp, err := client.Get(fmt.Sprintf("http://ip-api.com/json/%s?fields=countryCode", ip))
	if err != nil {
		return ""
	}
	defer resp.Body.Close()

	if resp.StatusCode == 200 {
		var result struct {
			CountryCode string `json:"countryCode"`
		}
		if err := json.NewDecoder(resp.Body).Decode(&result); err == nil {
			return strings.ToUpper(result.CountryCode)
		}
	}
	return "UNKNOWN"
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
	var result struct {
		Data struct {
			Prefixes []struct {
				Prefix string `json:"prefix"`
			} `json:"prefixes"`
		} `json:"data"`
	}
	if err := json.NewDecoder(io.LimitReader(resp.Body, 1<<20)).Decode(&result); err != nil {
		return nil
	}
	var prefixes []string
	for _, p := range result.Data.Prefixes {
		if !strings.Contains(p.Prefix, ":") {
			prefixes = append(prefixes, p.Prefix)
		}
	}
	return prefixes
}

func filterPrefixesByCountry(prefixes []string, targetCountry string) []string {
	if targetCountry == "" || len(prefixes) == 0 || targetCountry == "UNKNOWN" {
		return prefixes
	}
	targetCountry = strings.ToUpper(targetCountry)

	type QueryItem struct {
		Query string `json:"query"`
	}

	queryToPrefix := make(map[string]string)
	var allQueries []QueryItem

	for _, p := range prefixes {
		ip, _, err := net.ParseCIDR(p)
		if err == nil {
			qIP := ip.String()
			queryToPrefix[qIP] = p
			allQueries = append(allQueries, QueryItem{Query: qIP})
		}
	}

	var matched []string
	batchSize := 100

	for i := 0; i < len(allQueries); i += batchSize {
		end := i + batchSize
		if end > len(allQueries) {
			end = len(allQueries)
		}
		batch := allQueries[i:end]

		reqBody, _ := json.Marshal(batch)
		client := &http.Client{Timeout: 6 * time.Second}
		resp, err := client.Post("http://ip-api.com/batch?fields=query,countryCode,status", "application/json", bytes.NewBuffer(reqBody))
		if err != nil {
			continue
		}

		var resData []struct {
			Query       string `json:"query"`
			CountryCode string `json:"countryCode"`
			Status      string `json:"status"`
		}
		decodeErr := json.NewDecoder(io.LimitReader(resp.Body, 1<<20)).Decode(&resData)
		resp.Body.Close()
		if decodeErr != nil {
			continue
		}

		for _, item := range resData {
			if item.Status == "success" && strings.ToUpper(item.CountryCode) == targetCountry {
				if pref, ok := queryToPrefix[item.Query]; ok {
					matched = append(matched, pref)
				}
			}
		}
	}
	return matched
}

type checkpointData struct {
	Version       string       `json:"version"`
	Stage         string       `json:"stage"`
	TargetIP      string       `json:"target_ip"`
	TargetASN     string       `json:"target_asn"`
	TargetCountry string       `json:"target_country"`
	SampledIPs    []string     `json:"sampled_ips"`
	StageA        []TargetPair `json:"stage_a,omitempty"`
	StageD        []TargetPair `json:"stage_d,omitempty"`
	Final         []Candidate  `json:"final,omitempty"`
}

func saveCheckpoint(path string, cp checkpointData) error {
	if strings.TrimSpace(path) == "" {
		return nil
	}
	tmp := path + ".tmp"
	f, err := os.Create(tmp)
	if err != nil {
		return err
	}
	encErr := json.NewEncoder(f).Encode(cp)
	closeErr := f.Close()
	if encErr != nil {
		_ = os.Remove(tmp)
		return encErr
	}
	if closeErr != nil {
		_ = os.Remove(tmp)
		return closeErr
	}
	return os.Rename(tmp, path)
}

func checkpointMatches(cp checkpointData, cfg Config, sampledIPs []string) bool {
	if cp.Version != "v92" || cp.TargetIP != cfg.TargetIP || cp.TargetASN != cfg.TargetASN || cp.TargetCountry != cfg.TargetCountry {
		return false
	}
	if len(cp.SampledIPs) != len(sampledIPs) {
		return false
	}
	for i := range sampledIPs {
		if cp.SampledIPs[i] != sampledIPs[i] {
			return false
		}
	}
	return true
}

func loadCheckpoint(path string) (checkpointData, error) {
	var cp checkpointData
	f, err := os.Open(path)
	if err != nil {
		return cp, err
	}
	defer f.Close()
	if err := json.NewDecoder(f).Decode(&cp); err != nil {
		return cp, err
	}
	if cp.Version != "v92" {
		return cp, fmt.Errorf("unsupported checkpoint version %q", cp.Version)
	}
	return cp, nil
}

// ================= MAIN =================
func main() {
	uaRng = rand.New(rand.NewSource(time.Now().UnixNano()))

	cfg := Config{
		Workers:           30,
		IPOSINTLimit:      256,
		VTKey:             "dea2ba0b84a3d88ea20a5fb14165e94d170cbe369529dbc57119757e04f1efb5",
		ChaosKey:          "e3c91ed9-2f79-4147-807f-43dd150003e4",
		MaxIPs:            LimitMaxIPs,
		DNSWorkers:        32,
		DNSQueryTimeoutMs: int(DNSQueryTimeoutDefault.Milliseconds()),
		ECSPrefix:         DefaultECSIPv4Prefix,
		DNSResolvers:      normalizeDNSResolvers(strings.Split(DefaultDNSResolvers, ",")),
		TCPTimeoutMs:      3000,
		TLSTimeoutMs:      3000,
		H2ReadTimeoutMs:   3000,
		H2WriteTimeoutMs:  2000,
		Seed:              time.Now().UnixNano(),
	}

	flag.IntVar(&cfg.Workers, "w", 30, "Worker pool size")
	flag.IntVar(&cfg.IPOSINTLimit, "ip-osint-limit", 256, "Maximum sampled IPs for IP OSINT")
	flag.StringVar(&cfg.TargetIP, "vps-ip", "", "IP VPS для определения ASN, страны и ECS")
	flag.Float64Var(&cfg.Rate, "rate", 0, "New TCP/TLS probe rate per second; 0=unlimited")
	flag.BoolVar(&cfg.JSON, "json", false, "Emit JSON Lines instead of the text table")
	flag.StringVar(&cfg.Checkpoint, "checkpoint", "", "Checkpoint file")
	flag.BoolVar(&cfg.Resume, "resume", false, "Resume final results from checkpoint")
	flag.Parse()
	progressJSON = cfg.JSON

	if cfg.Workers < 1 {
		cfg.Workers = 1
	}
	cfg.DNSWorkers = cfg.Workers * 2
	if cfg.DNSWorkers < 8 {
		cfg.DNSWorkers = 8
	}
	if cfg.DNSWorkers > 64 {
		cfg.DNSWorkers = 64
	}
	if cfg.Rate < 0 {
		cfg.Rate = 0
	}
	probeLimiter = ratelimit.New(cfg.Rate)

	parsedIP := net.ParseIP(strings.TrimSpace(cfg.TargetIP))
	if parsedIP == nil || parsedIP.To4() == nil {
		log.Fatalf("[-] Нужен корректный IPv4 через -vps-ip")
	}
	cfg.TargetIP = parsedIP.To4().String()
	cfg.ECSIP = cfg.TargetIP

	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()

	cfg.TargetASN = getASN(cfg.TargetIP)
	if cfg.TargetASN == "UNKNOWN_ASN" {
		log.Fatalf("[-] Не удалось определить ASN для %s", cfg.TargetIP)
	}
	var startupWG sync.WaitGroup
	startupWG.Add(2)
	var startupCountry string
	var cidrs []string
	go func() { defer startupWG.Done(); startupCountry = getCountry(cfg.TargetIP) }()
	go func() { defer startupWG.Done(); cidrs = getPrefixes(cfg.TargetASN) }()
	startupWG.Wait()
	cfg.TargetCountry = startupCountry
	if len(cidrs) == 0 {
		log.Fatalf("[-] Не удалось получить announced prefixes для %s", cfg.TargetASN)
	}

	localPrefix := ""
	for _, c := range cidrs {
		_, ipnet, err := net.ParseCIDR(c)
		if err == nil && ipnet.Contains(parsedIP) {
			localPrefix = c
			break
		}
	}
	if localPrefix == "" {
		log.Fatalf("[-] VPS IP %s не входит в announced prefixes %s", cfg.TargetIP, cfg.TargetASN)
	}

	samplingCIDRs := cidrs
	if cfg.TargetCountry != "" && cfg.TargetCountry != "UNKNOWN" {
		countryCIDRs := filterPrefixesByCountry(cidrs, cfg.TargetCountry)
		if len(countryCIDRs) > 0 {
			samplingCIDRs = countryCIDRs
			foundLocal := false
			for _, prefix := range samplingCIDRs {
				if prefix == localPrefix {
					foundLocal = true
					break
				}
			}
			if !foundLocal {
				samplingCIDRs = append([]string{localPrefix}, samplingCIDRs...)
			}
		} else {
			progressf("[!] Country filter %s не дал prefixes; сканирование остаётся по ASN.\n", cfg.TargetCountry)
		}
	}

	samplingRanges := MergeCIDRs(samplingCIDRs)
	sampledIPs := SampleIPs(samplingRanges, cfg.MaxIPs, cfg.Seed)
	scanRanges := MergeCIDRs(cidrs)
	if len(sampledIPs) == 0 {
		log.Fatalf("[-] Пул IP пуст")
	}

	progressf("[*] Целевой VPS IP:          %s\n", cfg.TargetIP)
	progressf("[*] Announcing ASN:         %s\n", cfg.TargetASN)
	progressf("[*] Страна сервера:          %s\n", cfg.TargetCountry)
	progressf("[*] Фокус sampling:          %d prefixes\n", len(samplingCIDRs))
	progressf("[*] Полный ASN для DNS match: %d prefixes\n", len(cidrs))
	progressf("[*] IP в активном пуле:       %d\n", len(sampledIPs))
	progressf("[*] Workers:                  %d | DNS workers: %d | Rate: %.0f/s\n", cfg.Workers, cfg.DNSWorkers, cfg.Rate)
	progressf("[*] ECS client IP:             %s/%d\n", cfg.ECSIP, cfg.ECSPrefix)
	progressf("[*] DNS pool:                  %d resolvers\n\n", len(cfg.DNSResolvers))

	results := RunPipeline(ctx, cfg, sampledIPs, scanRanges)
	if cfg.Checkpoint != "" {
		_ = saveCheckpoint(cfg.Checkpoint, checkpointData{Version: "v92", Stage: "E", TargetIP: cfg.TargetIP, TargetASN: cfg.TargetASN, TargetCountry: cfg.TargetCountry, SampledIPs: sampledIPs, Final: results})
	}
	if len(results) == 0 {
		progressln("\n[-] Подходящих Reality-feasible HTTP/2 целей не найдено.")
		return
	}

	if cfg.JSON {
		if err := output.WriteJSONLines(os.Stdout, results); err != nil {
			log.Printf("[-] JSON output error: %v", err)
		}
		return
	}

	fmt.Printf("\n[+] Найдено валидных HTTP/2 целей после кластеризации: %d\n\n", len(results))
	fmt.Printf("%-32.32s | %-15.15s | %-6s | %-30.30s | %4s\n", "Цель (SNI)", "IP адрес", "STATUS", "certificate issuer", "RTT")
	fmt.Println(strings.Repeat("-", 101))
	for _, r := range results {
		issuer := r.CertIssuer
		if issuer == "" {
			issuer = "unknown issuer"
		}
		rtt := r.Timings.TotalProbeLatency().Milliseconds()
		fmt.Printf("%-32.32s | %-15.15s | %-6d | %-30.30s | %4dms\n", r.SNI, r.IP, r.HTTPStatus, limitStr(issuer, 30), rtt)
	}

	best := results[0]
	progressln("\n===================================================================================================================")
	fmt.Println("                                   РЕКОМЕНДУЕМАЯ КОНФИГУРАЦИЯ DEST/SNI")
	fmt.Println("===================================================================================================================")
	fmt.Printf("\"dest\": \"%s:443\",\n", best.SNI)
	fmt.Printf("\"serverNames\": [\n  \"%s\"\n]\n\n", best.SNI)
	fmt.Printf("STATUS: %d | TLS: %.0f/20 | certificate issuer: %s | SNI match: %t | Chain: %t | Valid time: %t | Reality feasible: %t | RTT: %d ms\n", best.HTTPStatus, best.RealityScore.TLSQuality, best.CertIssuer, best.CertSNIMatch, best.CertChainValid, best.CertValidTime, best.RealityFeasible, best.Timings.TotalProbeLatency().Milliseconds())
	fmt.Printf("FINAL REALITY SCORE: %.1f/100\n", best.Score)
}
