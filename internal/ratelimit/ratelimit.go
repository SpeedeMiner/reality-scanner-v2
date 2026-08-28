package ratelimit

import (
	"context"
	"sync"
	"time"
)

type Limiter struct {
	rate float64
	mu   sync.Mutex
	next time.Time
}

func New(rate float64) *Limiter { return &Limiter{rate: rate} }
func (l *Limiter) Wait(ctx context.Context) error {
	if l == nil || l.rate <= 0 {
		return nil
	}
	intervalNanos := float64(time.Second) / l.rate
	if intervalNanos < 1 {
		intervalNanos = 1
	}
	interval := time.Duration(intervalNanos)
	l.mu.Lock()
	now := time.Now()
	if l.next.Before(now) {
		l.next = now
	}
	at := l.next
	l.next = l.next.Add(interval)
	l.mu.Unlock()
	d := time.Until(at)
	if d <= 0 {
		return nil
	}
	t := time.NewTimer(d)
	defer t.Stop()
	select {
	case <-t.C:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}
