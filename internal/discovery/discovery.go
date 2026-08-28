package discovery

import (
	"context"
	"sync"
)

// Map executes a discovery function concurrently and returns results in input order.
func Map[T any, R any](ctx context.Context, jobs []T, workers int, fn func(context.Context, T) R) []R {
	if len(jobs) == 0 {
		return nil
	}
	if workers < 1 {
		workers = 1
	}
	if workers > len(jobs) {
		workers = len(jobs)
	}
	results := make([]R, len(jobs))
	indices := make(chan int)
	var wg sync.WaitGroup
	for i := 0; i < workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for idx := range indices {
				if ctx.Err() != nil {
					return
				}
				results[idx] = fn(ctx, jobs[idx])
			}
		}()
	}
	for i := range jobs {
		select {
		case indices <- i:
		case <-ctx.Done():
			break
		}
		if ctx.Err() != nil {
			break
		}
	}
	close(indices)
	wg.Wait()
	return results
}
