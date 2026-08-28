package scanning

import (
	"context"
	"sync"
)

// WorkerCount caps concurrency to the number of actual jobs without imposing
// an artificial upper bound on the user-requested worker count.
func WorkerCount(requested, jobs int) int {
	if jobs <= 0 {
		return 0
	}
	if requested < 1 {
		return 1
	}
	if requested > jobs {
		return jobs
	}
	return requested
}

// Map executes a scan function concurrently and returns results in input order.
func Map[T any, R any](ctx context.Context, jobs []T, workers int, fn func(context.Context, T) R) []R {
	if len(jobs) == 0 {
		return nil
	}
	workers = WorkerCount(workers, len(jobs))
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
