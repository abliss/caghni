package main

import (
	"runtime"
)

// A JobServer facilitates concurrent graph search by providing:
// 1. a duplicate function call suppressor, similar to singleflight.go
// 2. memoization
// 3. output channel fanout
// 4. deadlock detection
//
//
// TODO: currently cannot detect deadlocks spread between multiple servers. an
// external lockserver may be required for that.
type JobRequest struct {
	Parent string
	Target string
	Out    chan []*Entry
}
type JobServer struct {
	reqs      chan JobRequest
	results   chan []*Entry
	listeners map[string]map[string]chan []*Entry
	last      map[string][]*Entry
	done      map[string][]*Entry
	jobber    Jobber
	name      string
}

// Each JobServer has a Jobber, which performs the actual search. The Jobber is
// a function with the following contract:
// 1. input is a string argument; output is successive Entry Slices
// 2. On each output slice, entry[0].Key must exactly match the input arg
// 3. Each successive output should be an "improvement" on the previous one.
// 4. When no more outputs are coming, send a sentry with entry[0].IsDone set.
// 5. The output channel must not be closed.
// 6. Must be threadsafe.
// 7. Whenever calling back in to a JobServer, must pass its jobid.
type Jobber func(jobid, key string, job chan []*Entry)

func (this *JobServer) Run(jobber Jobber) {
	this.jobber = jobber
	this.reqs = make(chan JobRequest, 2000)
	this.results = make(chan []*Entry, 2000)
	this.last = make(map[string][]*Entry)
	this.done = make(map[string][]*Entry)
	this.listeners = make(map[string]map[string]chan []*Entry)
	for {
		select {
		case req := <-this.reqs:
			key := req.Target
			if last, ok := this.last[key]; ok {
				req.Out <- last
			}
			if sentinel, ok := this.done[key]; ok {
				req.Out <- sentinel
			} else {
				listeners, ok := this.listeners[key]
				if !ok {
					listeners = make(map[string]chan []*Entry)
					go this.jobber(req.Target, req.Target, this.results)
				}
				listeners[req.Parent] = req.Out
				this.listeners[key] = listeners
				// check for cycles
				/*
										work := make([]string, 1)
										work[0] = req.Parent
										var d string
										msg := "Cycle:\n"
										for len(work) > 0 {
											d, work = work[0], work[1:]
											msg += d + "\n"
											for k := range this.listeners[d] {
												if _, ok = listeners[k]; !ok {
													listeners[k] = nil
													work = append(work, k)
													if k == key {
														fmt.Fprintf(os.Stderr,
					                                        "DEBUG: Jobber %s: %s cycled: %s\n",
															this.name, key, msg)
														//TODO: pick less arbitrary target to kill
														sentinel := make([]*Entry, 1)
														sentinel[0] = new(Entry)
														sentinel[0].Key = key
														sentinel[0].IsDone = true
														this.results <- sentinel
														work = nil
														break
													}
												}
											}
										}
				*/
			}
		case res := <-this.results:
			key := res[0].Key
			if _, ok := this.done[key]; !ok {
				for _, listenerChan := range this.listeners[key] {
					if listenerChan != nil {
						listenerChan <- res
					}
				}
				if res[0].IsDone {
					this.done[key] = res
					delete(this.listeners, key)
				} else {
					this.last[key] = res
				}
			}
		}
	}
}

// Safe to call from anywhere
func (this *JobServer) Job(jobid, target string, out chan []*Entry) {
	jobReq := JobRequest{jobid, target, out}
	// for/select in case Run() hasn't been called yet
	for {
		select {
		case this.reqs <- jobReq:
			return
		default:
			runtime.Gosched()
		}
	}
}
