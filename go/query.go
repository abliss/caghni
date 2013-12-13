package main

import (
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"github.com/syndtr/goleveldb/leveldb"
	"github.com/syndtr/goleveldb/leveldb/opt"
	"os"
	"runtime"
	"strings"
)

const DEBUG = true

type Fact struct {
	Bone struct {
		Stmt interface{}
		Hyps []interface{}
		Free [][]string
	}
	Meat struct {
		Terms []string
		Kinds []string
	}
	Skin struct {
		Name       string
		License    string
		HypNames   []string
		Delimiters []string
		DepNames   []string
		V          [][]string
		T          [][]string
	}
	Tree struct {
		Cmd   string
		Deps  []string
		Proof []interface{}
		Dkind int
		Dsig  []interface{}
	}
}

type Entry struct {
	Key    string
	Fact   Fact
	IsDone bool
}

func GetFactsByPrefix(db *leveldb.DB, pfix string, out chan<- *Entry) {
	start := []byte(pfix)
	iter := db.NewIterator(nil)
	defer iter.Release()
	end := append(start, byte(0xff))
	iter.Seek(start)
	found := false
	for {
		key := iter.Key()
		if bytes.Compare(key, end) > 0 {
			break
		}
		value := iter.Value()
		keyFact := new(Entry)
		keyFact.Key = string(key)
		err := json.Unmarshal(value, &keyFact.Fact)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\nKey:%s\nValue: %s\n",
				err, key, value)
			panic(-1)
		} else {
			found = true
			out <- keyFact
		}
		fmt.Fprintf(os.Stderr, "Found: %s is %s\n", keyFact.Key, keyFact.Fact.Skin.Name)
		if !iter.Next() {
			break
		}
	}
	if !found {
		fmt.Fprintf(os.Stderr, "Pfix Not Found: %s\n", pfix)
	}
	close(out)
}

func scan_sexp(sexp string, off int) int {
	depth := 0
	for ; off < len(sexp); off++ {
		if sexp[off] == '[' {
			depth++
		} else if sexp[off] == ']' {
			//TODO: escaping? this is okay for scanning past the bone,
			// but there may be bracket chars in the meat.
			depth--
		}
		if depth == 0 {
			return off + 1
		}
	}
	return -1
}

// A JobServer facilitates concurrent graph search by providing:
// 1. a duplicate function call suppressor, similar to singleflight.go
// 2. memoization
// 3. output channel fanout
// 4. deadlock detection
//
// Each JobServer has a Jobber, which performs the actual search. The Jobber is
// a function with the following contract:
// 1. input is a string argument; output is successive Entry Slices
// 2. On each output slice, entry[0].Key must exactly match the input arg
// 3. Each successive output should be an "improvement" on the previous one.
// 4. When no more outputs are coming, send a sentry with entry[0].IsDone set.
// 5. The output channel must not be closed.
// 6. Must be threadsafe.
// 7. Whenever calling back in to a JobServer, must pass its jobid.
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
	Jobber    func(jobid, key string, job chan []*Entry)
	name      string
}

func (this *JobServer) Run() {
	this.reqs = make(chan JobRequest, 2000)
	this.results = make(chan []*Entry, 2000)
	this.last = make(map[string][]*Entry)
	this.done = make(map[string][]*Entry)
	this.listeners = make(map[string]map[string]chan []*Entry)
	for {
		select {
		case req := <-this.reqs:
			key := req.Target
			if DEBUG {
				fmt.Printf("XXXX Request for %s\n", key)
			}
			if last, ok := this.last[key]; ok {
				req.Out <- last
			}
			if sentinel, ok := this.done[key]; ok {
				req.Out <- sentinel
			} else {
				listeners, ok := this.listeners[key]
				if !ok {
					//fmt.Printf("XXXX Jobber %s: no listeners for key %s, jobbing\n", this.name, key)
					listeners = make(map[string]chan []*Entry)
					go this.Jobber(req.Target, req.Target, this.results)
				}
				listeners[req.Parent] = req.Out
				this.listeners[key] = listeners
				// check for cycles
				/*
					if this.name == "Closer" { //XXX
						fmt.Printf("XXXX Jobber %s: %s waiting on %s\n", this.name, req.Parent, key)
					}
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
									fmt.Printf("XXXX Jobber %s: %s cycled: %s\n",
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
			//XX fmt.Printf("XXXX Response for for %s\n", key)
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

// Parses a ghi and emits the label of each stmt on out, followed by an empty
// sentinel.
func parseInterface(fn string, out chan *Entry) {
	file, err := os.Open(fn)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Can't open interface %s: %v\n", fn, err)
		os.Exit(-1)
	}
	scanner := NewScanner(file)
	for scanner.Scan() {
		_ = scanner.Text()
		// TODO: one day these will be keys, not labels
		//XXX pickup
		e := scanner.Entry()
		if DEBUG {
			fmt.Fprintf(os.Stderr, "Axiom: %s\n%s\n%s\n",
				e.Fact.Skin.Name, e.Key, e.Fact)
		}
		out <- e
	}
	if err := scanner.Err(); err != nil {
		fmt.Fprintf(os.Stderr, "Scanner error: %v", err)
		panic(err)
	}
	out <- nil
}

func parseInterfaces(interfaces []string) map[string]*Entry {
	out := make(map[string]*Entry)
	ch := make(chan *Entry)
	jobs := 0
	for _, interfaceFn := range interfaces {
		if len(interfaceFn) > 0 {
			go parseInterface(interfaceFn, ch)
			jobs++
		}
	}
	for jobs > 0 {
		axiom := <-ch
		if axiom != nil {
			out[axiom.Key] = axiom
		} else {
			jobs--
		}
	}
	return out
}

// Given a depmap of entries, return a compact prooflist with duplicates removed
// (each duplicated entry only keeps the last copy); also returns the number of
// ungrounded stmts in the output. The given entry st will be prepended.
func compactify(st *Entry, groundSet map[string]*Entry, depMap map[string][]*Entry) (out []*Entry, stmts int) {
	stmts = 0
	out = make([]*Entry, 0)
	seen := make(map[string]bool)
	for _, es := range depMap {
		for i := range es {
			e := es[len(es)-i-1]
			if !seen[e.Key] {
				seen[e.Key] = true
				out = append(out, e)
				if (len(e.Fact.Tree.Deps) == 0) &&
					(groundSet[e.Fact.Skin.Name] != nil) {
					stmts++
				}
			}
		}
	}
	out = append(out, st)
	// Reverse out
	for i, j := 0, len(out)-1; i < j; i, j = i+1, j-1 {
		out[i], out[j] = out[j], out[i]
	}
	return out, stmts
}

func fmtProof(pf []*Entry) string {
	msg := "==> "
	for _, d := range pf {
		if len(d.Fact.Tree.Deps) == 0 {
			msg += "#"
		}
		msg += d.Fact.Skin.Name + " "
	}
	return msg
}

func main() {
	dbPath := flag.String("d", "facts.leveldb", "path to facts.leveldb")
	imports := flag.String("i", "", "comma-separated list of .ghi imports")
	exports := flag.String("e", "", "comma-separated list of .ghi exports")
	flag.Parse()
	opt := opt.Options{ErrorIfMissing: true}
	db, err := leveldb.OpenFile(*dbPath, &opt)
	if err != nil {
		fmt.Print(err)
		os.Exit(-1)
	}
	defer db.Close()
	groundSet := parseInterfaces(strings.Split(*imports, ","))
	targets := parseInterfaces(strings.Split(*exports, ","))
	var resolver, closer JobServer
	resolver.name = "Resolver"
	// The resolver expects a prefix of a key, and always returns an array of
	// two entries. the first one is a dummy so that its key can match the
	// (sometimes incomplete) target string. The second will be an actual entry,
	// whose key is prefixed by the given target, and which has been
	// closed. When no more results are available, we send the sentinel which
	// has entry[0].IsDone set.
	// Currently, we only ever send one hit.
	resolver.Jobber = func(jobid, target string, out chan []*Entry) {
		sendHit := func(hit *Entry) {
			myOut := make([]*Entry, 2)
			myOut[0] = new(Entry)
			myOut[0].Key = target
			myOut[1] = hit
			out <- myOut
			sentinel := make([]*Entry, 1)
			sentinel[0] = new(Entry)
			sentinel[0].Key = target
			sentinel[0].IsDone = true
			out <- sentinel
		}
		if axiom, ok := groundSet[target]; ok {
			sendHit(axiom)
			return
		}

		ch := make(chan *Entry)
		go GetFactsByPrefix(db, target, ch)
		entries := make([]*Entry, 0)
		for entry := range ch {
			if entry.Key == target {
				sendHit(entry)
				return
			} else if len(entry.Fact.Tree.Deps) > 0 {
				entries = append(entries, entry)
			}
		}
		closures := make(chan []*Entry, 2000)
		for _, e := range entries {
			closer.Job(jobid, e.Key, closures)
		}
		c := <-closures
		sendHit(c[0])
	}
	go resolver.Run()

	closer.name = "Closer"
	// The Closer expects an exact key, and outputs lists of entries such that:
	// 1. the first entry has a key matching the given key
	// 2. each entry's dependencies will be satisfied by something later
	// in the list
	// When no further closures exist, a sentinel will cap the stream by
	// setting entry[0].IsDone to true.
	closer.Jobber = func(jobid, key string, out chan []*Entry) {
		if DEBUG {
			fmt.Printf("XXXX Closing string %s\n", key)
		}
		keySexp := key[0:scan_sexp(key, 0)]
		_ = keySexp //XX
		// there can be only one resloution.
		ch := make(chan []*Entry, 2000)
		resolver.Job(jobid, key, ch)
		target := (<-ch)[1]
		name := fmt.Sprintf("%s/%d", target.Fact.Skin.Name,
			len(target.Fact.Tree.Deps))
		<-ch // clear out the sentinel
		//XX fmt.Printf("XXXX Closing string %s==%s\n", key, name)
		if DEBUG {
			fmt.Printf("XXXX CE %s begin!\n", name)
		}
		numDeps := len(target.Fact.Tree.Deps)
		if numDeps == 0 {
			//XX fmt.Printf("XXXX CE %s as stmt\n", name)
			// stmt has only one closure
			packet := make([]*Entry, 1)
			packet[0] = target
			out <- packet
		} else {
			// resolve and close each dependency
			resolveChan := make(chan []*Entry, 2000)
			tailChan := make(chan []*Entry, 2000)
			depMap := make(map[string][]*Entry, numDeps)
			rJobs := 0
			cJobs := make(map[string]bool)
			var lastOut []*Entry
			var lastStmts int
			for _, dep := range target.Fact.Tree.Deps {
				//XX fmt.Printf("XXXX CE %s, requesting resolve %s\n", name, dep)
				resolver.Job(jobid, dep, resolveChan)
				rJobs++
			}
			for rJobs > 0 || len(cJobs) > 0 {
				select {
				case r := <-resolveChan:
					if r[0].IsDone {
						rJobs--
						//XX fmt.Printf("XXXX CE %s, requesting resolve %s complete, need %d/%d\n", name, r[0].Key, rJobs, len(cJobs))
					} else {
						if cJobs[r[1].Key] {
							if DEBUG {
								fmt.Printf("XXXX CE %s, requesting close %s as %s, already subscribed\n", name, r[1].Key, r[1].Fact.Skin.Name)
							}
						} else {
							if DEBUG {
								fmt.Printf("XXXX CE %s, requesting close %s as %s\n", name, r[1].Key, r[1].Fact.Skin.Name)
							}
							cJobs[r[1].Key] = true
							closer.Job(jobid, r[1].Key, tailChan)
						}
					}
					break
				case t := <-tailChan:
					if t[0].IsDone {
						delete(cJobs, t[0].Key)
						if DEBUG {
							fmt.Printf("XXXX CE %s, requesting close %s complete, need %d/%d\n", name, t[0].Key, rJobs, len(cJobs))
						}
					} else {
						key := t[0].Key
						kSexp := key[0:scan_sexp(key, 0)]
						oldT, ok := depMap[kSexp]
						if !ok {
							numDeps--
							depMap[kSexp] = t
						}
						if numDeps > 0 {
							if DEBUG {
								fmt.Printf("XXXX CE %s need %d\n", name, numDeps)
							}
						} else {
							shouldSend := false
							if lastOut == nil {
								lastOut, lastStmts = compactify(target,
									groundSet, depMap)
								shouldSend = true
							} else {
								depMap[kSexp] = t
								newOut, newStmts := compactify(target,
									groundSet, depMap)
								if newStmts > lastStmts ||
									(newStmts == lastStmts &&
										len(newOut) >= len(lastOut)) {
									// not a better proof, reset
									//XX fmt.Printf("XXXX CE %s no improvement: %s\n", name, fmtProof(t))
									depMap[kSexp] = oldT

								} else {
									// better proof
									lastOut = newOut
									lastStmts = newStmts
									shouldSend = true
								}
							}
							if shouldSend {
								out <- lastOut
								if DEBUG {
									fmt.Printf("XXXX CE %s best #%d: %s\n", name, lastStmts, fmtProof(lastOut))
								}
								break
							}
						}
					}
				}
			}
		}
		//XX fmt.Printf("XXXX CE %s, z all done.\n", name)
		sentinel := make([]*Entry, 1)
		sentinel[0] = new(Entry)
		sentinel[0].Key = key
		sentinel[0].IsDone = true
		out <- sentinel
	}
	go closer.Run()

	out := make(chan []*Entry, len(targets))
	jobs := 0
	for key := range targets {
		fmt.Printf("XXXX closing %s\n", key)
		closer.Job("ROOT", key, out)
		jobs++
	}

	for res := range out {
		fmt.Printf("Result %v\n", res)

		if res[0].IsDone {
			jobs--
			if jobs == 0 {
				os.Exit(0)
			}
		} else {
			depMap := make(map[string][]*Entry)

			depMap[res[0].Key] = res
			newOut, newStmts := compactify(nil, groundSet, depMap)
			fmt.Printf("Result #%d: %s\n", newStmts, fmtProof(newOut))
			// TODO: why sometimes a problem here?

		}
	}
}
