package main

import (
	"flag"
	"fmt"
	"github.com/syndtr/goleveldb/leveldb"
	"github.com/syndtr/goleveldb/leveldb/opt"
	"os"
	"strings"
)

const DEBUG = false

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
	go resolver.Run(func(jobid, target string, out chan []*Entry) {
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
		myOut := make([]*Entry, 1)
		myOut[0] = new(Entry)
		myOut[0].Key = target
		myOut = append(myOut, c...)
		out <- myOut
		sentinel := make([]*Entry, 1)
		sentinel[0] = new(Entry)
		sentinel[0].Key = target
		sentinel[0].IsDone = true
		out <- sentinel
	})

	closer.name = "Closer"
	// The Closer expects an exact key, and outputs lists of entries such that:
	// 1. the first entry has a key matching the given key
	// 2. each entry's dependencies will be satisfied by something later
	// in the list
	// When no further closures exist, a sentinel will cap the stream by
	// setting entry[0].IsDone to true.
	go closer.Run(func(jobid, key string, out chan []*Entry) {
		if DEBUG {
			fmt.Printf("XXXX Closing string %s\n", key)
		}
		// there can be only one resloution.
		ch := make(chan []*Entry, 2000)
		resolver.Job(jobid, key, ch)
		target := (<-ch)[1]
		name := fmt.Sprintf("%s/%d", target.Fact.Skin.Name,
			len(target.Fact.Tree.Deps))
		<-ch // clear out the sentinel
		//XX fmt.Printf("XXXX Closing string %s==%s\n", key, name)
		if DEBUG {
			fmt.Printf("XXXX CE %s begin for %s:%s!\n", name, jobid, key)
		}
		numDeps := len(target.Fact.Tree.Deps)
		if numDeps == 0 {
			if DEBUG {
				fmt.Printf("XXXX CE %s as stmt\n", name)
			}
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
	})

	out := make(chan []*Entry, len(targets))
	jobs := 0
	for key := range targets {
		resolver.Job("ROOT."+key, key, out)
		jobs++
	}
	depMap := make(map[string][]*Entry)

	for jobs > 0 {
		res := <-out
		if !res[0].IsDone {
			//XX fmt.Printf("Result len %d for %s\n", len(res), res[0].Key)
			if depMap[res[0].Key] == nil {
				depMap[res[0].Key] = res[1:]
				jobs--
			}
		}
	}
	newOut, _ := compactify(nil, groundSet, depMap)
	_, err = WriteProofs(os.Stdout, newOut[1:])
	if err != nil {
		fmt.Printf("Error: %v\n", err)
		os.Exit(-1)
	}
	os.Exit(0)
}
