package main

import (
	"bufio"
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"github.com/syndtr/goleveldb/leveldb"
	"github.com/syndtr/goleveldb/leveldb/opt"
	"os"
	"regexp"
	"strings"
)

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

func GetFactsByPrefix(db *leveldb.DB, pfix string, out chan<- Entry) {
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
		var keyFact Entry
		keyFact.Key = string(key)
		err := json.Unmarshal(value, &keyFact.Fact)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\nValue: %s\n", err, value)
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
type JobRequest struct {
	Parent string
	Target string
	Out    chan []Entry
}
type JobServer struct {
	reqs      chan JobRequest
	results   chan []Entry
	listeners map[string][]chan []Entry
	last      map[string][]Entry
	done      map[string][]Entry
	Jobber    func(jobid, key string, job chan []Entry)
	name      string
}

func (this *JobServer) Run() {
	this.reqs = make(chan JobRequest, 2000)
	this.results = make(chan []Entry, 2000)
	this.last = make(map[string][]Entry)
	this.done = make(map[string][]Entry)
	this.listeners = make(map[string][]chan []Entry)
	for {
		select {
		case req := <-this.reqs:
			key := req.Target
			//XX fmt.Printf("XXXX Request for %s\n", key)
			if last, ok := this.last[key]; ok {
				req.Out <- last
			}
			if sentinel, ok := this.done[key]; ok {
				req.Out <- sentinel
			} else {
				listeners, ok := this.listeners[key]
				if !ok {
					//fmt.Printf("XXXX Jobber %s: no listeners for key %s, jobbing\n", this.name, key)
					listeners = make([]chan []Entry, 0, 1)
					go this.Jobber(this.name, req.Target, this.results)
				}
				this.listeners[key] = append(listeners, req.Out)
			}
		case res := <-this.results:
			key := res[0].Key
			//XX fmt.Printf("XXXX Response for for %s\n", key)
			for _, listener := range this.listeners[key] {
				listener <- res
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

// Safe to call from anywhere
func (this *JobServer) Job(jobid, target string, out chan []Entry) {
	jobReq := JobRequest{jobid, target, out}
	// for/select in case Run() hasn't been called yet
	for {
		select {
		case this.reqs <- jobReq:
			return
		default:
		}
	}
}

func parseIncludes(includes []string) map[string]bool {
	out := make(map[string]bool)
	stmtRegexp, err := regexp.Compile("^\\s*stmt\\s+\\((\\S+)\\s")
	if err != nil {
		fmt.Fprintf(os.Stderr, "Bad regexp: %v\n", err)
		panic(-1)
	}
	for _, include := range includes {
		if len(include) > 0 {
			file, err := os.Open(include)
			if err != nil {
				fmt.Fprintf(os.Stderr, "Can't open include %s: %v\n",
					include, err)
				os.Exit(-1)
			}
			scanner := bufio.NewScanner(file)
			for scanner.Scan() {
				line := scanner.Text()
				// TODO: should actually parse these
				if m := stmtRegexp.FindStringSubmatch(line); len(m) > 0 {
					fmt.Printf("Axiom: %s\n", m[1])
					out[m[1]] = true
				}
			}
		}
	}
	return out
}

// Given a depmap of entries, return a compact prooflist with duplicates removed
// (each duplicated entry only keeps the last copy); also returns the number of
// ungrounded stmts in the output. The given entry st will be prepended.
func compactify(st Entry, groundSet map[string]bool, depMap map[string][]Entry) (out []Entry, stmts int) {
	stmts = 0
	out = make([]Entry, 0)
	seen := make(map[string]bool)
	for _, es := range depMap {
		for i := range es {
			e := es[len(es)-i-1]
			if !seen[e.Key] {
				seen[e.Key] = true
				out = append(out, e)
				if len(e.Fact.Tree.Deps) == 0 && !groundSet[e.Fact.Skin.Name] {
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

func fmtProof(pf []Entry) string {
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
	includes := flag.String("i", "", "comma-separated list of .ghi includes")
	flag.Parse()
	opt := opt.Options{ErrorIfMissing: true}
	db, err := leveldb.OpenFile(*dbPath, &opt)
	if err != nil {
		fmt.Print(err)
		os.Exit(-1)
	}
	defer db.Close()
	groundSet := parseIncludes(strings.Split(*includes, ","))
	_ = groundSet //XXX
	var resolver, closer JobServer
	resolver.name = "Resolver"
	closer.name = "Closer"
	var closeEntry func(jobid, target string, out chan []Entry)
	var resolveKey func(jobid, target string, out chan []Entry)
	// The Closer expects an exact key, and outputs lists of entries such that:
	// 1. the first entry has a key matching the given key
	// 2. each entry's dependencies will be satisfied by something later
	// in the list
	// When no further closures exist, a sentinel will cap the stream by
	// setting entry[0].IsDone to true.
	closeEntry = func(jobid, key string, out chan []Entry) {
		fmt.Printf("XXXX Closing string %s\n", key)
		keySexp := key[0:scan_sexp(key, 0)]
		// since this is a full key, there can be only one resloution.
		ch := make(chan []Entry, 2000)
		resolver.Job(jobid, key, ch)
		target := (<-ch)[1]
		name := fmt.Sprintf("%s/%d", target.Fact.Skin.Name,
			len(target.Fact.Tree.Deps))
		<-ch // clear out the sentinel
		fmt.Printf("XXXX Closing string %s==%s\n", key, name)
		fmt.Printf("XXXX CE %s begin!\n", name)
		numDeps := len(target.Fact.Tree.Deps)
		if numDeps == 0 {
			fmt.Printf("XXXX CE %s as stmt\n", name)
			// stmt has only one closure
			packet := make([]Entry, 1)
			packet[0] = target
			out <- packet
		} else {
			// resolve and close each dependency
			resolveChan := make(chan []Entry, 2000)
			tailChan := make(chan []Entry, 2000)
			depMap := make(map[string][]Entry, numDeps)
			rJobs := 0
			cJobs := make(map[string]bool)
			var lastOut []Entry
			var lastStmts int
			for _, dep := range target.Fact.Tree.Deps {
				fmt.Printf("XXXX CE %s, requesting resolve %s\n", name, dep)
				resolver.Job(jobid, dep, resolveChan)
				rJobs++
			}
			for rJobs > 0 || len(cJobs) > 0 {
				select {
				case r := <-resolveChan:
					if r[0].IsDone {
						rJobs--
						fmt.Printf("XXXX CE %s, requesting resolve %s complete, need %d/%d\n", name, r[0].Key, rJobs, len(cJobs))
					} else {
						if cJobs[r[1].Key] {
							fmt.Printf("XXXX CE %s, requesting close %s as %s, already subscribed\n", name, r[1].Key, r[1].Fact.Skin.Name)
						} else {
							fmt.Printf("XXXX CE %s, requesting close %s as %s\n", name, r[1].Key, r[1].Fact.Skin.Name)
							cJobs[r[1].Key] = true
							closer.Job(jobid, r[1].Key, tailChan)
						}
					}
					break
				case t := <-tailChan:
					if t[0].IsDone {
						delete(cJobs, t[0].Key)
						fmt.Printf("XXXX CE %s, requesting close %s complete, need %d/%d\n", name, t[0].Key, rJobs, len(cJobs))
					} else {
						var cycle bool
						for _, d := range t {
							// make sure proposed closure does not cycle
							dSexp := d.Key[0:scan_sexp(d.Key, 0)]
							if dSexp == keySexp {
								cycle = true
								break
							}
						}
						if !cycle {
							key := t[0].Key
							kSexp := key[0:scan_sexp(key, 0)]
							oldT, ok := depMap[kSexp]
							if !ok {
								numDeps--
								depMap[kSexp] = t
							}
							if numDeps > 0 {
								fmt.Printf("XXXX CE %s need %d\n", name, numDeps)
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
									// XXX logging below
									fmt.Printf("XXXX CE %s best #%d: %s\n",
										name, lastStmts, fmtProof(lastOut))
								}
							}
						}
					}
				}
			}
		}
		fmt.Printf("XXXX CE %s, z all done.\n", name)
		sentinel := make([]Entry, 1)
		sentinel[0].Key = key
		sentinel[0].IsDone = true
		out <- sentinel
	}
	// The resolver expects a prefix of a key, and always returns an array of
	// two entries. the first one is a dummy so that its key can match the
	// (sometimes incomplete) target string. The second will be an actual entry,
	// whose key is prefixed by the given target, and which has been
	// closed. When no more results are available, we send the sentinel which
	// has entry[0].IsDone set.
	resolveKey = func(jobid, target string, out chan []Entry) {
		fmt.Printf("XXXX RS %s\n", target)
		sendHit := func(e Entry) {
			myOut := make([]Entry, 2)
			myOut[0].Key = target
			myOut[1] = e
			out <- myOut
		}
		ch := make(chan Entry, 2000)
		go GetFactsByPrefix(db, target, ch)
		closeCh := make(chan []Entry, 2000)
		numJobs := 0
		for entry := range ch {
			if len(entry.Fact.Tree.Deps) == 0 || entry.Key == target {
				// stmts and exact matches go out right away
				fmt.Printf("XXXX RS %s to stmt %s\n",
					target, entry.Fact.Skin.Name)
				sendHit(entry)
				if groundSet[entry.Fact.Skin.Name] {
					fmt.Printf("XXXX RS %s to stmt %s AX\n",
						target, entry.Fact.Skin.Name)

					numJobs = 0
					break
				}
			} else {
				// thm prefix matches get closed then sent out
				fmt.Printf("XXXX RS %s, requesting closure %s is %s\n", target, entry.Key, entry.Fact.Skin.Name)
				closer.Job(jobid, entry.Key, closeCh)
				numJobs++
			}
		}
		bestStmts := -1
		bestLen := -1
		for numJobs > 0 {
			closed := <-closeCh
			if closed[0].IsDone {
				numJobs--
				fmt.Printf("XXXX RS %s, requesting closure %s no longer, need %d\n", target, closed[0].Key, numJobs)
			} else {
				stmts := make(map[string]bool)
				for _, e := range closed {
					if len(e.Fact.Tree.Deps) == 0 &&
						!groundSet[e.Fact.Skin.Name] &&
						!stmts[e.Fact.Skin.Name] {
						stmts[e.Fact.Skin.Name] = true
					}
				}
				newLen := len(closed)
				if bestStmts == -1 || len(stmts) < bestStmts ||
					(len(stmts) == bestStmts && newLen < bestLen) {
					bestStmts = len(stmts)
					bestLen = newLen
					entry := closed[0]
					fmt.Printf("XXXX RS %s, to thm %s, stmts=%d, len=%d\n",
						target, entry.Fact.Skin.Name, bestStmts, bestLen)
					sendHit(entry)
				}
			}
		}
		fmt.Printf("XXXX RS %s, all done\n", target)
		sentinel := make([]Entry, 1)
		sentinel[0].Key = target
		sentinel[0].IsDone = true
		out <- sentinel
	}
	closer.Jobber = closeEntry
	resolver.Jobber = resolveKey
	go closer.Run()
	go resolver.Run()

	out := make(chan []Entry, 2000)
	//key := "[[[0,[1,T0.0],[0,[2,T0.0,[3,T0.1,T0.2]],[4,[2,T0.0,T0.1],[2,T0.0,T0.2]]]],[],[]],[[->,prime,|,*,\\/,0,1,S],[nat]]]" // key for euclidlem
	//key := "[[[0,T0.0,T0.1],[[0,T0.2,T0.3],[1,T0.2,T0.0],[1,T0.3,T0.1]],[]],[[->,<->],[wff]]]" // for 3imtr3i
	key := "[[[0,[1,[1,T0.0]],T0.0],[],[]],[[->,-.],[wff]]]!f14578e032bd77f8efc9cee923c161e6f5ca0616" // key for dn
	//key := "[[[0,T0.0,T0.1],[T0.1],[]],[[->],[wff]]]" // key for a1i
	closer.Job("", key, out)
	for res := range out {
		if res[0].IsDone {
			fmt.Printf("XXXX No more results.\n")
			break
		}
		fmt.Printf("XXXX Result length %d: %s\n", len(res), fmtProof(res))
	}
}
