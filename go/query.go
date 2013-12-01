package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"github.com/syndtr/goleveldb/leveldb"
	"os"
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
	es := make([]Entry, 0, 10)
	start := []byte(pfix)
	iter := db.NewIterator(nil)
	defer iter.Release()
	end := append(start, byte(0xff))
	iter.Seek(start)
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
			out <- keyFact
			es = append(es, keyFact)
		}
		fmt.Fprintf(os.Stderr, "Found: %s is %s\n", keyFact.Key, keyFact.Fact.Skin.Name)
		if !iter.Next() {
			break
		}
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

// Ensures that no more than one goroutine is working on closing any given
// entry.
type JobRequest struct {
	Target string
	Out    chan []Entry
}
type JobServer struct {
	reqs      chan JobRequest
	results   chan []Entry
	listeners map[string][]chan []Entry
	last      map[string][]Entry
	done      map[string][]Entry
	Jobber    func(key string, job chan []Entry)
	name      string
	// Jobber contract: every Entry must have a zeroth item whose Key is equal
	// to the given key. Its IsDone should be set to true (and Entry
	// unpopulated) to indicate it that all answers have been generated.
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
					go this.Jobber(req.Target, this.results)
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
func (this *JobServer) Job(target string, out chan []Entry) {
	jobReq := JobRequest{target, out}
	this.reqs <- jobReq
}

func main() {
	db, err := leveldb.OpenFile(os.Args[1], nil)
	if err != nil {
		fmt.Print(err)
		panic(-1)
	}
	defer db.Close()
	var resolver, closer JobServer
	resolver.name = "Resolver"
	closer.name = "Closer"
	var closeEntry func(target string, out chan []Entry)
	var resolveKey func(target string, out chan []Entry)
	closeEntry = func(key string, out chan []Entry) {
		fmt.Printf("XXXX Closing string %s\n", key)
		keySexp := key[0:scan_sexp(key, 0)]
		// since this is a full key, there can be only one resloution.
		ch := make(chan []Entry, 2000)
		resolver.Job(key, ch)
		target := (<-ch)[1]

		fmt.Printf("XXXX Closing entry %s\n", target.Fact.Skin.Name)
		numDeps := len(target.Fact.Tree.Deps)
		if numDeps == 0 {
			// stmt has only one closure
			packet := make([]Entry, 1)
			packet[0] = target
			out <- packet
		} else {
			// resolve and close each dependency
			resolveChan := make(chan []Entry, 2000)
			tailChan := make(chan []Entry, 2000)
			bestTail := make(map[string][]Entry, numDeps)
			rJobs, tJobs := 0, 0
			for _, dep := range target.Fact.Tree.Deps {
				fmt.Printf("XXXX Closing entry %s, requesting resolve %s\n", target.Fact.Skin.Name, dep)
				resolver.Job(dep, resolveChan)
				rJobs++
			}
			for rJobs > 0 || tJobs > 0 {
				select {
				case r := <-resolveChan:
					if r[0].IsDone {
						rJobs--
						fmt.Printf("XXXX Closing entry %s, requesting resolve %s complete, need %d\n", target.Fact.Skin.Name, r[0].Key, rJobs)
					} else {
						fmt.Printf("XXXX Closing entry %s, requesting close %s\n", target.Fact.Skin.Name, r[1].Key)

						closer.Job(r[1].Key, tailChan)
						tJobs++
					}
					break
				case t := <-tailChan:
					if t[0].IsDone {
						tJobs--
						fmt.Printf("XXXX Closing entry %s, requesting close %s complete, need %d\n", target.Fact.Skin.Name, t[0].Key, tJobs)

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
							oldT, ok := bestTail[kSexp]
							if !ok {
								numDeps--
							}
							if !ok || len(oldT) == 1 || len(oldT) > len(t) {
								// New is better if there is no old, or if old
								// was just a stmt, or if old was longer.
								bestTail[kSexp] = t
								if numDeps == 0 {
									axioms := make(map[string]bool)
									msg := "==> "
									newBest := make([]Entry, 1)
									newBest[0] = target
									msg += target.Fact.Skin.Name
									msg += ": "
									for _, v := range bestTail {
										for _, d := range v {
											newBest = append(newBest, d)
											if len(d.Fact.Tree.Deps) == 0 {
												msg += "#"
												axioms[d.Key] = true
											}
											msg += d.Fact.Skin.Name + " "
										}
										msg += "; "
									}
									fmt.Printf("XXXX Closing entry %s best #%d: %s\n",
										target.Fact.Skin.Name, len(axioms), msg)
									out <- newBest
								} else {
									fmt.Printf("XXXX Closing entry %s need %d\n", target.Fact.Skin.Name, numDeps)
								}
							}
						}
					}
				}
			}
		}
		sentinel := make([]Entry, 1)
		sentinel[0].Key = key
		sentinel[0].IsDone = true
		out <- sentinel
	}
	// First elt of the array is a dummy; second is the hit.
	resolveKey = func(target string, out chan []Entry) {
		fmt.Printf("XXXX resolving string %s\n", target)
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
				fmt.Printf("XXXX resolving string %s to stmt %s\n", target,
					entry.Fact.Skin.Name)
				sendHit(entry)
			} else {
				// thm prefix matches get closed then sent out
				fmt.Printf("XXXX resolving string %s, requesting closure %s is %s\n", target, entry.Key, entry.Fact.Skin.Name)
				go closer.Job(entry.Key, closeCh)
				numJobs++
			}
		}
		for numJobs > 0 {
			closed := <-closeCh
			if closed[0].IsDone {
				numJobs--
				fmt.Printf("XXXX resolving string %s, requesting closure %s no longer, need %d\n", target, closed[0].Key, numJobs)
			} else {
				entry := closed[0]
				fmt.Printf("XXXX resolving string %s, to thm %s\n", target,
					entry.Fact.Skin.Name)
				sendHit(entry)
			}
		}
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
	//key := "[[[0,[1,T0.0],[0,[2,T0.0,[3,T0.1,T0.2]],[4,[2,T0.0,T0.1],[2,T0.0,T0.2]]]],[],[]],[[->,prime,|,*,\\/,0,1,S],[nat]]]!1cce0fb9e7a3cdf178bcf279c8520a361a7ad57f" // key for euclidlem
	//key := "[[[0,T0.0,T0.1],[[0,T0.2,T0.3],[1,T0.2,T0.0],[1,T0.3,T0.1]],[]],[[->,<->],[wff]]]!efed0f44c9e16d9f35705d04dad6c5e9f20d302d" // for 3imtr3i
	//key := "[[[0,[1,[1,T0.0]],T0.0],[],[]],[[->,-.],[wff]]]!5b652db562c5aeeac4b706e4c7f45acf8cca779b" // key for dn
	key := "[[[0,T0.0,T0.1],[T0.1],[]],[[->],[wff]]]!be10f0f547e610a427a5d2a85c5d3cff3dcdaf71" // key for a1i
	go closer.Job(key, out)
	for res := range out {
		fmt.Printf("XXXX Result length: %d\n", len(res))
		for i := range res {
			e := res[len(res)-i-1]
			fmt.Printf("%s  ", e.Fact.Skin.Name)
		}
		fmt.Println()
	}
}
