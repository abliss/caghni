package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"github.com/syndtr/goleveldb/leveldb"
	"os"
	"sync"
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
	Key  string
	Fact Fact
}

func GetFactsByPrefix(db *leveldb.DB, cache map[string][]Entry, mu *sync.Mutex,
	pfix string, out chan<- Entry) {
	mu.Lock()
	es, ok := cache[pfix]
	mu.Unlock()
	if !ok {
		es = make([]Entry, 0, 10)
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
			if !iter.Next() {
				break
			}
		}
		mu.Lock()
		cache[pfix] = es
		mu.Unlock()
	} else {
		for _, e := range es {
			out <- e
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
	Target Entry
	Out    chan []Entry
}
type JobServer struct {
	reqs   chan JobRequest
	jobs   map[string]chan []Entry
	Jobber func(target Entry, job chan []Entry)
}

func (this *JobServer) Run() {
	this.jobs = make(map[string]chan []Entry)
	this.reqs = make(chan JobRequest, 100)
	for {
		req, ok := <-this.reqs
		if !ok {
			break
		}
		job, ok := this.jobs[req.Target.Key]
		if !ok {
			job = make(chan []Entry, 100)
			this.jobs[req.Target.Key] = job
			go this.Jobber(req.Target, job)
		}
		go func() {
			res := <-job
			job <- res
			req.Out <- res
		}()
	}
}

// Safe to call from anywhere
func (this *JobServer) Job(target Entry, out chan []Entry) {
	jobReq := JobRequest{target, out}
	this.reqs <- jobReq
}

func main() {
	db, err := leveldb.OpenFile("out-v2/facts.leveldb", nil)
	if err != nil {
		fmt.Print(err)
		panic(-1)
	}
	defer db.Close()
	dbCache := make(map[string][]Entry)
	euclidlem := "[[[0,[1,T0.0],[0,[2,T0.0,[3,T0.1,T0.2]],[4,[2,T0.0,T0.1],[2,T0.0,T0.2]]]],[],[]],[[->,prime,|,*,\\/,0,1,S],[nat]]]" // key for euclidlem

	var jobServer JobServer
	var closeEntry func(target Entry, out chan []Entry)
	var closeString func(target string, out chan []Entry)
	closeEntry = func(target Entry, out chan []Entry) {
		numDeps := len(target.Fact.Tree.Deps)
		tail := make([]Entry, 1, numDeps+1)
		tail[0] = target
		tailChan := make(chan []Entry, 100)
		for _, dep := range target.Fact.Tree.Deps {
			go closeString(dep, tailChan)
		}

		for numDeps > 0 {
			es := <-tailChan
			tail = append(tail, es...)
			numDeps--
		}
		if len(tail) > 1 {
			tail2 := make([]Entry, len(tail))
			fmt.Printf("Closed %s: ", target.Fact.Skin.Name)
			dedupe := make(map[string]bool, len(tail))
			j := len(tail)
			for i := range tail {
				e := tail[len(tail)-i-1]
				if !dedupe[e.Key] {
					dedupe[e.Key] = true
					j--
					tail2[j] = e
					fmt.Printf("%s ", e.Fact.Skin.Name)
				}
			}
			fmt.Println()
			tail = tail2[j:]
		}
		out <- tail
	}
	cacheMutex := new(sync.Mutex) //TODO: hack
	closeString = func(target string, out chan []Entry) {
		ch := make(chan Entry, 100)
		go GetFactsByPrefix(db, dbCache, cacheMutex, target, ch)
		myOut := make(chan []Entry, 100)
		numJobs := 0
		for {
			entry, ok := <-ch
			if !ok {
				break
			}
			jobServer.Job(entry, myOut)
			numJobs++
		}
		var bestRes []Entry
		var bestLen int
		for numJobs > 0 {
			res := <-myOut
			numJobs--
			if (bestLen == 0) || (bestLen > len(res)) {
				bestRes = res
				bestLen = len(res)
			}
		}
		out <- bestRes
	}
	jobServer.Jobber = closeEntry
	go jobServer.Run()

	out := make(chan []Entry, 100)
	go closeString(euclidlem, out)
	res := <-out
	fmt.Printf("Result length: %d\n", len(res))
	for i := range res {
		e := res[len(res)-i-1]
		fmt.Printf("%s  ", e.Fact.Skin.Name)
	}
	fmt.Println()
}
