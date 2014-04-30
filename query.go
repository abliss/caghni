package main

import (
	"container/heap"
	"flag"
	"fmt"
	"github.com/syndtr/goleveldb/leveldb"
	"github.com/syndtr/goleveldb/leveldb/opt"
	"log"
	"os"
	"runtime/pprof"
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
			out[axiom.MarkStr()] = axiom
		} else {
			jobs--
		}
	}
	return out
}

// Given a depmap of entries, return a compact prooflist with duplicates removed
// (each duplicated entry only keeps the last copy); also returns the number of
// ungrounded stmts in the output. The given entry st will be prepended.
func compactify(st *Entry, groundSet map[string]*Entry,
	depMap map[string][]*Entry) (out []*Entry, stmts int) {
	stmts = 0
	out = make([]*Entry, 0)
	seen := make(map[string]bool)
	for _, es := range depMap {
		for i := range es {
			e := es[len(es)-i-1]
			if !seen[e.Key] {
				seen[e.Key] = true
				out = append(out, e)
				if (len(e.Fact.Deps()) == 0) &&
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

func churn(db *leveldb.DB, groundMeat map[string][]*Entry,
	drafts *DraftHeap, maxLaps int) *Draft {
	//draftsSeen := make(map[string]bool)
	laps := 0
	for len(*drafts) > 0 {
		draft := heap.Pop(drafts).(*Draft)
		mark, ok := draft.TopNeed()
		if !ok {
			panic("No need!?")
		}
		bone := mark.BoneKey()
		needers := make([]*Draft, 1) // TODO: scan for other drafts needing this
		needers[0] = draft
		if DEBUG {
			fmt.Fprintf(os.Stderr, "%s (%f) needs %v\n", draft, draft.Score,
				mark.String())
		}
		// First check axioms in the groundSet. Use only ones which match fully,
		// to avoid the need to rewrite our imports.
		for _, v := range groundMeat[mark.String()] {
			//TODO: need to disallow conflating ground terms
			//TODO: also need to disallow re-defthm-ing them
			if DEBUG {
				fmt.Fprintf(os.Stderr, "Ground Using %s = %s ",
					v.MarkStr()[len(bone):], v.Fact.Skin.Name)
			}
			newDraft := draft.AddEntry(mark, v)
			if newDraft != nil {
				heap.Push(drafts, newDraft)
				if DEBUG {
					fmt.Fprintf(os.Stderr, "==> %f\n", newDraft.Score)
				}
				if _, ok := newDraft.TopNeed(); !ok {
					return newDraft
				}
			} else {
				if DEBUG {
					fmt.Fprintf(os.Stderr, "==> Nil!\n")
				}
			}
		}
		// Then check proved theorems
		resolved := make(chan *Entry, 100)
		GetFactsByPrefix(db, bone, resolved)

		for e := range resolved {
			if len(e.Fact.Deps()) > 0 {
				if DEBUG {
					fmt.Fprintf(os.Stderr, "Using %s = %s ",
						e.MarkStr()[len(bone):], e.Fact.Skin.Name)
				}
				for _, d := range needers {
					newDraft := d.AddEntry(mark, e)
					if newDraft != nil {
						if _, ok := newDraft.TopNeed(); !ok {
							return newDraft
						}
						//hash := newDraft.Hash()
						if true { //!draftsSeen[hash] {
							//draftsSeen[hash] = true
							if DEBUG {
								fmt.Fprintf(os.Stderr, "==> %f\n",
									newDraft.Score)
							}
							heap.Push(drafts, newDraft)
						} else {
							// TODO: this never seems to happen in practice...
							fmt.Fprintf(os.Stderr, "==> Already Seen!\n")
						}
					} else {
						if DEBUG {
							fmt.Fprintf(os.Stderr, "==> Nil!\n")
						}
					}
				}
			}
		}
		laps += 1
		if laps > maxLaps {
			fmt.Fprintf(os.Stderr, "Too many laps, giving up!")
			return nil
		}
		if laps%100 == 0 {
			fmt.Fprintf(os.Stderr, "Laps: %d, Drafts: %d\n", laps, drafts.Len())
		}
	}
	fmt.Fprintf(os.Stderr, "Out of drafts!")
	return nil
}
func main() {
	dbPath := flag.String("d", "facts.leveldb", "path to facts.leveldb")
	markQuery := flag.String("m", "", "for raw mark-to-json query")
	imports := flag.String("i", "", "comma-separated list of .ghi imports")
	exports := flag.String("e", "", "comma-separated list of .ghi exports")
	prof := flag.Bool("prof", true, "do profiling?")
	laps := flag.Int("l", 8000, "Maximum iterations")
	flag.Parse()
	opt := opt.Options{ErrorIfMissing: true}
	db, err := leveldb.OpenFile(*dbPath, &opt)
	if err != nil {
		fmt.Fprint(os.Stderr, err)
		os.Exit(-1)
	}
	defer db.Close()
	if len(*markQuery) > 0 {
		results := make(chan *Entry)
		go GetFactsByPrefix(db, *markQuery, results)
		fmt.Print("{\n")
		for e := range results {
			fmt.Printf("  %s: %s\n", jsonize(e.Key), e.Json)
		}
		fmt.Print("}\n")
		return
	}
	importList := strings.Split(*imports, ",")
	exportList := strings.Split(*exports, ",")
	groundSet := parseInterfaces(importList)
	targets := parseInterfaces(exportList)
	groundMeat := make(map[string][]*Entry)
	for _, e := range groundSet {
		markStr := e.MarkStr()
		arr := groundMeat[markStr]
		arr = append(arr, e)
		groundMeat[markStr] = arr
	}

	draft := new(Draft)
	for _, e := range targets {
		targetMark := e.Mark()
		if DEBUG {
			fmt.Fprintf(os.Stderr, "Target: %s\n%s\n%s\n%v\n",
				e.Fact.Skin.Name, e.Key, e.Fact, e.Mark())
		}
		draft = draft.AddTarget(targetMark)
	}
	drafts := new(DraftHeap)
	heap.Init(drafts)
	heap.Push(drafts, draft)

	var cpu, heap *os.File
	if *prof {
		cpu, err = os.Create("pprof-cpu.txt")
		if err != nil {
			log.Fatal("Couldn't create pprof.txt! ", err)
		}
		heap, err = os.Create("pprof-heap.txt")
		if err != nil {
			log.Fatal("Couldn't create pprof.txt! ", err)
		}
		pprof.StartCPUProfile(cpu)
	}
	winner := churn(db, groundMeat, drafts, *laps)
	if *prof {
		pprof.StopCPUProfile()
		pprof.WriteHeapProfile(heap)
		cpu.Close()
		heap.Close()
	}
	fmt.Fprintf(os.Stderr, "\nResult: %s\n", winner)
	if winner == nil {
		os.Exit(-1)
	}
	for _, imp := range importList {
		fmt.Printf("import (%s %s () \"\")\n", imp, imp)
	}
	_, err = WriteProofs(os.Stdout, winner.Flatten(), targets, winner.Bind)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(-1)
	}

	for _, exp := range exportList {
		fmt.Printf("export (%s %s () \"\")\n", exp, exp)
	}

	os.Exit(0)
}
