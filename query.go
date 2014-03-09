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

func churn(db *leveldb.DB, groundBones map[string][]*Entry,
	drafts *DraftHeap) *Draft {
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
		fmt.Fprintf(os.Stderr, "%s (%f) needs %v\n", draft, draft.Score,
			mark)

		// First check axioms in the groundSet
		for _, v := range groundBones[bone] {
			//TODO:PICKUP: need to disallow conflating ground terms
			fmt.Fprintf(os.Stderr, "Ground Using %s = %s ",
				v.MarkStr()[len(bone):], v.Fact.Skin.Name)
			newDraft := draft.AddEntry(mark, v)
			if newDraft != nil {
				heap.Push(drafts, newDraft)
				fmt.Fprintf(os.Stderr, "==> %f\n", newDraft.Score)
			} else {
				fmt.Fprintf(os.Stderr, "==> Nil!\n")
			}
		}
		// Then check proved theorems
		resolved := make(chan *Entry, 100)
		GetFactsByPrefix(db, bone, resolved)

		for e := range resolved {
			if len(e.Fact.Tree.Deps) > 0 {
				fmt.Fprintf(os.Stderr, "Using %s = %s ",
					e.MarkStr()[len(bone):], e.Fact.Skin.Name)
				for _, d := range needers {
					newDraft := d.AddEntry(mark, e)
					if newDraft != nil {
						if _, ok := newDraft.TopNeed(); !ok {
							fmt.Fprintf(os.Stderr, "Needless Draft! %v\n",
								draft)
							return newDraft
						}
						//hash := newDraft.Hash()
						if true { //!draftsSeen[hash] {
							//draftsSeen[hash] = true
							fmt.Fprintf(os.Stderr, "==> %f\n", newDraft.Score)
							heap.Push(drafts, newDraft)
						}
					} else {
						fmt.Fprintf(os.Stderr, "==> Nil!\n")
					}
				}
			}
		}
		laps += 1
		if laps > 800 {
			fmt.Fprintf(os.Stderr, "Too many laps, giving up!")
			return nil
		}
		fmt.Fprintf(os.Stderr, "\nDrafts length: %d\n", drafts.Len())
	}
	fmt.Fprintf(os.Stderr, "Out of drafts!")
	return nil
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
	importList := strings.Split(*imports, ",")
	exportList := strings.Split(*exports, ",")
	groundSet := parseInterfaces(importList)
	targets := parseInterfaces(exportList)
	groundBones := make(map[string][]*Entry)
	for k, e := range groundSet {
		arr := groundBones[BonePrefix(k)]
		arr = append(arr, e)
		groundBones[BonePrefix(k)] = arr
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

	f, err := os.Create("pprof.txt")
	if err != nil {
		log.Fatal("Couldn't create pprof.txt! ", err)
	}
	pprof.StartCPUProfile(f)
	winner := churn(db, groundBones, drafts)
	pprof.StopCPUProfile()

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
