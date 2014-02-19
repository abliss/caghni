package main

import (
	"container/heap"
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
			out[BoneMeatPrefix(axiom.Key)] = axiom
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
	laps := 0
	for len(*drafts) > 0 {
		draft := heap.Pop(drafts).(*Draft)
		need, _ := draft.TopNeed()
		bone := BonePrefix(need)
		needers := make([]*Draft, 1)
		needers[0] = draft
		fmt.Fprintf(os.Stderr, "%s (%f) needs %v\n", draft, draft.Score, need)

		// First check axioms in the groundSet
		for _, v := range groundBones[bone] {
			newDraft := draft.AddEntry(need, v)
			if newDraft != nil {
				heap.Push(drafts, newDraft)
			}
		}
		// Then check proved theorems
		resolved := make(chan *Entry, 10)
		go GetFactsByPrefix(db, BonePrefix(need), resolved)

		for e := range resolved {
			if len(e.Fact.Tree.Deps) > 0 {
				fmt.Fprintf(os.Stderr, "%s = %s, ",
					BoneMeatPrefix(e.Key)[len(bone):], e.Fact.Skin.Name)
				for _, d := range needers {
					newDraft := d.AddEntry(need, e)
					if newDraft != nil {
						if _, ok := newDraft.TopNeed(); !ok {
							fmt.Fprintf(os.Stderr, "Needless Draft! %v\n",
								draft)
							return newDraft
						}
						heap.Push(drafts, newDraft)
					}
				}
			}
		}
		laps += 1
		if laps > 40 {
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
	for k, _ := range targets {
		draft = draft.AddTarget(BoneMeatPrefix(k))
	}
	drafts := new(DraftHeap)
	heap.Init(drafts)
	heap.Push(drafts, draft)

	winner := churn(db, groundBones, drafts)
	fmt.Fprintf(os.Stderr, "\nResult: %s\n", winner)

	for _, imp := range importList {
		fmt.Printf("import (%s %s () \"\")\n", imp, imp)
	}
	_, err = WriteProofs(os.Stdout, winner.Flatten(), targets)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(-1)
	}

	for _, exp := range exportList {
		fmt.Printf("export (%s %s () \"\")\n", exp, exp)
	}

	os.Exit(0)
}
