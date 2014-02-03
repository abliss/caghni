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

	draft := new(Draft)
	for k, _ := range targets {
		draft = draft.AddNeed(k)
	}

	fmt.Fprintf(os.Stderr, "XXXX Score: %f\n", draft.score)

	depMap := make(map[string][]*Entry)
	newOut, _ := compactify(nil, groundSet, depMap)

	for _, imp := range importList {
		fmt.Printf("import (%s %s () \"\")\n", imp, imp)
	}
	_, err = WriteProofs(os.Stdout, newOut[1:], targets)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(-1)
	}

	for _, exp := range exportList {
		fmt.Printf("export (%s %s () \"\")\n", exp, exp)
	}

	os.Exit(0)
}
