package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"github.com/syndtr/goleveldb/leveldb"
	"io"
	"os"
	"reflect"
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
		if DEBUG {
			fmt.Fprintf(os.Stderr, "Found: %s is %s\n", keyFact.Key, keyFact.Fact.Skin.Name)
		}
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

// makes a ghilbert-parsable string from a parsed-json sexp
func (this *Fact) sexpToString(sexp interface{}) string {
	if s, ok := sexp.(string); ok {
		return s
	} else if s, ok := sexp.(float64); ok {
		return fmt.Sprintf("%d", int(s))
	} else {
		v := reflect.ValueOf(sexp)
		l := v.Len()
		out := "("
		for i := 0; i < l; i++ {
			if i > 0 {
				out += " "
			}
			out += this.sexpToString(v.Index(i).Interface())
		}
		out += ")"
		return out
	}
}

func WriteProof(out io.Writer, list []*Entry) (n int, err error) {
	lookup := make(map[string]*Entry)
	rev := make([]*Fact, 0, len(list))
	for _, e := range list {
		kSexp := e.Key[0:scan_sexp(e.Key, 0)]
		lookup[kSexp] = e
		if len(e.Fact.Tree.Deps) > 0 {
			rev = append(rev, &e.Fact)
		}
	}
	write := func(s string) {
		nn, err := io.WriteString(out, s)
		if err != nil {
			panic(err)
		}
		n += nn
	}
	for _, f := range rev {
		write("thm (")
		write(f.Skin.Name)
		write(" ")
		write(f.sexpToString(f.Bone.Free))
		write("\n   ")
		write(f.sexpToString(f.Bone.Hyps))
		write("\n   ")
		write(f.sexpToString(f.Bone.Stmt))
		write("\n")
		write("#TODO\n)\n")
	}
	return
}
