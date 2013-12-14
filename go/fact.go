package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"github.com/syndtr/goleveldb/leveldb"
	"io"
	"os"
	"reflect"
	"strconv"
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
		Terms []string
		Kinds []string
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
		fields := strings.Split(s, ".")
		if len(fields) != 2 {
			panic("Bad var string fields " + s)
		}
		num, err := strconv.Atoi(fields[1])
		if err != nil {
			panic("Bad num " + s)
		}
		switch fields[0] {
		case "Deps":
			return this.Skin.DepNames[num]
		case "Hyps":
			return this.Skin.HypNames[num]
		default: // TN or VN
			var names [][]string
			switch fields[0][0] {
			case 'T':
				names = this.Skin.T
			case 'V':
				names = this.Skin.V
			default:
				panic("Bad var string " + s)
			}
			kindNum, err := strconv.Atoi(fields[0][1:])
			if err != nil {
				panic("Bad var kind num " + s)
			}
			return names[kindNum][num]
		}
	} else if s, ok := sexp.(float64); ok {
		return this.Tree.Terms[int(s)]
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

// Extract the vars and tvars used in this fact into the given maps.
func (this *Fact) getVarNames(varDecs, tvarDecs map[string]map[string]bool) {
	for ki, vs := range this.Skin.V {
		if len(vs) == 0 {
			continue
		}
		kind := this.Tree.Kinds[ki]
		vd, ok := varDecs[kind]
		if !ok {
			vd = make(map[string]bool)
			varDecs[kind] = vd
		}
		for _, v := range vs {
			vd[v] = true
		}
	}
	for ki, vs := range this.Skin.T {
		if len(vs) == 0 {
			continue
		}
		kind := this.Tree.Kinds[ki]
		vd, ok := tvarDecs[kind]
		if !ok {
			vd = make(map[string]bool)
			tvarDecs[kind] = vd
		}
		for _, v := range vs {
			vd[v] = true
		}
	}
}

func WriteProofs(out io.Writer, list []*Entry) (n int, err error) {
	// Step 1: scan through the list. Discard axioms and reverse the rest. Pull
	// out all var names to predeclare.
	depNames := make(map[string]string)
	varDecs := make(map[string]map[string]bool)
	tvarDecs := make(map[string]map[string]bool)
	rev := make([]*Fact, len(list))
	j := len(list) - 1
	for _, e := range list {
		f := e.Fact
		kSexp := e.Key[0:scan_sexp(e.Key, 0)]
		depNames[kSexp] = f.Skin.Name
		if len(f.Tree.Deps) > 0 {
			rev[j], j = &f, j-1
			f.getVarNames(varDecs, tvarDecs)
		}
	}
	rev = rev[j+1:]
	write := func(s string) {
		nn, err := io.WriteString(out, s)
		if err != nil {
			panic(err)
		}
		n += nn
	}
	// Step 2: write var and tvar decs for each kind
	for k, vs := range varDecs {
		write("var (")
		write(k)
		write(" ")
		for v := range vs {
			write(v)
			write(" ")
		}
		write(")\n")
	}
	for k, vs := range tvarDecs {
		write("tvar (")
		write(k)
		write(" ")
		for v := range vs {
			write(v)
			write(" ")
		}
		write(")\n")
	}

	// Step 3: write each of the proofs.
	for _, f := range rev {
		for i, d := range f.Tree.Deps {
			newDep, ok := depNames[d]
			if !ok {
				panic("Can't find dep for " + d)
			}
			f.Skin.DepNames[i] = newDep
		}
		if f.Tree.Dsig != nil {
			write("def")
		}
		write("thm (")
		write(f.Skin.Name)
		write(" ")
		if f.Tree.Dsig != nil {
			write(f.Tree.Kinds[f.Tree.Dkind])
			write(" ")
			write(f.sexpToString(f.Tree.Dsig))
			write(" ")
		}
		write(f.sexpToString(f.Bone.Free))
		write("\n   (")
		for i, s := range f.Bone.Hyps {
			write(f.Skin.HypNames[i])
			write(" ")
			write(f.sexpToString(s))
			write("\n   ")
		}
		write(")\n   ")
		write(f.sexpToString(f.Bone.Stmt))
		write("\n")
		for _, s := range f.Tree.Proof {
			write(f.sexpToString(s))
			write("  ")
		}
		write("\n)\n\n")
	}
	return
}
