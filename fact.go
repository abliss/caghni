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

// A Mark is a JSON-unmarshalable, structure that specifes the bone and meat of
// a fact. The format is [[boneStr], terms, kinds]. The boneStr is a
// JSON-flattened nested-string-array with the quotes removed (the nodes of
// this tree cannot contain commas or brackets). Best not to try to interact
// with a Mark's contents directly; use the methods.  Marks should be considered
// immutable.
type Mark [][]string

func (this Mark) String() string {
	// TODO: this might be faster manually since we know the format.
	return jsonize(this)
}

//BoneKey gives the prefix-string to use in a database query for bones like this
//mark.
func (this Mark) BoneKey() string {
	return this[0][0]
}

// Rewrite takes two maps to rewrite the terms and kinds of the mark. The bone
// parts are unchanged. If the output would be the same as the input, the input
// is simply returned.
func (this Mark) Rewrite(terms, kinds Subst) Mark {
	that := make([][]string, 3)
	that[0] = this[0]
	mapStuff := func(j int, stuff Subst) bool {
		workDone := false
		that[j] = make([]string, len(this[j]))
		for i, oldw := range this[j] {
			var ok bool
			that[j][i], ok = stuff.Get(oldw)
			if ok {
				workDone = true
			}
		}
		return workDone
	}
	tChange, kChange := true, true
	if terms == nil || !mapStuff(1, terms) {
		that[1] = this[1]
		tChange = false
	}
	if kinds == nil || !mapStuff(2, kinds) {
		that[2] = this[2]
		kChange = false
	}
	if !tChange && !kChange {
		return this
	}
	return that
}

// A fact represents a stmt, thm, or defthm. This struct is designed to be
// unmarshalled into by the json package. Anything that is listed as interface{}
// in this struct is a nested list of strings.
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
		Deps  []Mark
		Proof []interface{}
		Dkind int
		Dsig  []interface{}
		Terms []string
		Kinds []string
	}
}

// An Entry is a database entry containing a Fact and its Key. The Key is the
// Fact's Mark, optionally followed by ! and a sha1sum.
type Entry struct {
	Key  string
	Fact Fact
}

// BonePrefix returns that prefix of a Key or MarkStr which only pertains to the fact's Bone,
// not its Meat.
func BonePrefix(key string) string {
	return key[0:strings.Index(key, ";")]
}

// MarkStr returns that prefix of an entry's Key which only pertains to the fact's Bone and Meat, not its sha1.
func (this *Entry) MarkStr() string {
	return this.Key[0:strings.LastIndex(this.Key, ";")]
}

func (this *Entry) Mark() Mark {
	return Mark{[]string{BonePrefix(this.Key)},
		this.Fact.Meat.Terms, this.Fact.Meat.Kinds}
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
			fmt.Fprintf(os.Stderr, "Error: %v\nPfix:%v\nKey:%s\nValue: %s\n",
				err, pfix, key, value)
			panic("JSON Error")
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

// makes a ghilbert-parsable string from a parsed-json sexp
func (this *Fact) sexpToString(sexp interface{}, bind Bind) string {
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
		return bind.Term(this.Tree.Terms[int(s)])
	} else {
		v := reflect.ValueOf(sexp)
		l := v.Len()
		out := "("
		for i := 0; i < l; i++ {
			if i > 0 {
				out += " "
			}
			out += this.sexpToString(v.Index(i).Interface(), bind)
		}
		out += ")"
		return out
	}
}

// Extract the vars and tvars used in this fact into the given maps.
func (this *Fact) getVarNames(varDecs, tvarDecs map[string]map[string]bool,
	bind Bind) {
	for ki, vs := range this.Skin.V {
		if len(vs) == 0 {
			continue
		}
		kind := bind.Kind(this.Tree.Kinds[ki])
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
		kind := bind.Kind(this.Tree.Kinds[ki])
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

func WriteProofs(out io.Writer, list []*Entry, exports map[string]*Entry,
	bind Bind) (n int, err error) {
	// Step 1: scan through the list. Discard axioms and reverse the rest. Pull
	// out all var names to predeclare. Rename exports to match interface.
	depNames := make(map[string]string)
	varDecs := make(map[string]map[string]bool)
	tvarDecs := make(map[string]map[string]bool)
	rev := make([]*Fact, len(list))
	j := len(list) - 1
	for _, e := range list {
		f := e.Fact
		mark := bind.Rewrite(e.Mark())
		markStr := mark.String()
		fmt.Fprintf(os.Stderr, "XXXX: %v\n      %v\n", e.Key, mark)
		if exp, ok := exports[markStr]; ok {
			f.Skin.Name = exp.Fact.Skin.Name
		}
		depNames[markStr] = f.Skin.Name
		if len(f.Tree.Deps) > 0 {
			rev[j], j = &f, j-1
			f.getVarNames(varDecs, tvarDecs, bind)
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
		for i, mark := range f.Tree.Deps {
			newMark := bind.Rewrite(mark)
			markStr := newMark.String()
			fmt.Fprintf(os.Stderr, "XXXX: %v\n      %v\n", mark, newMark)
			newDep, ok := depNames[markStr]
			if !ok {
				panic("Can't find dep for " + markStr)
			}
			// TODO: oughtn't mutate
			f.Skin.DepNames[i] = newDep
		}
		if f.Tree.Dsig != nil {
			write("def")
		}
		write("thm (")
		write(f.Skin.Name)
		write(" ")
		if f.Tree.Dsig != nil {
			write(bind.Kind(f.Tree.Kinds[f.Tree.Dkind]))
			write(" ")
			write(f.sexpToString(f.Tree.Dsig, bind))
			write(" ")
		}
		write(f.sexpToString(f.Bone.Free, bind))
		write("\n   (")
		for i, s := range f.Bone.Hyps {
			write(f.Skin.HypNames[i])
			write(" ")
			write(f.sexpToString(s, bind))
			write("\n   ")
		}
		write(")\n   ")
		write(f.sexpToString(f.Bone.Stmt, bind))
		write("\n")
		for _, s := range f.Tree.Proof {
			write(f.sexpToString(s, bind))
			write("  ")
		}
		write("\n)\n\n")
	}
	return
}
