package main

import (
	"encoding/json"
	"fmt"
	"github.com/syndtr/goleveldb/leveldb"
	"github.com/syndtr/goleveldb/leveldb/util"
	"io"
	"os"
	"reflect"
	"strconv"
	"strings"
)

// Either an int (representing a var), or a list whose first term is an int
// (representing a term) and whose other terms are Sexps (representing arguments
// to that term).
type Sexp interface{}

// A list of [Hyps, Stmt, Free].
type Core []interface{}

// TODO: PICKUP
func (this *Mark) Hash() string {
	if len(this.hash) == 0 {
		this.hash = this.list[0][0] + "\x01" +
			strings.Join(this.list[1], "\x00") + "\x01" +
			strings.Join(this.list[2], "\x00")
		if markIndices == nil {
			markIndices = make(map[string]int)
		}
		index, ok := markIndices[this.hash]
		if !ok {
			index = len(markIndices)
			markIndices[this.hash] = index
		}
		this.Index = index
		if index >= MaxMark {
			MaxMark = MaxMark*2 + 400
		}
	}
	return this.hash
}

func (this *Mark) String() string {
	if len(this.flat) == 0 {
		str := this.list[0][0] + ";["
		for j := 1; j < len(this.list); j++ {
			if j > 1 {
				str += ","
			}
			str += "["
			for i, k := range this.list[j] {
				k = strings.Replace(k, "\\", "\\\\", -1)
				k = strings.Replace(k, "\"", "\\\"", -1)
				if i > 0 {
					str += ","
				}
				str += "\"" + k + "\""
			}
			str += "]"
		}
		str += "]"
		this.flat = str
		return str
	} else {
		return this.flat
	}

}

//BoneKey gives the prefix-string to use in a database query for bones like this
//mark.
func (this Mark) BoneKey() string {
	return this.list[0][0]
}

// Rewrite takes two maps to rewrite the terms and kinds of the mark. The bone
// parts are unchanged. If the output would be the same as the input, the input
// is simply returned.
func (this Mark) Rewrite(bind Bind) Mark {
	if memo == nil {
		memo = make(map[MarkBind]Mark)
	}
	keyMarkBind := MarkBind{this.Index, bind.terms, bind.kinds}
	if m, ok := memo[keyMarkBind]; ok {
		return m
	}
	var that Mark
	that.list = make([][]string, 3)
	that.list[0] = make([]string, 1)
	that.list[0][0] = this.list[0][0]
	// TODO: duplicate code in Bind
	mapStuff := func(j int, stuff *Subst) bool {
		workDone := false
		that.list[j] = make([]string, len(this.list[j]))
		for i, oldw := range this.list[j] {
			var ok bool
			that.list[j][i], ok = stuff.Get(oldw)
			if ok {
				workDone = true
			}
		}
		return workDone
	}
	tChange, kChange := true, true
	if bind.terms.Len() == 0 || !mapStuff(1, bind.terms) {
		that.list[1] = this.list[1]
		tChange = false
	}
	if bind.kinds.Len() == 0 || !mapStuff(2, bind.kinds) {
		that.list[2] = this.list[2]
		kChange = false
	}
	if !tChange && !kChange {
		that = this
	}
	// Force precompute these
	that.Hash()
	that.String()
	memo[keyMarkBind] = that
	return that
}

// A fact represents a stmt, thm, or defthm. This struct is designed to be
// unmarshalled into by the json package. Anything that is listed as interface{}
// in this struct is a nested list of strings.
type Fact struct {
	Core     []interface{}
	FreeMaps [][][]int
	Skin     struct {
		Name       string
		License    string
		HypNames   []string
		DepNames   []string
		VarNames   []string
		TermNames  []string
		Delimiters []string
	}
	Tree struct {
		Cmd         string
		Definiendum interface{}
		Deps        [][]interface{}
		Proof       []interface{}
	}
}

func (this *Fact) Deps() []Mark {
	if this.Tree.depMarks == nil {
		this.Tree.depMarks = make([]Mark, len(this.Tree.Deps))
		for i, m := range this.Tree.Deps {
			var mm Mark
			mm.list = m
			// Force precompute these
			mm.Hash()
			mm.String()
			this.Tree.depMarks[i] = mm
		}
	}
	return this.Tree.depMarks
}

// An Entry is a database entry containing a Fact and its Key. The Key is the
// Fact's Mark, optionally followed by ! and a sha1sum.
type Entry struct {
	Key  string
	Fact Fact
	mark *Mark
	Json string
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
	if this.mark == nil {
		m := new(Mark)
		m.list = [][]string{[]string{BonePrefix(this.Key), this.MarkStr()},
			this.Fact.Meat.Terms, this.Fact.Meat.Kinds}
		this.mark = m
		// Force precompute these
		m.Hash()
		m.String()
	}
	return *this.mark
}

var dbCache map[string][]*Entry

func GetFactsByPrefix(db *leveldb.DB, pfix string, out chan<- *Entry) {
	if dbCache == nil {
		dbCache = make(map[string][]*Entry)
	}
	if es, ok := dbCache[pfix]; ok {
		for _, e := range es {
			out <- e
		}
		close(out)
		return
	}
	es := make([]*Entry, 0)
	var rang util.Range
	rang.Start = []byte(pfix)
	rang.Limit = append(rang.Start, byte(0xff))
	iter := db.NewIterator(&rang, nil)
	defer iter.Release()
	found := false
	for iter.Next() {
		key := iter.Key()
		value := iter.Value()
		keyFact := new(Entry)
		keyFact.Key = string(key)
		keyFact.Json = string(value)
		err := json.Unmarshal(value, &keyFact.Fact)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\nPfix:%v\nKey:%s\nValue: %s\n",
				err, pfix, key, value)
			panic("JSON Error")
		} else {
			found = true
			out <- keyFact
			es = append(es, keyFact)
		}
		if DEBUG {
			fmt.Fprintf(os.Stderr, "Found: %s is %s\n", keyFact.Key, keyFact.Fact.Skin.Name)
		}
	}
	if !found {
		fmt.Fprintf(os.Stderr, "Pfix Not Found: %s\n", pfix)
	}
	dbCache[pfix] = es
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
	// Step 1: scan through the list. Set aside axioms. Pull out all var names
	// to predeclare. Rename exports to match interface.
	depNames := make(map[string]string)
	varDecs := make(map[string]map[string]bool)
	tvarDecs := make(map[string]map[string]bool)
	axioms := make([]*Fact, 0)
	rev := make([]*Fact, len(list))
	j := len(list) - 1
	for _, e := range list {
		f := &e.Fact
		mark := e.Mark().Rewrite(bind)
		markStr := mark.String()
		if exp, ok := exports[markStr]; ok {
			f.Skin.Name = exp.Fact.Skin.Name
		}
		depNames[markStr] = f.Skin.Name
		if len(f.Deps()) > 0 {
			rev[j], j = f, j-1
			f.getVarNames(varDecs, tvarDecs, bind)
		} else {
			axioms = append(axioms, f)
			// TODO: use these
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
		for i, mark := range f.Deps() {
			newMark := bind.Rewrite(mark)
			markStr := newMark.String()
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
