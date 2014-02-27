package main

import (
	"fmt"
)

type Bind struct {
	terms Subst
	kinds Subst
}

// RewriteMark takes a Mark from some fact's Deps array and returns a new
// bonemeat after mapping its bound terms and kinds.
func (this Bind) Rewrite(mark Mark) Mark {
	return mark.Rewrite(this.terms, this.kinds)
}

// Given the original bonemeat need and the new bonemeat, write the mapping.
func (this Bind) Bind(mark Mark, entry *Entry) (out Bind, ok bool) {
	newMark := this.Rewrite(entry.Mark())
	that := Bind{this.terms, this.kinds}
	workDone := false
	mapStuff := func(w int, s Subst) (out Subst, ok bool) {
		out, ok = s, true
		for i, x := range mark[w] {
			if newMark[w][i] != x {
				out, ok = out.Put(x, newMark[w][i])
				if !ok {
					return out, false
				}
				workDone = true
			}
		}
		return out, true
	}
	that.terms, ok = mapStuff(1, this.terms)
	if !ok {
		return this, false
	}
	that.kinds, ok = mapStuff(2, this.kinds)
	if !ok {
		return this, false
	}
	if workDone {
		return that, true
	} else {
		return this, true
	}
}

func (this Bind) Term(term string) string {
	t, _ := this.terms.Get(term)
	return t
}
func (this Bind) Kind(kind string) string {
	k, _ := this.kinds.Get(kind)
	return k
}

func (this Bind) LessThan(that Bind) bool {
	return len(that.terms) > len(this.terms) ||
		len(that.kinds) > len(this.kinds)
}

func (this Bind) String() string {
	return fmt.Sprintf("{%v;%v}", this.terms, this.kinds)
}

// TODO: need something like this
// shortcuts the transitive closure the map. panics if any cycle is detected.
func closeTransMap(m map[string]string) {
	for cont := 0; cont < 2; cont++ {
		for k, v := range m {
			if j, ok := m[v]; ok {
				if j == k {
					panic(-1)
				}
				m[k] = j
				cont = 0
			}
		}
	}
}
