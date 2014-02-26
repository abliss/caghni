package main

type Bind struct {
	terms map[string]string
	kinds map[string]string
}

func cloneMapStringString(src map[string]string) map[string]string {
	dst := make(map[string]string, len(src))
	for k, v := range src {
		dst[k] = v
	}
	return dst
}

// RewriteMark takes a Mark from some fact's Deps array and returns a new
// bonemeat after mapping its bound terms and kinds.
func (this *Bind) Rewrite(mark Mark) Mark {
	if this == nil {
		return mark
	}
	return mark.Rewrite(this.terms, this.kinds)
}

// Given the original bonemeat need and the new bonemeat, write the mapping.
func (this *Bind) Bind(mark Mark, entry *Entry) *Bind {
	newMark := this.Rewrite(entry.Mark())
	that := new(Bind)
	if this == nil {
		that.terms = make(map[string]string)
		that.kinds = make(map[string]string)
	} else {
		that.terms = cloneMapStringString(this.terms)
		that.kinds = cloneMapStringString(this.kinds)
	}
	workDone := false
	mapStuff := func(w int, m map[string]string) {
		for i, x := range mark[w] {
			if newMark[w][i] != x {
				m[x] = newMark[w][i]
				workDone = true
			}
		}
	}
	mapStuff(0, that.terms)
	mapStuff(1, that.kinds)
	if workDone {
		return that
	} else {
		return this
	}
}

func (this *Bind) Term(term string) string {
	if this == nil {
		return term
	}
	t, ok := this.terms[term]
	if !ok {
		return term
	}
	return t
}
func (this *Bind) Kind(kind string) string {
	if this == nil {
		return kind
	}
	k, ok := this.kinds[kind]
	if !ok {
		return kind
	}
	return k
}

func (this *Bind) LessThan(that *Bind) bool {
	if that == nil {
		return false
	}
	if this == nil {
		return true
	}
	return len(that.terms) > len(this.terms) ||
		len(that.kinds) > len(this.kinds)
}

func (this *Bind) String() string {
	if this == nil {
		return "{}"
	}
	s := "{"
	for k, v := range this.terms {
		s += k + "->" + v + ","
	}
	s += "};{"
	for k, v := range this.kinds {
		s += k + "->" + v + ","
	}
	return s + "}"
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
