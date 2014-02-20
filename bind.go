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

func (this *Bind) RewriteKey(key string) string {
	if this == nil {
		return key
	}
	if len(this.terms) == 0 && len(this.kinds) == 0 {
		return key
	}
	out := BonePrefix(key) + ","
	meat := parseMeat(key)
	for i, t := range meat[0] {
		if t2, ok := this.terms[t]; ok {
			meat[0][i] = t2
		}
	}
	for i, k := range meat[1] {
		if k2, ok := this.kinds[k]; ok {
			meat[1][i] = k2
		}
	}
	kt := []string{bracketize(meat[0]), bracketize(meat[1])}
	out += bracketize(kt) + "]"
	return out
}

// Given the original bonemeat need and the new bonemeat, write the mapping.
func (this *Bind) Bind(in, out string) *Bind {
	if in == out {
		return this
	}
	that := new(Bind)
	if this == nil {
		that.terms = make(map[string]string)
		that.kinds = make(map[string]string)
	} else {
		that.terms = cloneMapStringString(this.terms)
		that.kinds = cloneMapStringString(this.kinds)
	}
	// TODO: this is unsafe if terms/kinds can contain [,] chars
	mapStuff := func(a, b [][]string, w int, m map[string]string) {
		for i, x := range b[w] {
			if a[w][i] != x {
				m[x] = a[w][i]
			}
		}
	}
	ins := parseMeat(in)
	outs := parseMeat(out)
	mapStuff(ins, outs, 0, that.terms)
	mapStuff(ins, outs, 1, that.kinds)
	return that
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
