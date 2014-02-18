package main

// A Draft is a possible solution-in-progress. For any given entry in the
// entries list, each of its dependencies is either (a) listed later in entries,
// or (b) a ""-valued key in needs. If the score is 0, the Draft is a complete
// solution. The kinds and terms maps give an acyclic, consistent
// reinterpretation of all meat. Each Draft is immutable; any extension creates
// a new Draft. If dependency x is satisfied by entry y, needs[x] = "index of y"
// in entries. Equivalent Drafts will have identical hashes.
type Draft struct {
	Entries []*Entry
	needs   map[string]string // would be int, if golang had generics
	kinds   map[string]string
	terms   map[string]string
	hash    string
	Score   float64
}

func copyMapStringString(dst, src map[string]string) {
	for k, v := range src {
		dst[k] = v
	}
}

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

func (this *Draft) Hash() string {
	return "todo"
}

func (this *Draft) String() string {
	s := ""
	for _, e := range this.Entries {
		s += e.Fact.Skin.Name + ","
	}
	return s
}

func (this *Draft) rewriteKey(key string) string {
	if len(this.terms) == 0 && len(this.kinds) == 0 {
		return key
	}
	panic(-2) // TODO
}
func (this *Draft) AddNeed(need string) (that *Draft) {
	need2 := this.rewriteKey(need)
	if _, ok := this.needs[need]; ok {
		// adding a need already present: no-op.
		return this
	}
	that = &Draft{
		this.Entries,
		make(map[string]string, len(this.needs)+1),
		this.kinds,
		this.terms,
		"",
		this.Score,
	}
	copyMapStringString(that.needs, this.needs)
	that.needs[need2] = ""
	that.Score++
	return
}
func (this *Draft) TopNeed() (need string, ok bool) {
	//TODO: use a heap or something instead of scanning
	for k, v := range this.needs {
		if len(v) == 0 {
			return k, true
		}
	}
	return "", false
}

func (this *Draft) AddEntry(need string, entry *Entry) (that *Draft) {
	var newTerms, newKinds map[string]string
	if val, ok := this.needs[need]; ok && len(val) > 0 {
		// adding an entry already present is an error
		panic(-3)
	}
	if BoneMeatPrefix(entry.Key) != need {
		// TODO: try remapping
		return nil
	}
	that = new(Draft)
	that.Entries = make([]*Entry, len(this.Entries)+1)
	that.kinds = make(map[string]string, len(this.kinds))
	that.terms = make(map[string]string, len(this.terms))
	that.needs = make(map[string]string, len(this.needs))
	that.Score = this.Score - 1
	copy(that.Entries, this.Entries)
	copyMapStringString(that.kinds, this.kinds)
	copyMapStringString(that.kinds, newKinds)
	closeTransMap(that.kinds)
	copyMapStringString(that.terms, this.terms)
	copyMapStringString(that.terms, newTerms)
	closeTransMap(that.terms)

	if len(that.terms) > len(this.terms) || len(that.kinds) > len(this.kinds) {
		// TODO: with a reverse index this might go faster
		for k, v := range this.needs {
			k2 := that.rewriteKey(k)
			that.needs[k2] = v
		}
	} else {
		copyMapStringString(that.needs, this.needs)
	}
	that.Entries[len(this.Entries)] = entry
	that.needs[need] = entry.Key
	for _, dep := range entry.Fact.Tree.Deps {
		that = that.AddNeed(dep)
	}
	return that
}

func (this *Draft) Needs(need string) bool {
	n, ok := this.needs[need]
	return ok && len(n) == 0
}

type DraftHeap []*Draft

func (h DraftHeap) Len() int           { return len(h) }
func (h DraftHeap) Less(i, j int) bool { return h[i].Score < h[j].Score }
func (h DraftHeap) Swap(i, j int)      { h[i], h[j] = h[j], h[i] }
func (h *DraftHeap) Push(x interface{}) {
	// Push and Pop use pointer receivers because they modify the slice's length,
	// not just its contents.
	*h = append(*h, x.(*Draft))
}

func (h *DraftHeap) Pop() interface{} {
	old := *h
	n := len(old)
	x := old[n-1]
	*h = old[0 : n-1]
	return x
}
