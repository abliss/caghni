package main

import (
	"fmt"
	"os"
)

// A Draft is a possible solution-in-progress. For any given entry in the
// entries list, each of its dependencies is either (a) listed later in entries,
// or (b) a ""-valued key in needs. If the score is 0, the Draft is a complete
// solution. The kinds and terms maps give an acyclic, consistent
// reinterpretation of all meat. Each Draft is immutable; any extension creates
// a new Draft. If dependency x is satisfied by entry y, needs[x] = "index of y"
// in entries. Equivalent Drafts will have identical hashes.
type Draft struct {
	haves map[string]*Entry // bonemeat -> entry
	needs map[string]int    // bonemeat -> tier#
	kinds map[string]string // oldKind -> newKind
	terms map[string]string // oldTerm -> newTerm
	hash  string
	Score float64
}

// My kingdom for generics
func cloneMapStringInt(src map[string]int) map[string]int {
	dst := make(map[string]int, len(src))
	for k, v := range src {
		dst[k] = v
	}
	return dst
}
func cloneMapStringPEntry(src map[string]*Entry) map[string]*Entry {
	dst := make(map[string]*Entry, len(src))
	for k, v := range src {
		dst[k] = v
	}
	return dst
}
func cloneMapStringString(src map[string]string) map[string]string {
	dst := make(map[string]string, len(src))
	for k, v := range src {
		dst[k] = v
	}
	return dst
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
	for _, e := range this.haves {
		s += fmt.Sprintf("%s(%d),", e.Fact.Skin.Name,
			this.needs[BoneMeatPrefix(e.Key)])
	}
	return s
}

func (this *Draft) rewriteKey(key string) string {
	if len(this.terms) == 0 && len(this.kinds) == 0 {
		return key
	}
	panic(-2) // TODO
}
func (this *Draft) AddTarget(need string) (that *Draft) {
	return this.addNeed(need, 0, nil)
}
func (this *Draft) addNeed(need string, tier int,
	cycle map[string]bool) (that *Draft) {
	need2 := this.rewriteKey(need)
	if t, ok := this.needs[need]; ok {
		// adding a need already present; elevate tiers if necessary
		if t < tier {
			this.needs[need] = tier
			entry, ok := this.haves[need]
			if !ok {
				return this
			}
			// already have an entry for this need; bump up all deps
			if cycle == nil {
				cycle = make(map[string]bool)
			}
			if _, ok := cycle[need]; ok {
				// Cycle detected; abort
				return nil
			}
			cycle[need] = true
			for _, dep := range entry.Fact.Tree.Deps {
				this = this.addNeed(dep, tier+1, cycle)
				if this == nil {
					return this
				}
			}
		}
		return this
	}
	that = new(Draft)
	that.haves = this.haves
	that.needs = cloneMapStringInt(this.needs)
	that.kinds = this.kinds
	that.terms = this.terms
	that.Score = this.Score
	that.needs[need2] = tier
	that.Score++
	return
}
func (this *Draft) TopNeed() (need string, ok bool) {
	//TODO: use a heap or something instead of scanning
	for k, _ := range this.needs {
		if _, ok = this.haves[k]; !ok {
			return k, true
		}
	}
	return "", false
}

func (this *Draft) AddEntry(need string, entry *Entry) (that *Draft) {
	//var newTerms, newKinds map[string]string
	if _, ok := this.haves[need]; ok {
		// adding an entry already present is an error
		panic(-3)
	}
	if BoneMeatPrefix(entry.Key) != need {
		// TODO: try remapping
		return nil
	}
	that = new(Draft)
	that.haves = cloneMapStringPEntry(this.haves)
	that.kinds = cloneMapStringString(this.kinds)
	that.terms = cloneMapStringString(this.terms)
	that.needs = cloneMapStringInt(this.needs)
	that.Score = this.Score - 1
	/** TODO
	    copyMapStringString(that.kinds, newKinds)
		closeTransMap(that.kinds)
		copyMapStringString(that.terms, newTerms)
		closeTransMap(that.terms)
	**/
	if len(that.terms) > len(this.terms) || len(that.kinds) > len(this.kinds) {
		// TODO: with a reverse index this might go faster
		for k, v := range this.needs {
			k2 := that.rewriteKey(k)
			that.needs[k2] = v
		}
	}
	that.haves[need] = entry
	tier, ok := this.needs[need]
	if !ok {
		// cannot add unneeded entry
		panic(-4)
	}
	for _, dep := range entry.Fact.Tree.Deps {
		that = that.addNeed(dep, tier+1, nil)
		if that == nil {
			return that
		}
	}
	return that
}

// Returns all the entries in appropriate reverse proof-order
func (this *Draft) Flatten() []*Entry {
	tiers := make([][]*Entry, 0)
	for n, tier := range this.needs {
		for len(tiers) <= tier {
			tiers = append(tiers, make([]*Entry, 0))
		}
		e := this.haves[n]
		if e == nil {
			fmt.Fprintf(os.Stderr, "Entry not found: %v -> %v\n", n,
				this.haves[n])
			panic(-5)
		}
		tiers[tier] = append(tiers[tier], this.haves[n])
	}
	out := make([]*Entry, 0)
	for _, t := range tiers {
		out = append(out, t...)
	}
	return out
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
