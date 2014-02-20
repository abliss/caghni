package main

import (
	"fmt"
	"os"
	"strings"
)

// A Draft is a possible solution-in-progress. For any given entry in the
// entries list, each of its dependencies is either (a) listed later in entries,
// or (b) a ""-valued key in needs. If the score is 0, the Draft is a complete
// solution. The kinds and terms maps give an acyclic, consistent
// reinterpretation of all meat. Each Draft is immutable; any extension creates
// a new Draft. If dependency x is satisfied by entry y, needs[x] = "index of y"
// in entries. Equivalent Drafts will have identical hashes.
type Draft struct {
	have  map[string]*Entry // bonemeat -> entry
	need  map[string]int    // bonemeat -> tier#
	Bind  *Bind
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

func (this *Draft) Hash() string {
	return "todo"
}

func (this *Draft) String() string {
	s := ""
	for _, e := range this.have {
		s += fmt.Sprintf("%s(%d),", e.Fact.Skin.Name,
			this.need[BoneMeatPrefix(e.Key)])
	}
	return s
}

func (this *Draft) AddTarget(need string) (that *Draft) {
	return this.addNeed(need, 0, nil)
}

// Mutates: to move existing needs to higher tiers
func (this *Draft) addNeed(need string, tier int,
	cycle map[string]bool) (that *Draft) {
	need2 := this.Bind.RewriteKey(need)
	if t, ok := this.need[need]; ok {
		// adding a need already present; elevate tiers if necessary
		if t < tier {
			this.need[need] = tier
			entry, ok := this.have[need]
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
	that.have = this.have
	that.need = cloneMapStringInt(this.need)
	that.Bind = this.Bind
	that.Score = this.Score
	that.need[need2] = tier
	that.Score++
	return
}
func (this *Draft) TopNeed() (need string, ok bool) {
	//TODO: use a heap or something instead of scanning
	for k, _ := range this.need {
		if _, ok = this.have[k]; !ok {
			return k, true
		}
	}
	return "", false
}

func parseMeat(key string) [][]string {
	meat := key[len(BonePrefix(key))+1 : len(BoneMeatPrefix(key))-1]
	tk := strings.Split(meat[2:len(meat)-2], "],[")
	out := make([][]string, 2)
	out[0] = strings.Split(tk[0], ",")
	out[1] = strings.Split(tk[1], ",")
	return out
}

func (this *Draft) AddEntry(need string, entry *Entry) (that *Draft) {
	//var newTerms, newKinds map[string]string
	if _, ok := this.have[need]; ok {
		// adding an entry already present is an error
		panic(-3)
	}
	that = new(Draft)
	that.have = cloneMapStringPEntry(this.have)
	that.Score = this.Score - 1
	need2 := this.Bind.RewriteKey(BoneMeatPrefix(entry.Key))
	that.Bind = this.Bind.Bind(need, need2)
	if that == nil {
		return nil
	}
	if this.Bind.LessThan(that.Bind) {
		// TODO: with a reverse index this might go faster
		that.need = make(map[string]int, len(this.need))
		for k, v := range this.need {
			k2 := that.Bind.RewriteKey(k)
			that.need[k2] = v
		}
	} else {
		that.need = cloneMapStringInt(this.need)
	}
	that.have[need] = entry
	tier, ok := this.need[need]
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
	for n, tier := range this.need {
		for len(tiers) <= tier {
			tiers = append(tiers, make([]*Entry, 0))
		}
		e := this.have[n]
		if e == nil {
			fmt.Fprintf(os.Stderr, "Entry not found: %v -> %v\n", n,
				this.have[n])
			panic(-5)
		}
		tiers[tier] = append(tiers[tier], this.have[n])
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
