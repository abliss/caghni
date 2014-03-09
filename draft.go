package main

import (
	"fmt"
	"sort"
)

type Need struct {
	tier  int
	mark  Mark
	entry *Entry // nil until the need is satisfied
}

// A Draft is a possible solution-in-progress. For any given entry in the
// entries list, each of its dependencies is either (a) listed later in entries,
// or (b) a ""-valued key in needs. If the score is 0, the Draft is a complete
// solution. The kinds and terms maps give an acyclic, consistent
// reinterpretation of all meat. Each Draft is immutable; any extension creates
// a new Draft. If dependency x is satisfied by entry y, needs[x] = "index of y"
// in entries. Equivalent Drafts will have identical hashes.
type Draft struct {
	need  map[string]*Need // key is string(Mark)
	Bind  Bind
	Score float64
}

func (this *Draft) Hash() string {
	out := ""
	for _, n := range this.flatten() {
		out += fmt.Sprintf("%d.%v", n.tier, n.mark)
		if n.entry != nil {
			out += n.entry.Key
		}
	}
	return out
}

func cloneNeed(src map[string]*Need) map[string]*Need {
	dst := make(map[string]*Need, len(src))
	for k, v := range src {
		dst[k] = &Need{v.tier, v.mark, v.entry}
	}
	return dst
}

func (this *Draft) String() string {
	s := ""
	for _, n := range this.need {
		if n.entry != nil {
			s += fmt.Sprintf("%s@%d ", n.entry.Fact.Skin.Name, n.tier)
		}
	}
	s += "_" + this.Bind.String()
	return s
}

func (this *Draft) AddTarget(mark Mark) (that *Draft) {
	return this.addNeed(mark, 0, nil)
}

func copymsb(in map[string]bool) map[string]bool {
	out := make(map[string]bool)
	for k, v := range in {
		out[k] = v
	}
	return out
}

// Mutates: to move existing needs to higher tiers
func (this *Draft) addNeed(mark Mark, tier int,
	cycle map[string]bool) *Draft {
	// TODO: something fishy in here
	mark2 := this.Bind.Rewrite(mark)
	markStr2 := mark2.String()
	if n, ok := this.need[markStr2]; ok {
		// adding a need already present; elevate tiers if necessary
		if n.tier < tier {
			n.tier = tier
			if n.entry == nil {
				// need not satisfied, so no need to elevate more tiers.
				return this
			}
			// already have an entry for this need; bump up all deps
			if _, ok := cycle[markStr2]; ok {
				// Cycle detected; abort
				//fmt.Println("#XXXX Cycle detected: " + markStr2)
				return nil
			}
			cycle = copymsb(cycle)
			cycle[markStr2] = true
			for _, dep := range n.entry.Fact.Tree.Deps {
				dep2 := this.Bind.Rewrite(dep)
				this = this.addNeed(dep2, tier+1, cycle)
				if this == nil {
					/*fmt.Printf("#XXXX Cannot add need %v@%d(%s)\n",
					dep2, tier+1, n.entry.Fact.Skin.Name)*/
					return this
				}
			}
		}
		return this
	}
	// Adding a new need
	that := new(Draft)
	that.need = cloneNeed(this.need)
	that.Bind = this.Bind
	that.Score = this.Score

	that.need[markStr2] = &Need{tier, mark2, nil}
	that.Score++
	return that
}

func (this *Draft) TopNeed() (mark Mark, ok bool) {
	//TODO: use a heap or something instead of scanning
	for _, v := range this.need {
		if v.entry == nil {
			return v.mark, true
		}
	}
	return Mark{}, false
}

func (this *Draft) AddEntry(mark Mark, entry *Entry) (that *Draft) {
	if entry == nil {
		panic("adding nil entry")
	}
	mark = this.Bind.Rewrite(mark)
	markStr := mark.String()
	need, ok := this.need[markStr]
	if !ok {
		panic("adding an unneeded entry " + markStr)
	}
	if need.entry != nil {
		panic("adding a need already satisfied")
	}

	that = new(Draft)
	that.Score = float64(int(this.Score) - 1)
	that.Bind, ok = this.Bind.Bind(mark, entry)
	if !ok {
		//fmt.Println("#XXXX Cannot bind!")
		//TODO: should use comma ok, not nil
		return nil
	}
	delta := this.Bind.LessThan(that.Bind)
	if delta > 0 {
		// TODO: with a reverse index this might go faster
		that.need = make(map[string]*Need, len(this.need))
		for _, v := range this.need {
			m2 := that.Bind.Rewrite(v.mark)
			that.need[m2.String()] = &Need{v.tier, m2, v.entry}
		}
	} else {
		that.need = cloneNeed(this.need)
	}
	newNeed := that.need[that.Bind.Rewrite(mark).String()]
	newNeed.entry = entry
	for i, dep := range entry.Fact.Tree.Deps {
		that = that.addNeed(dep, need.tier+1, nil)
		if that == nil {
			_ = i
			//fmt.Printf("#XXXX Cannot add need %s=%v\n", entry.Fact.Skin.DepNames[i], dep.String())
			return nil
		}
	}
	that.Score += float64(delta) / 10.0
	return that
}

func (this *Draft) Flatten() []*Entry {
	needs := this.flatten()
	es := make([]*Entry, len(needs))
	for i, need := range needs {
		if need.entry == nil {
			panic("Entry not found: " + need.mark.String())
		}
		es[i] = need.entry
	}
	return es
}

// Returns all the entries in appropriate reverse proof-order
func (this *Draft) flatten() []*Need {
	tiers := make([][]*Need, 0)
	for _, need := range this.need {
		for len(tiers) <= need.tier {
			tiers = append(tiers, make([]*Need, 0))
		}
		tiers[need.tier] = append(tiers[need.tier], need)
	}
	out := make([]*Need, 0)
	for _, t := range tiers {
		sort.Sort(ByMark(t))
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

type ByMark []*Need

func (a ByMark) Len() int      { return len(a) }
func (a ByMark) Swap(i, j int) { a[i], a[j] = a[j], a[i] }
func (a ByMark) Less(i, j int) bool {
	if a[i].entry == nil {
		if a[j].entry == nil {
			return a[i].mark.String() < a[j].mark.String()
		} else {
			return true
		}
	}
	if a[j].entry == nil {
		return false
	}
	return a[i].entry.Key < a[j].entry.Key
}
