package main

import (
	"fmt"
	"sort"
)

// A Draft is a possible solution-in-progress. For any given entry in the
// entries list, each of its dependencies is either (a) listed later in entries,
// or (b) a ""-valued key in needs. If the score is 0, the Draft is a complete
// solution. The kinds and terms maps give an acyclic, consistent
// reinterpretation of all meat. Each Draft is immutable; any extension creates
// a new Draft. If dependency x is satisfied by entry y, needs[x] = "index of y"
// in entries. Equivalent Drafts will have identical hashes.
type Draft struct {
	need  NeedMap // key is string(Mark)
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

func (this *Draft) String() string {
	s := ""
	for _, n := range this.need.All() {
		if n.entry != nil {
			s += fmt.Sprintf("%s@%d ", n.entry.Fact.Skin.Name, n.tier)
		}
	}
	s += "_" + this.Bind.String()
	return s
}

func (this *Draft) AddTarget(mark Mark) (that *Draft) {
	return this.addNeed(mark, 0)
}

// map[mark]bool
type Cycle struct {
	a []bool
}

func (this *Cycle) Put(m Mark) {
	if len(this.a) <= m.Index {
		newA := make([]bool, m.Index+1)
		copy(newA, this.a)
		this.a = newA
	}
	this.a[m.Index] = true
}
func (this Cycle) Has(m Mark) bool {
	if len(this.a) <= m.Index {
		return false
	}
	return this.a[m.Index]
}
func (this Cycle) Copy() Cycle {
	var that Cycle
	that.a = make([]bool, len(this.a))
	copy(that.a, this.a)
	return that
}

func (this *Draft) addNeed(mark Mark, tier int) *Draft {
	var cycle Cycle
	return this.addNeedR(mark, tier, cycle)
}

// Mutates: to move existing needs to higher tiers
func (this *Draft) addNeedR(mark Mark, tier int, cycle Cycle) *Draft {
	// TODO: something fishy in here
	mark2 := mark.Rewrite(this.Bind)
	if n, ok := this.need.Get(mark2); ok {
		// adding a need already present; elevate tiers if necessary
		if n.tier < tier {
			this.need.SetTier(mark2, tier)
			if n.entry == nil {
				// need not satisfied, so no need to elevate more tiers.
				return this
			}
			// already have an entry for this need; bump up all deps
			if cycle.Has(mark2) {
				// Cycle detected; abort
				//fmt.Println("#XXXX Cycle detected: " + markStr2)
				return nil
			}
			cycle := cycle.Copy()
			cycle.Put(mark2)
			for _, dep := range n.entry.Fact.Deps() {
				dep2 := this.Bind.Rewrite(dep)
				this = this.addNeedR(dep2, tier+1, cycle)
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
	that.need = this.need.Copy()
	that.Bind = this.Bind
	that.Score = this.Score

	that.need.Put(mark2, Need{tier, mark2, nil})
	that.Score++
	return that
}

func (this *Draft) TopNeed() (mark Mark, ok bool) {
	//TODO: use a heap or something instead of scanning
	return this.need.TopMark()
}

func (this *Draft) AddEntry(mark Mark, entry *Entry) (that *Draft) {
	if entry == nil {
		panic("adding nil entry")
	}
	mark = this.Bind.Rewrite(mark)
	need, ok := this.need.Get(mark)
	if !ok {
		panic("adding an unneeded entry " + mark.String())
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
		that.need = this.need.Rewrite(that.Bind)
	} else {
		that.need = this.need.Copy()
	}

	that.need.SetEntry(that.Bind.Rewrite(mark), entry)
	for i, dep := range entry.Fact.Deps() {
		that = that.addNeed(dep, need.tier+1)
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

// Returns all the entries in appropriate reverse proof-order.  Within a tier,
// entries are sorted alphabetically by mark, which is not particularly
// meaningful, but is at least consistent.
func (this *Draft) flatten() []Need {
	tiers := make([][]Need, 0)
	for _, n := range this.need.All() {
		for len(tiers) <= n.tier {
			tiers = append(tiers, make([]Need, 0))
		}
		tiers[n.tier] = append(tiers[n.tier], *n)
	}
	out := make([]Need, 0)
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

type ByMark []Need

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
