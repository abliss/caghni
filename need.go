package main

import (
	"fmt"
	"sort"
)

// This file implements a map[Mark]*Need that's easily clonable.

// Need must be immutable.
type Need struct {
	tier  int
	mark  Mark
	entry *Entry // nil until the need is satisfied
}

type NeedMap struct {
	indices []int
	needs   []*Need
}

func (this NeedMap) Get(key Mark) (val Need, ok bool) {
	i := sort.SearchInts(this.indices, key.Index)
	if i < len(this.indices) && this.indices[i] == key.Index {
		return *(this.needs[i]), true
	}
	return Need{}, false
}

func (this *NeedMap) Put(key Mark, val Need) { // TODO: key == val.mark?
	i := sort.SearchInts(this.indices, key.Index)
	l := len(this.indices) + 1
	newIndices := make([]int, l)
	newNeeds := make([]*Need, l)
	copy(newIndices, this.indices[0:i])
	copy(newNeeds, this.needs[0:i])
	newIndices[i] = key.Index
	newNeeds[i] = &val
	copy(newIndices[i+1:], this.indices[i:])
	copy(newNeeds[i+1:], this.needs[i:])
	this.indices = newIndices
	this.needs = newNeeds
}

func (this NeedMap) SetTier(key Mark, tier int) {
	val, ok := this.Get(key)
	if !ok {
		panic("Can't set tier")
	}
	val.tier = tier
	this.Put(key, val)
	return
}

func (this NeedMap) SetEntry(key Mark, entry *Entry) (ok bool) {
	i := sort.SearchInts(this.indices, key.Index)
	if i >= len(this.indices) && this.indices[i] != key.Index {
		panic(fmt.Sprintf("Can't set entry %d:%s", key.Index, key.String()))
		return false
	}
	old := this.needs[i]
	this.needs[i] = &Need{old.tier, old.mark, entry}
	return true
}

func (this NeedMap) Copy() NeedMap {
	var that NeedMap
	that.indices = make([]int, len(this.indices))
	copy(that.indices, this.indices)
	that.needs = make([]*Need, len(this.needs))
	copy(that.needs, this.needs)
	return that
}

func (this *NeedMap) All() []*Need {
	return this.needs
}

func (this NeedMap) Len() int {
	return len(this.needs)
}

// Returns a mark whose need has no entry
func (this NeedMap) TopMark() (Mark, bool) {
	for _, n := range this.needs {
		if n.entry == nil {
			return n.mark, true
		}
	}
	return Mark{}, false
}
func (this NeedMap) Rewrite(bind Bind) NeedMap {
	var that NeedMap
	that.indices = make([]int, 0, len(this.indices))
	that.needs = make([]*Need, 0, len(this.needs))
	for _, n := range this.needs {
		newN := Need{n.tier, bind.Rewrite(n.mark), n.entry}
		that.Put(newN.mark, newN)
	}
	return that
}
