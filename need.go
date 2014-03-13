package main

import (
	"fmt"
)

// This file implements a map[Mark]*Need that's easily clonable.

// Need must be immutable.
type Need struct {
	tier  int
	mark  Mark
	entry *Entry // nil until the need is satisfied
}

type NeedMap struct {
	a []*Need
}

func (this NeedMap) Get(key Mark) (val Need, ok bool) {
	if len(this.a) <= key.Index || this.a[key.Index] == nil {
		return
	}
	return *(this.a[key.Index]), true
}

func (this *NeedMap) Put(key Mark, val Need) { // TODO: key == val.mark?
	if len(this.a) <= key.Index {
		newA := make([]*Need, MaxMark)
		copy(newA, this.a)
		this.a = newA
	}
	this.a[key.Index] = &val
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
	var val Need
	val, ok = this.Get(key)
	if !ok {
		panic(fmt.Sprintf("Can't set entry %d:%s", key.Index, key.String()))
	}
	if val.entry != nil {
		panic("Can't reset entry " + key.String())
	}
	val.entry = entry
	this.Put(key, val)
	return
}

func (this NeedMap) Copy() NeedMap {
	var that NeedMap
	that.a = make([]*Need, len(this.a))
	copy(that.a, this.a)
	return that
}

func (this *NeedMap) All() []Need {
	out := make([]Need, 0, len(this.a))
	for _, v := range this.a {
		if v != nil {
			out = append(out, *v)
		}
	}
	return out
}

func (this NeedMap) Len() int {
	// TODO: dumb
	return len(this.All())
}

// Returns a mark whose need has no entry
func (this NeedMap) TopMark() (Mark, bool) {
	// TODO: dumb
	for _, n := range this.All() {
		if n.entry == nil {
			return n.mark, true
		}
	}
	return Mark{}, false
}
func (this NeedMap) Rewrite(bind Bind) NeedMap {
	var that NeedMap
	that.a = make([]*Need, len(this.a))
	for _, n := range this.a {
		if n != nil {
			newN := &Need{n.tier, bind.Rewrite(n.mark), n.entry}
			that.a[newN.mark.Index] = newN
		}
	}
	return that
}
