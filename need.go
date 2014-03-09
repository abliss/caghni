package main

// This file implements a map[Mark]*Need that's easily clonable.

// Need must be immutable.
type Need struct {
	tier  int
	mark  Mark
	entry *Entry // nil until the need is satisfied
}

type NeedMap struct {
	mine map[int]*Need
}

func (this *NeedMap) Get(key Mark) (val *Need, ok bool) {
	val, ok = this.mine[key.Hash()]
	return
}

func (this *NeedMap) Put(key Mark, val *Need) {
	if this.mine == nil {
		this.mine = make(map[int]*Need)
	}
	this.mine[key.Hash()] = val
}

func (this *NeedMap) SetTier(key Mark, tier int) (ok bool) {
	var val *Need
	val, ok = this.mine[key.Hash()]
	if !ok {
		return
	}
	val2 := &Need{tier, val.mark, val.entry}
	this.mine[key.Hash()] = val2
	return
}

func (this *NeedMap) SetEntry(key Mark, entry *Entry) (ok bool) {
	var val *Need
	val, ok = this.mine[key.Hash()]
	if !ok {
		panic("Can't set entry")
	}
	val2 := &Need{val.tier, val.mark, entry}
	this.mine[key.Hash()] = val2
	return
}

func (this *NeedMap) Copy() NeedMap {
	dst := NeedMap{make(map[int]*Need, len(this.mine))}
	for k, v := range this.mine {
		dst.mine[k] = &Need{v.tier, v.mark, v.entry}
	}
	return dst
}

func (this *NeedMap) Each(what func(*Need)) {
	for _, v := range this.mine {
		what(v)
	}
}

func (this *NeedMap) Len() int {
	return len(this.mine)
}

// Returns a mark whose need has no entry
func (this *NeedMap) TopMark() (Mark, bool) {
	for _, n := range this.mine {
		if n.entry == nil {
			return n.mark, true
		}
	}
	return Mark{}, false
}
