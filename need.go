package main

//import "fmt"

// This file implements a map[Mark]*Need that's easily clonable.

// Need must be immutable.
type Need struct {
	tier  int
	mark  Mark
	entry *Entry // nil until the need is satisfied
}

type NeedMap struct {
	mine map[string]Need
	papa *NeedMap
}

func (this *NeedMap) Get(key Mark) (val Need, ok bool) {
	val, ok = this.mine[key.Hash()]
	if !ok && this.papa != nil {
		val, ok = this.papa.Get(key)
	}
	return
}

func (this *NeedMap) Put(key Mark, val Need) { // TODO: key == val.mark?
	if this.mine == nil {
		this.mine = make(map[string]Need)
	}
	this.mine[key.Hash()] = val
}

func (this *NeedMap) SetTier(key Mark, tier int) {
	val, ok := this.Get(key)
	if !ok {
		panic("Can't set tier")
	}
	val.tier = tier
	this.Put(key, val)
	return
}

func (this *NeedMap) SetEntry(key Mark, entry *Entry) (ok bool) {
	var val Need
	val, ok = this.Get(key)
	if !ok {
		panic("Can't set entry " + key.String())
	}
	if val.entry != nil {
		panic("Can't reset entry " + key.String())
	}
	val.entry = entry
	this.Put(key, val)
	return
}

func (this *NeedMap) Copy() NeedMap {
	var dst NeedMap
	dst.papa = this
	return dst
}

func (this *NeedMap) All() []Need {
	var b Bind
	that := this.Rewrite(b)
	out := make([]Need, 0, len(that.mine))
	for _, v := range that.mine {
		out = append(out, v)
	}
	return out
}

func (this *NeedMap) Len() int {
	if this == nil {
		return 0
	}
	return len(this.mine) + this.papa.Len() // TODO: ignores duplicates
}

// Returns a mark whose need has no entry
func (this *NeedMap) TopMark() (Mark, bool) {
	that := this
	for that != nil {
		for _, n := range that.mine {
			if nn, _ := this.Get(n.mark); nn.entry == nil {
				return nn.mark, true
			}
		}
		that = that.papa
	}
	return Mark{}, false
}
func (this *NeedMap) Rewrite(bind Bind) NeedMap {
	eirs := make(map[string]Need)
	that := this
	for that != nil {
		for _, n := range that.mine {
			n.mark = bind.Rewrite(n.mark)
			if _, ok := eirs[n.mark.Hash()]; !ok {
				eirs[n.mark.Hash()] = n
			}
		}
		that = that.papa
	}
	return NeedMap{eirs, nil}
}
