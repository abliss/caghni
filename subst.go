package main

import (
	"sort"
	"strings"
)

// A Subst is a souped-up map[string]string. It is transitively closed, meaning
// that if s[a] => b and s[b] => c, then s[a] => c automatically. Cycles are
// disallowed. Further, in order to avoid a proliferation of distinct but
// equivalent Substs (and thus a massive duplication of effort), a global
// synchronized lookup is performed on each Put. For this purpose we maintain
// the contents in two parallel arrays sorted by key.

// Internally, uses \x00 and \x01 as delimiters, so they better not be in the
// keys or values.
type kv struct {
	k string
	v string
}

var (
	substCanon map[kv]*Subst // TODO: make threadsafe
)

// Invariant: no key is also a value.
type Subst struct {
	m map[string]int
	k []string
	v []string
}

func (this Subst) String() string {
	s := ""
	for k, i := range this.m {
		s += k + ":" + this.v[i] + " "
	}
	return s
}
func canonicalize(k, v []string) *Subst {
	key := kv{strings.Join(k, "\x00"), strings.Join(v, "\x00")}
	if substCanon == nil {
		substCanon = make(map[kv]*Subst)
	}
	if val, ok := substCanon[key]; ok {
		return val
	}
	val := new(Subst)
	val.k = k
	val.v = v
	val.m = make(map[string]int, len(k))
	for i, s := range k {
		val.m[s] = i
	}
	substCanon[key] = val
	return val
}

// For now, we disallow multiple keys mapping to the same value, and remapping
// keys
func (this *Subst) Put(key, value string) (out *Subst, ok bool) {
	if this == nil {
		k := []string{key}
		v := []string{value}
		return canonicalize(k, v), true
	}
	if _, ok := this.m[key]; ok {
		return nil, false
	}
	if _, ok := this.m[value]; ok {
		return nil, false
	}

	i := sort.SearchStrings(this.k, key)
	l := len(this.k) + 1
	k := make([]string, l)
	v := make([]string, l)
	copy(k, this.k[0:i])
	copy(v, this.v[0:i])
	k[i] = key
	v[i] = value
	copy(k[i+1:], this.k[i:])
	copy(v[i+1:], this.v[i:])
	for _, s := range v {
		if s == key {
			return nil, false // TODO: support actual transitivity
		}
	}
	return canonicalize(k, v), true
}

// Returns the value corresponding to the key, if there is one, or the key, if
// not.
func (this *Subst) Get(key string) (val string, ok bool) {
	if this == nil {
		return key, false
	}
	i, ok := this.m[key]
	if !ok {
		return key, false
	}
	return this.v[i], true
}

func (this *Subst) Len() int {
	if this == nil {
		return 0
	}
	return len(this.k)
}

/*
func (this Subst) Clone() Subst {
	dst := make(Subst, len(this))
	for k, v := range this {
		dst[k] = v
	}
	return dst
}
*/
