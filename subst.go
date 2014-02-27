package main

// Invariant: no key is also a value.
type Subst map[string]string

// For now, we disallow multiple keys mapping to the same value.
func (this Subst) Put(key, value string) (out Subst, ok bool) {
	if _, ok := this[value]; ok {
		return nil, false
	}
	if _, ok := this[key]; ok {
		return nil, false
	}
	that := make(Subst, len(this)+1)
	that[key] = value
	for k, v := range this {
		if v == key || v == value {
			return nil, false
		} else {
			that[k] = v
		}
	}
	return that, true
}
func (this Subst) Get(key string) (val string, ok bool) {
	val, ok = this[key]
	if !ok {
		val = key
	}
	return
}
func (this Subst) Clone() Subst {
	dst := make(Subst, len(this))
	for k, v := range this {
		dst[k] = v
	}
	return dst
}
