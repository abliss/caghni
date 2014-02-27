package main

// Invariant: no key is also a value.
type Subst map[string]string

func (this Subst) Put(key, value string) (out Subst, ok bool) {
	newValue, ok := this[value]
	if ok && newValue == key {
		return nil, false
	}
	if !ok {
		newValue = value
	}
	that := make(Subst, len(this)+1)
	that[key] = newValue
	for k, v := range this {
		if v == key {
			that[k] = newValue
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
