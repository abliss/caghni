package main

// Invariant: no key is also a value.
type Subst map[string]string

func (this *Subst) Put(key, value string) (out *Subst, ok bool) {
	if this == nil {
		that := make(Subst, 1)
		that[key] = value
		return &that, true
	}
	newValue, ok := (*this)[value]
	if ok && newValue == key {
		return nil, false
	}
	if !ok {
		newValue = value
	}
	that := make(Subst, len(*this)+1)
	that[key] = newValue
	for k, v := range *this {
		if v == key {
			that[k] = newValue
		} else {
			that[k] = v
		}
	}
	return &that, true
}
func (this *Subst) Get(key string) (val string, ok bool) {
	if this == nil {
		return key, false
	}
	val, ok = (*this)[key]
	if !ok {
		val = key
	}
	return
}
func (this *Subst) Clone() *Subst {
	if this == nil {
		return nil
	}
	dst := make(Subst, len(*this))
	for k, v := range *this {
		dst[k] = v
	}
	return &dst
}
