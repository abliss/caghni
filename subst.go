package main

// Invariant: no key is also a value.
type Subst map[string]string

func (this *Subst) Put(key, value string) *Subst {
	if this == nil {
		that := make(map[string]string, 1)
		that[key] = value
		return &that
	}
	newValue, ok := *this[value]
	if ok && newValue == key {
		return nil
	}
	if !ok {
		newValue = value
	}
	that := make(map[string]string, len(this)+1)
	that[key] = newValue
	for k, v := range this {
		if v == key {
			that[k] = newValue
		} else {
			that[k] = v
		}
	}
	return &that
}
func (this *Subst) Get(key string) (val string, ok bool) {
	val, ok = this[key]
	if !ok {
		val = key
	}
	return
}
