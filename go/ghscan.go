package main

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"unicode"
	"unicode/utf8"
)

type GhScanner struct {
	*bufio.Scanner
	varKinds  map[string]string
	tvarKinds map[string]string
	lastEntry *Entry
}

func (this *GhScanner) ghSplit(data []byte, atEOF bool) (
	advance int, token []byte, err error) {
	i := 0
	var r rune
	var n int
	var EOF, UTF8 interface{}
	var eofError error
	eatUntil := func(f func() bool) {
		for {
			if i >= len(data) {
				advance = 0
				if atEOF {
					err = eofError
				}
				panic(&EOF)
			}
			r, n = utf8.DecodeRune(data[i:])
			if r == utf8.RuneError {
				err = errors.New("Bad UTF8 encoding!")
				panic(&UTF8)
			}
			i += n
			if f() {
				return
			}
		}
	}
	defer func() {
		r := recover()
		if r == &EOF {
		} else if r == &UTF8 {
		} else if r != nil {
			panic(r)
		}
	}()
	eatUntil(func() bool { return !unicode.IsSpace(r) })
	for r == '#' {
		eatUntil(func() bool { return r == '\n' })
		eatUntil(func() bool { return !unicode.IsSpace(r) })
	}
	eofError = errors.New("Unexpected EOF") // eof not allowed until end sexp
	cmdStart := i - n
	eatUntil(func() bool { return unicode.IsSpace(r) })
	cmd := string(data[cmdStart : i-n])

	parenDepth := 0
	balanced := func() bool {
		if r == '(' {
			parenDepth++
		} else if r == ')' {
			parenDepth--
		}
		return parenDepth == 0
	}

	if cmd == "stmt" {
		var label []byte
		var dvStart, hypStart, concStart, end int
		eatUntil(func() bool { return r == '(' })
		start := i
		eatUntil(func() bool { return unicode.IsSpace(r) })
		label = data[start : i-n]
		// read DVs
		eatUntil(func() bool { return r == '(' })
		i -= n
		dvStart = i
		eatUntil(balanced)
		// read Hyps
		eatUntil(func() bool { return r == '(' })
		i -= n
		hypStart = i
		eatUntil(balanced)
		// read Conc
		eatUntil(func() bool { return !unicode.IsSpace(r) })
		i -= n
		concStart = i
		parenDepth = 1
		eatUntil(balanced)
		end = i
		// We just emit the label to Text();
		// the rest is available in thus.Entry()
		token = label
		entry := new(Entry)
		entry.Fact.Skin.Name = string(label)
		// Now build the key
		key := ""
		terms := make([]string, 0)
		kinds := make([]string, 0)
		i = concStart
		parenDepth = 1
		start = i
		argNum := make([]int, 1)
		argNum[0] = -1
		fmt.Printf("XXXX Parsing %s\n", data[i:end])

		eatUntil(func() bool {
			if r == ')' || unicode.IsSpace(r) {
				if i-n > start {
					tok := string(data[start : i-n])
					if argNum[len(argNum)-1] == 0 {
						key += "T(" + tok + ")"
					} else {
						key += ",V(" + tok + ")"
					}
					argNum[len(argNum)-1]++
				}
				start = i
			}
			if r == '(' {
				parenDepth++
				if argNum[len(argNum)-1] > 0 {
					key += ","
				}
				key += "["
				start = i
				argNum = append(argNum, 0)
			} else if r == ')' {
				parenDepth--
				key += "]"
				argNum = argNum[0:len(argNum)]
			}
			return parenDepth == 0
		})
		key = key[0 : len(key)-1] // strip trailing ']'
		_ = dvStart
		_ = hypStart
		_ = terms
		_ = kinds
		fmt.Printf("XXXX %s\n", key)
		i = end
	} else if cmd == "tvar" || cmd == "var" {
		eatUntil(func() bool { return r == '(' })
		start := i
		eatUntil(func() bool { return unicode.IsSpace(r) })
		kind := string(data[start : i-n])
		start = i
		eatUntil(func() bool {
			if unicode.IsSpace(r) || r == ')' {
				if i-n > start {
					tok := string(data[start : i-n])
					if cmd == "tvar" {
						this.tvarKinds[tok] = kind
					} else {
						this.varKinds[tok] = kind
					}
				}
				start = i
			}
			return r == ')'
		})
		token = make([]byte, 0)
	} else {
		// other commands (kind, term) we skip.
		eatUntil(balanced)
		token = make([]byte, 0)
	}
	advance = i
	return
}

// NB: ghSplit emits empty tokens on ignored text. This wrapper
// eliminates those.
func (this *GhScanner) splitWrap(data []byte, atEOF bool) (
	advance int, token []byte, err error) {
	var a int
	for len(token) == 0 && err == nil {
		a, token, err = this.ghSplit(data[advance:], atEOF)
		if a == 0 {
			return 0, nil, err
		}
		advance += a
	}
	return
}

func (this *GhScanner) Entry() *Entry {
	return nil //XXX
}

func NewScanner(r io.Reader) *GhScanner {
	scanner := GhScanner{
		bufio.NewScanner(r),
		make(map[string]string),
		make(map[string]string),
		nil,
	}
	scanner.Split(scanner.splitWrap)
	return &scanner
}
