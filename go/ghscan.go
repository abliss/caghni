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
}

func (this *GhScanner) ghSplit(data []byte, atEOF bool) (
	advance int, token []byte, err error) {
	_ = fmt.Print //XXX
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
	fmt.Printf("XXXX cmd=%s\n", cmd)

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
		var dvs, hyps, conc []byte
		eatUntil(func() bool { return r == '(' })
		// read DVs
		eatUntil(func() bool { return r == '(' })
		i -= n
		start := i
		eatUntil(balanced)
		dvs = data[start:i]
		// read Hyps
		eatUntil(func() bool { return r == '(' })
		i -= n
		start = i
		eatUntil(balanced)
		hyps = data[start:i]
		// read Conc
		start = i
		parenDepth = 1
		eatUntil(balanced)
		conc = data[start : i-n]
		fmt.Printf("XXXX [%s/%s/%s]\n", dvs, hyps, conc)
		token = make([]byte, 0)
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
					fmt.Printf("%s %s %s\n", cmd, kind, tok)
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
	fmt.Printf("XXXX Advancing %d\n", i)

	advance = i
	return
}

func NewScanner(r io.Reader) *GhScanner {
	scanner := GhScanner{
		bufio.NewScanner(r),
		make(map[string]string),
		make(map[string]string),
	}
	scanner.Split(scanner.ghSplit)
	return &scanner
}
