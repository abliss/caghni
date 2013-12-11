package main

import (
	"bufio"
	"errors"
	"unicode"
	"unicode/utf8"
)

// A bufio.SplitFunc for scanning ghilbert files.  Comments are eaten and
// whitespace normalized; you will get a string with a cmd token and a balanced
// sexp.
func split(data []byte, atEOF bool) (advance int, token []byte, err error) {
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
	token = make([]byte, len(data))
	j := 0
	take := func(s rune) {
		j += utf8.EncodeRune(token[j:], s)
	}
	space := func() {
		if token[j-1] != ' ' {
			token[j] = ' '
			j++
		}
	}
	take(r)
	eatUntil(func() bool {
		if unicode.IsSpace(r) {
			return true
		} else {
			take(r)
			return false
		}
	})
	space()
	parenDepth := 0
	eatUntil(func() bool {
		if r == '(' {
			parenDepth++
			take(r)
		} else if r == ')' {
			parenDepth--
			take(r)
		} else if unicode.IsSpace(r) {
			space()
		} else {
			take(r)
		}
		return parenDepth == 0
	})

	token = token[0:j]
	advance = i
	return
}

var GhSplit bufio.SplitFunc = split
