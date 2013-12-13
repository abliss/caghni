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

type sexp struct {
	Leaf string
	Kids []*sexp
	mama *sexp
}

func (s *sexp) toString() string {
	if len(s.Leaf) > 0 {
		return s.Leaf
	}
	out := "("
	first := true
	for _, k := range s.Kids {
		if !first {
			out += ","
		}
		first = false
		out += k.toString()
	}
	out += ")"
	return out
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
	eatUntil(func() bool { return !unicode.IsSpace(r) })
	i -= n
	var s *sexp
	tokStart := i
	// eat sexp  TODO: needs testing
	eatUntil(func() bool {
		isSpace := unicode.IsSpace(r)
		if r == ')' || isSpace {
			if i-n > tokStart {
				tok := new(sexp)
				tok.Leaf = string(data[tokStart : i-n])
				tok.mama = s
				s.Kids = append(s.Kids, tok)
			}
			tokStart = i
		}

		if r == '(' {
			kid := new(sexp)
			kid.mama = s
			if s != nil {
				s.Kids = append(s.Kids, kid)
			}
			s = kid
			tokStart = i
		} else if r == ')' {
			if s.mama == nil {
				return true
			}
			s = s.mama
		}
		return false
	})

	if cmd == "stmt" {
		// Emit the token as flat text. Access to the parsed fact is through
		// Entry()
		token = data[cmdStart:i]
		kinds := make([]string, 0)
		terms := make([]string, 0)
		if len(s.Kids) != 4 {
			err = errors.New(fmt.Sprintf("Bad stmt command: %s\n",
				data[cmdStart:i]))
			panic(err)
		}
		label, dvs, hyps, conc := s.Kids[0], s.Kids[1], s.Kids[2], s.Kids[3]
		e := new(Entry)
		e.Fact.Skin.Name = label.Leaf
		this.lastEntry = e
		_ = dvs
		_ = hyps
		_ = conc
		_ = kinds
		_ = terms
	} else if cmd == "tvar" || cmd == "var" {
		kind := s.Kids[0].Leaf
		for _, vars := range s.Kids[1:] {
			varName := vars.Leaf
			if cmd == "tvar" {
				this.tvarKinds[varName] = kind
			} else {
				this.varKinds[varName] = kind
			}
			//XX fmt.Printf("XXXX %s %s = %s\n", cmd, varName, kind)
		}
		token = make([]byte, 0)
	} else {
		// other commands (kind, term) we skip.
		token = make([]byte, 0)
	}
	if false {
		fmt.Printf("XXXX %s %s\n", cmd, s.toString())
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
	return this.lastEntry
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
