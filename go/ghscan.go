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

// TODO: not sure whether this is necessary??
func (s *sexp) destroy() {
	s.mama = nil
	for _, k := range s.Kids {
		k.destroy()
	}
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

func indexOf(list []string, t string) (i int, l []string) {
	l = list
	var k string
	for i, k = range l {
		if k == t {
			return
		}
	}
	return len(l), append(l, t)
}

// returns a JSON-like string wrapping
func bracketize(ss []string) string {
	out := "["
	first := true
	for _, s := range ss {
		if !first {
			out += ","
		}
		out += s
		first = false
	}
	out += "]"
	return out
}
func mapify(ss []*sexp, f func(s *sexp) string) []string {
	out := make([]string, len(ss))
	for i, k := range ss {
		out[i] = f(k)
	}
	return out
}

// Turns a sexp into a string.  Assumes all leafs are vars.
// Augments the fields of this.lastEntry as we go.
func (this *GhScanner) stringify(s *sexp) string {
	if len(s.Leaf) > 0 {
		var kind, pfix string
		var ok bool
		if kind, ok = this.tvarKinds[s.Leaf]; ok {
			pfix = "T"
		} else if kind, ok = this.varKinds[s.Leaf]; ok {
			pfix = "V"
		} else {
			panic(errors.New(fmt.Sprintf("Unknown var %s", s.Leaf)))
		}
		oldLen := len(this.lastEntry.Fact.Meat.Kinds)
		var kindI int
		kindI, this.lastEntry.Fact.Meat.Kinds =
			indexOf(this.lastEntry.Fact.Meat.Kinds, kind)
		if kindI >= oldLen {
			// new kind; augment V and T
			this.lastEntry.Fact.Skin.T = append(this.lastEntry.Fact.Skin.T,
				make([]string, 0))
			this.lastEntry.Fact.Skin.V = append(this.lastEntry.Fact.Skin.V,
				make([]string, 0))
		}
		var varList [][]string
		if pfix == "T" {
			varList = this.lastEntry.Fact.Skin.T
		} else {
			varList = this.lastEntry.Fact.Skin.V
		}
		var varI int
		varI, varList[kindI] = indexOf(varList[kindI], s.Leaf)
		return fmt.Sprintf("%s%d.%d", pfix, kindI, varI)
	} else {
		return bracketize(mapify(s.Kids, this.stringify))
	}
}

// Turns a sexp into a string.  Assumes all leafs are vars, except the first,
// which is a term.  Augments the fields of this.lastEntry as we go.
func (this *GhScanner) stringifyTerm(s *sexp) string {
	if len(s.Leaf) > 0 {
		return this.stringify(s)
	} else {
		if len(s.Kids) < 1 {
			msg := ""
			for s.mama != nil {
				msg += s.toString() + "\n"
				s = s.mama
			}
			panic("Empty isTerm sexp! " + msg)
		}
		var termI int
		termI, this.lastEntry.Fact.Meat.Terms =
			indexOf(this.lastEntry.Fact.Meat.Terms, s.Kids[0].Leaf)
		ss := make([]string, 1)
		ss[0] = fmt.Sprintf("%d", termI)
		kids := mapify(s.Kids[1:], this.stringifyTerm)
		return bracketize(append(ss, kids...))
	}
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

	switch cmd {
	case "stmt":
		// Emit the token as flat text. Access to the parsed fact is through
		// Entry()
		token = data[cmdStart:i]
		if len(s.Kids) != 4 {
			err = errors.New(fmt.Sprintf("Bad stmt command: %s\n",
				data[cmdStart:i]))
			panic(err)
		}
		label, dvs, hyps, conc := s.Kids[0], s.Kids[1], s.Kids[2], s.Kids[3]
		this.lastEntry = new(Entry)
		this.lastEntry.Fact.Skin.Name = label.Leaf

		key := bracketize([]string{
			bracketize([]string{
				this.stringifyTerm(conc),
				bracketize(mapify(hyps.Kids, this.stringifyTerm)),
				bracketize(mapify(dvs.Kids, this.stringify)),
			}),
			bracketize([]string{
				bracketize(this.lastEntry.Fact.Meat.Terms),
				bracketize(this.lastEntry.Fact.Meat.Kinds),
			}),
		})
		this.lastEntry.Key = key
	case "tvar", "var":
		kind := s.Kids[0].Leaf
		for _, vars := range s.Kids[1:] {
			varName := vars.Leaf
			if cmd == "tvar" {
				this.tvarKinds[varName] = kind
			} else {
				this.varKinds[varName] = kind
			}
		}
		token = make([]byte, 0)
	case "param":
		//PICKUP : how to handle?
	default:
		// other commands (kind, term) we skip.
		token = make([]byte, 0)
	}
	advance = i
	s.destroy()
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
