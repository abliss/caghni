caghni
======

# Summary

Content-Addressable GHilbert Namespace and Index

The names for theorems in set.mm are too short to be understood by more than a handful of people. The names for theorems in ProofWiki are too long to be remembered, typed, or standardized upon. If I prove a theorem in set.mm and you prove a theorem in ProofWiki, even if they say exactly the same thing and are proved exactly the same way, they will never be part of the same body of interchangeable proofs.

The Ghilbert interface format solves part of the problem, but in an attempt to remain human-readable, has given up solving the hardest part: naming things.

The idea of caghni is to build a Ghilbert-compatable (or nearly-so) convention for naming theorems (and variables, operators, kinds, and interfaces). The goal is to have scripts which can convert a proof in set.mm, or the equivalent proof from ProofWiki, into a caghni repository, where identical proofs map to the same machine-readable object. Other scripts will convert from the universal caghni repository into metamath or ProofWiki, with the ability to add a style layer that assigns readable names (either short ones or long ones as the user prefers). The result will be one big happy family.

# Current Status

A small script is provided which parses a ghilbert module and produces a verifiable output. In version 1, the following names are standardized:

* the label of thms, defthms, and stmts
* the label of hyps within a thm or defthm
* the names of variables

Exported interfaces are updated so that peano_thms.gh matches. Imported interfaces are currently not changed.

# The next schema (V2 draft)

In peano/peano_thms.gh, thm `alnex` is proved using `df-ex`:

    thm (alnex () () (<-> (A. x (-. ph)) (-. (E. x ph))) x ph df-ex con2bii)

In caghni V2, this will become:

    {{alnex}} = {
      bone: {
         stmt: [0,[1,"v0.0",[2,"t1.0"],[2,[3,"v0.0","t1.0"]]]],
         hyps: [],
         free: [],
      },
      meat: {
         terms: ["<->", "A.", "-.", "E."],
         kinds: ["nat", "wff"],
      },
      skin: {
         v: [["x"]],
         t: [[],["ph"]],
         name: "alnex",
         hypNames: [],
         license: "public domain",
         delimiters: [...],    // preserves whitespace and comments
      },
      tree: {
         cmd: "thm",
         deps: [{{df-ex}}, {{conb2bii}}],
         proof: [v0.0, t1.0, deps.0, deps.1],
      },
    }
    
depending on:

    defthm (df-ex wff (E. x ph) () () (<-> (E. x ph) (-. (A. x (-. ph)))) ...)

which enters caghni V2 as:

    {{df-ex}} = {
      conc: {
        dvs:  [],
        hyps: [],
        term: [o.0,[o.1, v.0.0, t.1.0],[o.2,[o.3, v.0.0,[o.2, t.1.0]]]],
      },
      style: {
         o: ["<->", "E.", "-.", "A."],
         k: ["nat", "wff"],
         v: [["x"]],
         t: [[],["ph"]],
      },
      // ...etc
    }

Also, in general/First-order_logic.gh, there is 

    defthm (ThereExists formula (∃ x φ) () () (↔ (∃ x φ) (¬ (∀ x (¬ φ)))) ...)

which parses as 

    {
      conc: {
        dvs:  [],
        hyps: [],
        term: [o.0,[o.1, v.0.0, t.1.0],[o.2,[o.3, v.0.0,[o.2, t.1.0]]]],
      },
      style: {
         o: ["↔","∃", ¬", ∀"]
         k: ["object", "formula"],
         v: [["x"]],
         t: [[],["φ"]],
      },
      // ...etc
    }

We throw all these objects into a content-addressable store, and index by
`conc`. Now for an artist working in `general/` to pull in `alnex`, all that is
required is to specify the desired `conc` and the preferred styling. The lookup
returns the `{{alnex}}` object above, and creates a "style map" necessary to
convert the object to the preferred style. The engine then looks up dependencies
recursively, augmenting the style map as it goes. If the dependencies all ground
out (either in thms, in defthms, or in stmts), it then returns a chunk of
ghilbert, styled appropriately, proving the desired thm, ready for insertion
into the artist's ghilbert file.

Note that a query by `conc` will in general give many results. You might find
several different proofs of the thm you want, in different corpi. Or you might
find within one corpus two theorems with totally different operators which
happen to have the same `conc`. Each time we recurse on dependencies, we have to
preserve the old style map, in case we find a mismatch and have to
backtrack. Among the complete results, we can score them based on, say: 1. how
many new axioms must be added; 2. how many new theorems must be added; 3. how
many steps are in the proof; etc. We can even program in automatic license
compatability testing.

# Try it out

You need relatively recent versions of `node.js` (I'm using 0.8.20) and `go` (1.21)

    $ npm install level
    $ node js/convert.js test/in-gh out
    $ go get github.com/syndtr/goleveldb/leveldb
    $ go build go/query
    $ go/query -d out/facts.leveldb
