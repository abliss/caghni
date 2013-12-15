caghni
======

# Summary

Content-Addressable GHilbert Namespace and Index

The names for theorems in set.mm are too short to be understood by more than a handful of people. The names for theorems in wikiproofs are too long to be remembered, typed, or standardized upon. Furthermore, every corpus has its own way to represent operators (e.g. $->$ or &rarr;) and different decisions about definitions (e.g. whether to define &harr; in terms of &and; or vice-versa). If I prove a theorem in set.mm and you prove a theorem in wikiproofs, even if they say exactly the same thing and are proved exactly the same way, they will never be part of the same body of interchangeable proofs. 

The Ghilbert interface format solves part of the problem, but in an attempt to remain human-readable, has given up solving the hardest part: naming things.

The idea of caghni is to build a Ghilbert-compatable (or nearly-so) convention for naming theorems (and variables, operators, kinds, and interfaces). The goal is to have scripts which can convert a proof in set.mm, or the equivalent proof from wikiproofs, into a caghni repository, where identical proofs map to the same machine-readable object. Other scripts will convert from the universal caghni repository into metamath or wikiproofs, with the ability to add a style layer that assigns readable names (either short ones or long ones as the user prefers). The result will be one big happy family.

# Current Status

A nodejs-based tool can compile ghilbert files into a leveldb. A go-based tool
can then query the leveldb and produce ghilbert-verifiable output, gluing any
one interface to another on demand.

Sadly, whitespace and comments do not yet survive the procedure. And currently
everything must use the same set of operator terms.

# Try it out

You need relatively recent versions of `node.js` (I'm using 0.8.20) and `go` (1.1)

    $ npm install level
    $ node js/convert.js test/in-gh out

This compiles all `.gh` files into a database,`out/facts.leveldb`. It's slow, but you only have to do it once.

    $ cd go
    $ go get github.com/syndtr/goleveldb/leveldb
    $ go build
    $ cd ..
    $ go/go -d out/facts.leveldb \
            -i test/in-gh/peano/prop_nic.ghi \
            -e test/in-gh/peano/prop_luk.ghi > out.gh
    $ python ~/ghilbert/verify.py out.gh

This creates a file `out.gh` which starts by importing `prop-nic.ghi` and ends by exporting `prop_luk.ghi`. You can move from any of `prop_{nic,luk,mer,min}.ghi` to any other in this way. (If you did this by storing proofs in `.gh` files, some utility theorems would need to be proved ~12 times! In a caghni database we only need one copy of each.)

Only theorems which are necessary for the verification will be output. There are many possible way to achieve this. For example, a theorem which depends on the assertion `(-> ph ph)` might use either `id` or `id1` in its proof (regardless of which was used when the proof was originally written). In general, choosing which theorems to include is an NP-complete problem. The current code guarantees only that if there is a solution, it will eventually be found; and if there is not, the program will crash. In the future, we hope to improve the quality of the solutions.

The go program is pretty fast; it is also concurrent, so setting `$GOMAXPROCS` to, say, 4 or so, will likely make it even faster if your machine has many CPU cores.

# Schema

Each entity in the database represents a "Fact", which means a `stmt`, a `thm`, or a `defthm`. For example, in `peano/peano_thms.gh`, thm `alnex` is proved using `df-ex`:

    thm (alnex () () (<-> (A. x (-. ph)) (-. (E. x ph))) x ph df-ex con2bii)

In the database, this becomes

    {{alnex}} = {
      Bone: {
         Stmt: [0,[1,"v0.0",[2,"t1.0"],[2,[3,"v0.0","t1.0"]]]],
         Hyps: [],
         Free: [],
      },
      Meat: {
         Terms: ["<->", "A.", "-.", "E."],
         Kinds: ["nat", "wff"],
      },
      Skin: {
         V: [["x"]],
         T: [[],["ph"]],
         Name: "alnex",
         HypNames: [],
         DepNames: ["df-ex", "con2bii"]
         License: "public domain",
         Delimiters: [...],    // will preserve whitespace and comments
      },
      Tree: {
         Cmd: "thm",
         Deps: [{{df-ex}}, {{conb2bii}}],
         Proof: [V0.0, T1.0, Deps.0, Deps.1],   
         Terms: ["<->", "A.", "-.", "E."],    // Meat.Terms is a prefix
         Kinds: ["nat", "wff"],               // Meat.Kinds is a prefix
      },
    }

The "Bone" is the actual skeleton of the Fact, and is fundamental to how it is used in a proof. The "Meat" represents the "arbitrary-but-consistent" name-choices: within a `.gh` file, all Facts must use the same Meat-values; but a substitution applied consistently throughout the file (e.g. &rarr; for `->`) is okay. The "Skin" comprises presentation-only content which doesn't affect the Fact's meaning or how it is used. The "Tree" captures the Fact's dependence on other Facts. (Terms and Kinds which are present in the proof of a thm, but not in its statement or hyps, are kept in the Tree in order to keep the Bone clean.)

An element of the Tree.Deps array does not refer to a particular fact, but only to its Bone and Meat. So intead of "df-ex", we store this key:
    
    [[[0,[1,V0.0,T1.0],[2,[3,V0.0,[2,T1.0]]]],[],[]],[<->,E.,-.,A.],[nat,wff]]
 
Now we know that if we want to prove the Fact of `alnex`, we don't necessarily need `df-ex`, just some Fact (be it a thm, a defthm, or a stmt) with this Bone, and a compatible Meat.

For example, in general/First-order_logic.gh, there is 

    defthm (ThereExists formula (∃ x φ) () () (↔ (∃ x φ) (¬ (∀ x (¬ φ)))) ...)

which creates a Fact with this key:

    [[[0,[1,V0.0,T1.0],[2,[3,V0.0,[2,T1.0]]]],[],[],[↔,∃, ¬, ∀],[object,formula]] 

Thus, as long as our query engine can consistently map ↔ to `<->` ,  "formula" to "wff", etc. throughout the file, this could be used just as well as df-ex. (Not yet implemented.)

The leveldb is a simply key-value store; the key for each Fact is its Bone-Meat string, as above, plus the sha1sum of its JSON contents. A Fact's proof is verified as it is added to the database; its entry never changes and need never be deleted. Multiple proofs of a Fact can happily exist side-by-side; one or another may be chosen for a particular query based on a variety of scoring algorithms. This database should scale well to many millions of Facts, and could easily be sharded across machines.



