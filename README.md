caghni
======

# Summary

Content-Addressable GHilbert Namespace and Index

The names for theorems in set.mm are too short to be understood by more than a handful of people. The names for theorems in wikiproofs are too long to be remembered, typed, or standardized upon. Furthermore, every corpus has its own way to represent operators (e.g. `->` or &rarr;) and different decisions about definitions (e.g. whether to define &harr; in terms of &and; or vice-versa). If I prove a theorem in set.mm and you prove a theorem in wikiproofs, even if they say exactly the same thing and are proved exactly the same way, they will never be part of the same body of interchangeable proofs. 

The Ghilbert interface format solves part of the problem, but in an attempt to remain human-readable, has given up solving the hardest part: naming things.

The idea of caghni is to build a Ghilbert-compatable (or nearly-so) convention for naming theorems (and variables, operators, kinds, and interfaces). The goal is to have scripts which can convert a proof in set.mm, or the equivalent proof from wikiproofs, into a caghni repository, where identical proofs map to the same machine-readable object. Other scripts will convert from the universal caghni repository into metamath or wikiproofs, with the ability to add a style layer that assigns readable names (either short ones or long ones as the user prefers). The result will be one big happy family.

# Current Status

A nodejs-based tool can compile ghilbert files into a leveldb. Another nodejs
tool can then query the leveldb and produce ghilbert-verifiable output, creating
from any target thm a minimal .gh/.ghi filepair. (The go-lang code is currently not
up-to-date.)

Sadly, whitespace and comments do not yet survive the procedure. And currently
everything must use the same set of term operators.

# Try it out

You need relatively recent versions of `node.js` (I'm using 0.8.20) and `go` (1.1)

    $ cd js
    $ npm install level
    $ node convert.js ../test/in-gh ../out

This compiles all `.gh` files into a database,`out/facts.leveldb`. It's slow, but you only have to do it once.

    $ node query.js ../out

This creates a proof file `tmp.gh` (which ends in the desired fact) and an
interface file 'tmp.ghi' (which includes all needed axioms for tmp.gh).  Note
that even though the original proof of a theorem may have appeared in a file
that imported several interfaces with many axioms, the generated proof file has
only one import, and it only contains the axioms necessary to support the theorem.

In general, there are many possible way to achieve this. For example, a theorem which depends on the assertion `(-> ph ph)` might use either `id` or `id1` in its proof (regardless of which was used when the proof was originally written). There is also the problem of choosing which axiom set to ground out in. These choices are driven by a scoring function in `query.js`, which is presently rather crude.

The query script is very much a work-in-progress. It doesn't backtrack, and is wasteful of RAM and CPU.  It can handle `addcom` if you let it have a few minutes and a few hundred MB of RAM to work with. If your scoring function isn't tuned exactly right, the search can get stuck in an infinite recursion.

# Schema

Each entity in the database represents a "Fact", which means a `stmt`, a `thm`, or a `defthm`. For example, in `peano/peano_thms.gh`, thm `alnex` is proved using `df-ex`:

    thm (alnex () () (<-> (A. x (-. ph)) (-. (E. x ph))) x ph df-ex con2bii)

In the database, this becomes the following object:

    {
     Core: [
            [],                           // Hyps
            [0,[1,0,[2,1]],[2,[3,0,1]]],  // Stmt
            [],                           // Free
           ],
     Skin:{
         Name:"alnex",
         HypNames:[],
         Delimiters:[],            // will preserve whitespace and comments
         DepNames:["df-ex","con2bii"],
         VarNames:["x", "ph"],
         TermNames:["<->","A.","-.","E."],  // May end with terms not present in Core
     },
     Tree:{
         Cmd:"thm",
         Deps:[
             [[[],[0,[1,0,1],[2,[3,0,[2,1]]]],[]], // The Core of a Fact we depend on
              [0,3,2,1]],       // A permutation mapping the dep's terms onto our own
             [[[[0,1,[1,0]]],[0,0,[1,1]],[]],
              [0,2]]],
         Proof:[0,1,"Deps.0","Deps.1"],
     }
     FreeMaps: [[],[[]],[],[[]]],         // FreeMap for each Term
    }

The "Core" is the actual skeleton of the Fact, and is fundamental to how it is used in a proof. The "Skin" comprises presentation-only content which doesn't affect the Fact's meaning or how it is used. The "Tree" captures the Fact's dependence on other Facts. Each element of the Tree.Deps array names a prerequisite for the Proof. However, it does not refer to a particular fact, but only to its Core, and to the mapping between the Term indices of the two Facts.

"FreeMaps" is necessary to calculate which binding variables are free in which
terms. It also helps us identify which variables are binding variables.
 
Now we know that if we want to prove the Fact of `alnex`, we don't necessarily need `df-ex`, just some Fact (be it a thm, a defthm, or a stmt) with the same Core, and a compatible set of terms. If its Skin.TermNames matches, we can use it directly. If a substitution is applied consistently through the file (e.g. &rarr; for `->`) that's okay too.

For example, in general/First-order_logic.gh, there is 

    defthm (ThereExists formula (∃ x φ) () () (↔ (∃ x φ) (¬ (∀ x (¬ φ)))) ...)

which creates a Fact with the same Core as `alnex` (i.e, `[[],[0,[1,0,1],[2,[3,0,[2,1]]]],[]]`) and a `Skin.TermNames` array of `["↔","∃","¬","∀"]]`.  Thus, as long as the FreeMaps match up, and our query engine can consistently map ↔ to `<->` ,  etc. ,throughout the file, this can be used just as well as df-ex. (Not yet implemented.)

Note that the Fact schema stores no information about the Kinds of variables or
terms, nor the distinction between "Term Variables" and "Binding Variables"
(`tvar` versus `var` statements). The latter can be inferred from the freemaps
(with the side-effect of occasionally making a theorem more general) and the
former can be elided without sacrificing soundness: in the generated ghilbert
proofs, all objects are projected onto a single kind `k`. (Kind inference is
expected to be added in the future.)

The leveldb is a simply key-value store; the key for each Fact is its Core, as above, plus the sha1sum of its JSON contents. A Fact's proof is verified as it is added to the database; its entry never changes and need never be deleted. Multiple proofs of a Fact can happily exist side-by-side; one or another may be chosen for a particular query based on a variety of scoring algorithms. This database should scale well to many millions of Facts, and could easily be sharded across machines.



