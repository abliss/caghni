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

# Fingerprints (version "y")

First, define the "lexencode" function on a string argument:
```
  lexencode(S): 'y' + ('+' x len(len(S)))+ (len(S)) + '-' + sha1hex(S)
```

This has the property that lexencode(S) < lexencode(T) If S is shorter than T.

## Basis Fingerprints

A "Basis" is an interface together with all its transitively dependent
interfaces. To make a Basis Fingerprint (BF):

1. Collect all Terms in the Basis; put them (and their FreeMaps) into a global
Term List. Make sure each FreeMap is maximal (no omitted entries, no skipping
null suffixes)

2. Assemble the Cores of all stmts in the Basis as JSONified strings:
[hyps,stmt,dvs]. Within each Core, terms are numbered from 0 as normal. Keep
track of how each Core's terms map to the global Term List.

3. Sort the Core Strings by ASCII order.

4. Rearrange the global Term List by order of first appearance. Reorder the
FreeMaps the same way.

5. Assemble each Core's Term Mapping. The first Core will have [0,1,2,...n] as
its term map. The other Cores could have anything, but each new Term j appears
before Term k iff j<k.

6. create the Basis String BS by JSONifying the array [[[core0,
terms0],[core1,terms1],...[coreN,termsN]],FreeMaps]. (JSON arrays have no
whitespace.)

7. The Basis Fingerprint BF(B) is then `lexencode(BS)`.

8. BFs are to be compared lexically.

9. One Basis "Proves" another, A |- B, if there's a consistent term map M with
which stmts of the Cores of A can prove all stmts of the Cores of B. Some of B's
terms may be null in M, indicating that they are supplied with defthms over A.

10. Two bases are equivalent, A ~ B, If A |- B using M and B |- A using
inv(M). (terms of A unmapped by M become nulls in inv(M) and must be defthm'd.)

11. We maintain a Least Equivalent Basis table, which records A->B (and the
proof of B|-A) anytime A ~ B and B <= C for all C ~ A.

## Term Fingeprints

For each Term T, relative to a given basis B, we can also compute a Term Fingerprint TF(T/B). 

1. If the term is in the basis as term #N, the TF is ('y#'+N). 

2. Otherwise, if the term is given by a defthm D, provable from B, we expand
every non-basis term in the core of D to get a new core C.

3. Assemble the Term Map: for each term in order of appearance in C, put n if it
is term #n in the basis; otherwise put null. There should be exactly one null:
for the definiendum.

4. Assemble the Term String TS by JSONifying the array [C,T].

5. The Term Fingerprint TF(T/B) is then `FreeMap(T)/lexencode(B)/lexencode(TS)`.

6. TFs are to be compared lexically.

7. Relative to a basis B, Two terms T,U are considered equivalent, T~U, if:
  a. If T and U are both in B, only if there Term Numbers are the same, OR if swapping T for U in B gives a new basis C and B ~ C.
  b. If T is term #n in B, and U is a defthm, then only when the Core of U, with the definiendum replaced by n, can be proved from B.
  c. If T and U are both defthms, only when (B + defthm(T)) proves thm(U) and (B + defthm(U)) proves thm(T). In each proof, the same term goes in the definiendum of the defthm() and in *place* of the definiendum in the thm().

8. Terms in different bases: T/A is considered equivalent to term U/B when A~B using a Term Map that maps T to U. 

9. We keep a Least Equivalent Term table which records TF(T/B) -> TF(U/C) whenever T/A ~ U/C.

When a core C can be grounded in a basis B with a Term Map M, each element of M (corresponding to a term T in C) will be a Least Equivalent TF(T/B).

We can then build a Grounding Index by Basis: BF(B)/Core/TermMap -> [[FactFP,
TermMap]]. The last FactFP in the list matches the given Core, and for each fact
F in the list and each dependency D of F, there will be either a matching stmt
in B or a matching [def]thm in the list earlier than F.

When we find that B ~ C and C < B, add BF(C)/Core/TermMap -> [[FactFP, TermMap]], and mark the earlier one as obsolete, entering B->C into the Equivalences table.

Trying to ground a new fact F in a basis B?
1. lookup the Least Known Equivalent Basis C for B, and start off your proof with the recorded proof C|-B.
2. for each dependency D in F, look up TF(C)/D/ and get a list of TermMaps TM(D/C). 
3. Filter for those whose TermMaps all have correct FreeMaps to the ones specified in F.
4. Then a simple search through the permutations should(TODO?) tell you whether there is a consistent global TermMap. 
5. If you find one, merge the fact-lists and record it in the Grounding Index.
6. If you don't, optionally try to discover new groundings for some of the missing dependencies. 
7. (TODO: cache failure in the Grounding Index table by global DB hash? only retry by focusing on newly-proven theorems since the last failure?)
