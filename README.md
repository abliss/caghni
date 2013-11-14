caghni
======

# Summary

Content-Addressable GHilbert Namespace and Index

The names for theorems in set.mm are too short to be understood by more than a handful of people. The names for theorems in ProofWiki are too long to be remembered, typed, or standardized upon. If I prove a theorem in set.mm and you prove a theorem in ProofWiki, even if they say exactly the same thing and are proved exactly the same way, they will never be part of the same body of interchangeable proofs.

The Ghilbert interface format solves part of the problem, but in an attempt to remain human-readable, has given up solving the hardest part: naming things.

The idea of caghni is to build a Ghilbert-compatable (or nearly-so) convention for naming theorems (and variables, operators, kinds, and interfaces). The goal is to have scripts which can convert a proof in set.mm, or the equivalent proof from ProofWiki, into a caghni repository, where identical proofs map to the same machine-readable object. Other scripts will convert from the universal caghni repository into metamath or ProofWiki, with the ability to add a style layer that assigns readable names (either short ones or long ones as the user prefers). The result will be one big happy family.

# Current Status

A small script is provided which parses a ghilbert module and produces a verifiable output. In version 1, the names of thms, defthms, and stmts are standardized.