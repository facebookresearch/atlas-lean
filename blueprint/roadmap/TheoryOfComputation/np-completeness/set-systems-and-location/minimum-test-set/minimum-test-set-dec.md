# The MINIMUM TEST SET decision problem

It accepts a bitstring $x$ exactly when $x$ decodes,
under the canonical bitstring encoding, to a triple $(n, C, K)$ of a natural number $n$, a list
$C$ of lists of natural numbers (the tests) and a natural number $K$ with the following
properties: every test is a list of numbers below $n$ without repeated entries, and some sublist
$T$ of $C$, obtained by deleting entries of $C$, has length at most $K$ and distinguishes every
pair, that is, for all distinct $a, b < n$ some test in $T$ contains exactly one of $a$ and $b$.
Bitstrings that do not decode are rejected.
