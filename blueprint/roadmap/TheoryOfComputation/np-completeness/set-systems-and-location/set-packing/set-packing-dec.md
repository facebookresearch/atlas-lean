# The SET PACKING decision problem

SET PACKING is the decision problem that accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a set-packing
instance $(n, C, K)$ that is both well formed and feasible: every list in $C$ has no repeated
entries and only entries less than $n$, and some sublist of $C$ with no repeated entries and at
least $K$ entries has no element in common between any two of its distinct entries. Bitstrings
that do not decode to a set-packing instance are rejected.
