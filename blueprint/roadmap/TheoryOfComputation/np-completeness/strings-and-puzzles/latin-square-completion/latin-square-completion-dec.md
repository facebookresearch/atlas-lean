# LATIN SQUARE COMPLETION as a decision problem

The decision problem LATIN SQUARE
COMPLETION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding of pairs of a natural number and a list of lists of natural numbers, to an instance
$(n, G)$ that is well formed ($n > 0$ and $G$ consists of $n$ rows of length $n$ with entries at
most $n$) and feasible ($G$ can be completed to an $n \times n$ grid whose rows and columns are
permutations of $1, \dots, n$ and which agrees with $G$ on its nonzero entries). Bitstrings that
do not decode, or that decode to a malformed instance, are rejected.
