# LINEAR ORDERING (TOURNAMENTS) as a decision problem

The decision problem LINEAR
ORDERING (TOURNAMENTS) accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of triples of a natural number, a list of pairs of natural numbers and a
natural number, to an instance $(n, E, K)$ that is well formed ($n > 0$ and $E$ is a tournament
on the vertices $0, \dots, n - 1$ without repeated arcs) and feasible (some ordering of the
vertices has at least $K$ arcs of $E$ going forward). Bitstrings that do not decode, or that
decode to a malformed instance, are rejected.
