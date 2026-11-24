# ZERO FORCING NUMBER as a decision problem

The decision problem ZERO FORCING NUMBER accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$ (a natural number, a list of pairs of natural numbers and a natural number), to an instance that is well-formed as a GRAPH COLORING instance (the list $E$ has no repeated entries, and every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$) and feasible for ZERO FORCING NUMBER. It rejects every bitstring that does not decode to such an instance.
