# INDEPENDENT SET ON 2-DIR GRAPHS as a decision problem

The decision problem INDEPENDENT SET ON 2-DIR GRAPHS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$ (a natural number, a list of pairs of natural numbers and a natural number), to an instance that is well-formed for INDEPENDENT SET ON 2-DIR GRAPHS and feasible: some set of at least $K$ vertices contains no two adjacent vertices. It rejects every bitstring that does not decode to such an instance.
