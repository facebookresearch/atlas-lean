# FEEDBACK VERTEX SET ON BIPARTITE PLANAR GRAPHS as a decision problem

The decision problem FEEDBACK VERTEX SET ON BIPARTITE PLANAR GRAPHS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$ (a natural number, a list of pairs of natural numbers and a natural number), to an instance that is well-formed for FEEDBACK VERTEX SET ON BIPARTITE PLANAR GRAPHS and feasible for FEEDBACK VERTEX SET: deleting some set of at most $K$ vertices leaves an acyclic graph (a forest). It rejects every bitstring that does not decode to such an instance.
