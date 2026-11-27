# TREEWIDTH ON CUBIC GRAPHS as a decision problem

The decision problem TREEWIDTH ON CUBIC GRAPHS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$ (a natural number, a list of pairs of natural numbers and a natural number), to an instance that is well-formed for TREEWIDTH ON CUBIC GRAPHS and feasible for TREEWIDTH: the graph has a tree decomposition all of whose bags have at most $K + 1$ vertices. It rejects every bitstring that does not decode to such an instance.
