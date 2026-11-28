# HAMILTONIAN PATH IN GRID GRAPHS as a decision problem

The decision problem HAMILTONIAN PATH IN GRID GRAPHS accepts a bitstring $x$ exactly when $x$
decodes, under the canonical bitstring encoding of its instances, to an instance that is
[well-formed](well-formed.md) and whose [grid
graph](../hamiltonian-circuit-in-grid-graphs/to-hamiltonian-instance.md) has a Hamiltonian path
in the sense of [HAMILTONIAN
PATH](../undirected-hamiltonian-path/hamiltonian-path-undirected-feasible.md). It rejects every
bitstring that does not decode to an instance.
