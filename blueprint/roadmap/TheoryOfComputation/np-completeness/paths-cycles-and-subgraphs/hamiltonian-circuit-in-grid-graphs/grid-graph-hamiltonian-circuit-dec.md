# HAMILTONIAN CIRCUIT IN GRID GRAPHS as a decision problem

The decision problem HAMILTONIAN CIRCUIT IN GRID GRAPHS accepts a bitstring $x$ exactly when $x$
decodes, under the canonical bitstring encoding of its instances, to an instance that is
[well-formed](well-formed.md) and whose [grid graph](to-hamiltonian-instance.md) has a
Hamiltonian cycle in the sense of [HAMILTONIAN
CYCLE](../undirected-hamiltonian-cycle/hamiltonian-cycle-undirected-feasible.md). It rejects
every bitstring that does not decode to an instance.
