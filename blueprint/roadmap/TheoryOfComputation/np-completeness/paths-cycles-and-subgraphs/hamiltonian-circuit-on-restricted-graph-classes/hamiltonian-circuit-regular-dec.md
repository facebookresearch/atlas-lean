# HAMILTONIAN CIRCUIT ON k-REGULAR GRAPHS as a decision problem

Fix a natural number $k$. The decision problem HAMILTONIAN CIRCUIT ON $k$-REGULAR GRAPHS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs $(n, E)$ (a natural number and a list of pairs of natural numbers), to an instance that is well-formed for HAMILTONIAN CIRCUIT ON $k$-REGULAR GRAPHS and feasible for HAMILTONIAN CIRCUIT: $n \ge 3$ and the graph has a Hamiltonian cycle, a cycle through every vertex exactly once. It rejects every bitstring that does not decode to such an instance.
