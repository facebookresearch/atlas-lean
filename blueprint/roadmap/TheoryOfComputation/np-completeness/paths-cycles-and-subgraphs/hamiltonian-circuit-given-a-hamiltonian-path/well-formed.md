# Well-formed HAMILTONIAN CIRCUIT given a Hamiltonian path instances

A HAMILTONIAN CIRCUIT given a Hamiltonian path instance is well-formed when at least one vertex
(a path has one), the edge list describes a simple graph (no duplicate edges in either
orientation, no self-loops, endpoints in range), and the given list is a Hamiltonian path of it:
it lists `n` distinct vertices, each `< n` (so every vertex exactly once), and consecutive
entries are joined by an edge.
