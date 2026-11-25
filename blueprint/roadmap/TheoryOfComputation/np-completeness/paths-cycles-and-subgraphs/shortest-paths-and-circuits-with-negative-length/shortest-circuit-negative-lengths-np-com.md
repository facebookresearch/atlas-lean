# SHORTEST CIRCUIT with negative lengths is NP-complete

The SHORTEST CIRCUIT with negative lengths decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)`, an integer length `l(e) ∈ ℤ` for each `e ∈ E` (negative lengths allowed), and an integer `K`. Question: is there a simple circuit in `G` whose length (the sum of the lengths of its edges) is `K` or less?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND28] LONGEST CIRCUIT, comment (p. 213: "The analogous directed and undirected problems, which ask for a simple circuit of length K or less, can be solved in polynomial time ..., but are NP-complete if negative lengths are allowed"), and problem [GT37] HAMILTONIAN CIRCUIT (all lengths `-1`, `K = -|V|`).
- R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN CIRCUIT is NP-complete).
