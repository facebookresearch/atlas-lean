# PARTITION INTO AT MOST K HAMILTONIAN SUBGRAPHS (UNDIRECTED) is NP-complete

The decision problem PARTITION INTO AT MOST K HAMILTONIAN SUBGRAPHS (UNDIRECTED) belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT13] PARTITION INTO HAMILTONIAN SUBGRAPHS, comment (p. 193: the undirected problem with `|V_i| ≥ 3` is solvable by matching, "However, it becomes NP-complete ... if the instance includes an upper bound K on k"), and problem [GT37] HAMILTONIAN CIRCUIT, the case `K = 1` for nonempty graphs.
- R. M. Karp, "Reducibility among combinatorial problems", in R. E. Miller and J. W. Thatcher (eds.), *Complexity of Computer Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (undirected HAMILTONIAN CIRCUIT is NP-complete).
