# HAMILTONIAN PATH on strongly chordal split graphs is NP-complete

The HAMILTONIAN PATH on strongly chordal split graphs decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)` that is both a split graph (its vertex set can be partitioned into a clique and an independent set) and strongly chordal (every cycle of length at least `4` has a chord, and every cycle of even length at least `6` has an odd chord, an edge joining two vertices of the cycle at odd distance greater than `1` along the cycle). Question: does `G` contain a Hamiltonian path, that is, a simple path through every vertex (endpoints not specified)?

## Sources

- H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996), 291-298, doi:10.1016/0012-365X(95)00057-4.
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH.
