# UNICONNECTED SUBGRAPH is NP-complete

The UNICONNECTED SUBGRAPH decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a directed graph `G = (V, A)` (no loops, no multiple arcs) and a positive integer `K ≤ |A|`. Question: is there a subset `A' ⊆ A` with `|A'| ≥ K` such that `G' = (V, A')` has at most one directed path between any pair of vertices?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT30] UNICONNECTED SUBGRAPH.
- S. N. Maheshwari, "Traversal marker placement problems are NP-complete", Technical Report CU-CS-092-76, Department of Computer Science, University of Colorado, Boulder (1976), Lemma 1, https://scholar.colorado.edu/concern/reports/rb68xc64n.
