# WEIGHTED RADIUS WITH LENGTHS 0 AND 1 is NP-complete for K = 1

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a simple graph on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops, and a list $C$ of edge lengths, each $0$ or $1$, with one length per edge, decide whether the lengths can be assigned to the edges, one to each, so that some vertex is within weighted distance $1$ of every vertex.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER (p. 205), comment "If C consists entirely of 0's and 1's, then both the diameter and radius versions are solvable in polynomial time for trees, but are NP-complete for general graphs, even if K is fixed at 2 (diameter) or 1 (radius)" (credited there to Perl and Zaks, 1978).
- Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical Computer Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
