# MINIMUM BISECTION on 3-regular graphs is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a simple graph $G$ on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops in which every vertex has degree exactly $3$ (so $n$ is even), and a bound $K$, decide whether the vertices split into two sets of $n / 2$ vertices each with at most $K$ edges between them. Both problems decode the same triples $(n, E, K)$, and the yes-instances of this problem are exactly the yes-instances of MINIMUM BISECTION whose graph is 3-regular.

## Sources

- T. N. Bui, S. Chaudhuri, F. T. Leighton and M. Sipser, "Graph bisection algorithms with good average case behavior", Combinatorica 7(2) (1987), 171-191, doi:10.1007/BF02579448.
- L. Lichev and D. Mitsche, "On the minimum bisection of random 3-regular graphs", The Electronic Journal of Combinatorics 30(2) (2023), doi:10.37236/11085, Section 1.
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND17] MINIMUM CUT INTO BOUNDED SETS.
