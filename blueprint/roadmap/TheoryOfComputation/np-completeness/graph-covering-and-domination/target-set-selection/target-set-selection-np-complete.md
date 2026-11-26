# TARGET SET SELECTION is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a simple graph on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops, a positive threshold $t(v)$ for every vertex $v$ and an integer $K$ with $0 < K \le n$, decide whether some set of at most $K$ initially active vertices eventually activates every vertex, when in each round every vertex with at least $t(v)$ active neighbors becomes active.

## Sources

- P. A. Dreyer Jr. and F. S. Roberts, "Irreversible k-threshold processes: graph-theoretical threshold models of the spread of disease and of opinion", Discrete Applied Mathematics 157(7) (2009), 1615-1627, doi:10.1016/j.dam.2008.09.012.
- N. Chen, "On the approximability of influence in social networks", SIAM Journal on Discrete Mathematics 23(3) (2009), 1400-1415, doi:10.1137/08073617X.
- J. Kynčl, B. Lidický and T. Vyskočil, "Irreversible 2-conversion set in graphs of bounded degree", Discrete Mathematics & Theoretical Computer Science 19(3) (2017), doi:10.23638/DMTCS-19-3-5.
