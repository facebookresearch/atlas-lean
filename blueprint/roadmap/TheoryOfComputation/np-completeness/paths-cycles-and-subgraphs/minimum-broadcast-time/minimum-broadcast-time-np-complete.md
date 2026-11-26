# MINIMUM BROADCAST TIME is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a simple graph on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops, a list $V_0$ of distinct vertices and a positive integer $K$, decide whether information held by the vertices of $V_0$ can reach every vertex in $K$ rounds, where in each round every informed vertex may pass it along one edge to an uninformed neighbor and no vertex is informed twice in a round.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND49] MINIMUM BROADCAST TIME (credited there to Garey and Johnson, unpublished: transformation from 3DM).
- P. J. Slater, E. J. Cockayne and S. T. Hedetniemi, "Information dissemination in trees", SIAM Journal on Computing 10 (1981), 692-701, doi:10.1137/0210052.
