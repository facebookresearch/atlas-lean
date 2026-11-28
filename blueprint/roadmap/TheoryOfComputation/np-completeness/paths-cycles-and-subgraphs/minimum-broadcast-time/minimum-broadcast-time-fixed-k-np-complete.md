# MINIMUM BROADCAST TIME FOR FIXED K is NP-complete for every fixed K ≥ 4

For every natural number $K \ge 4$, the following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a simple graph on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops, and a list $V_0$ of distinct originators, decide whether information held by $V_0$ can reach every vertex in $K$ rounds, where in each round every informed vertex may pass it along one edge to an uninformed neighbor and no vertex is informed twice in a round.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND49] MINIMUM BROADCAST TIME, p. 219 (comment: "Remains NP-complete for any fixed K ≥ 4"; the entry's reference is [Garey and Johnson, unpublished], "Transformation from 3DM").
