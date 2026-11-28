# H-MATCHING is NP-complete

Let $H$ be a pattern graph on $\{0, \dots, m-1\}$ with a simple edge list (no duplicate edges in
either orientation, no loops, endpoints less than $m$) that has a connected component with at
least $3$ vertices. Then the decision problem [H-MATCHING](h-matching-dec.md) for $H$ belongs to
NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem MAXIMUM H-MATCHING (the decision version of the optimization problem stated here).
- D. G. Kirkpatrick and P. Hell, "On the completeness of a generalized matching problem", Proceedings of the 10th Annual ACM Symposium on Theory of Computing (1978), 240-245, doi:10.1145/800133.804353.
- D. G. Kirkpatrick and P. Hell, "On the complexity of general graph factor problems", SIAM Journal on Computing 12(3) (1983), 601-609, doi:10.1137/0212040.
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), comment to problem [GT12] PARTITION INTO ISOMORPHIC SUBGRAPHS.
