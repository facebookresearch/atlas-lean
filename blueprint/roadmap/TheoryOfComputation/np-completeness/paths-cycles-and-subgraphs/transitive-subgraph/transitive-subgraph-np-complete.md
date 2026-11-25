# TRANSITIVE SUBGRAPH is NP-complete

The TRANSITIVE SUBGRAPH decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a directed graph `G = (V, A)` (no loops, no multiple arcs) and a positive integer `K ≤ |A|`. Question: is there a subset `A' ⊆ A` with `|A'| ≥ K` such that `G' = (V, A')` is transitive, i.e., `(u, v) ∈ A'` and `(v, w) ∈ A'` imply `(u, w) ∈ A'`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT29] TRANSITIVE SUBGRAPH.
- M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264, doi:10.1145/800133.804355.
- journal version: M. Yannakakis, "Edge-deletion problems", SIAM Journal on Computing 10 (1981), 297-309, doi:10.1137/0210021.
