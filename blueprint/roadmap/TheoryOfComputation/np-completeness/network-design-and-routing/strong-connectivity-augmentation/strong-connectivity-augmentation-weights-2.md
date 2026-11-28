# STRONG CONNECTIVITY AUGMENTATION with weights 1 or 2 and no arcs is NP-complete

The STRONG CONNECTIVITY AUGMENTATION with weights 1 or 2 and no arcs decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a directed graph `G = (V, A)` with `A` empty, a weight `w(u, v) ∈ {1, 2}` for each ordered pair `(u, v) ∈ V × V`, and a positive integer `B`. Question: is there a set `A'` of ordered pairs of vertices from `V` such that `∑_{a ∈ A'} w(a) ≤ B` and the graph `G' = (V, A ∪ A')` is strongly connected?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND19] STRONG CONNECTIVITY AUGMENTATION, comment on p. 211 ("Remains NP-complete if all weights are either 1 or 2 and A is empty").
- K. P. Eswaran and R. E. Tarjan, "Augmentation problems", SIAM Journal on Computing 5 (1976), 653-665, doi:10.1137/0205044.
