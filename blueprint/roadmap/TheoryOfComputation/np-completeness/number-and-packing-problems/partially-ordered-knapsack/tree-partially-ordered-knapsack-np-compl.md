# PARTIALLY ORDERED KNAPSACK with a tree order is NP-complete

The PARTIALLY ORDERED KNAPSACK with a tree order decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a finite set `U`, a tree partial order `<` on `U`, for each `u ∈ U` a size `s(u) ∈ ℤ⁺` and a value `v(u) ∈ ℤ⁺`, and positive integers `B` and `K`. Question: is there a subset `U' ⊆ U` such that if `u ∈ U'` and `u' < u`, then `u' ∈ U'`, and such that `∑_{u ∈ U'} s(u) ≤ B` and `∑_{u ∈ U'} v(u) ≥ K`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP12] PARTIALLY ORDERED KNAPSACK, pp. 247-248 (comment: "General problem is solvable in pseudo-polynomial time if < is a "tree" partial order [Garey and Johnson, ——].").
- D. S. Johnson and K. A. Niemi, "On knapsacks, partitions, and a new dynamic programming technique for trees", Mathematics of Operations Research 8 (1983), 1-14, doi:10.1287/moor.8.1.1 (abstract: the special case where the order is an out-tree "is still NP-complete").
