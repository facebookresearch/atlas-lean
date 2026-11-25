# 3-DIMENSIONAL MATCHING for pairwise consistent triples is NP-complete

The 3-DIMENSIONAL MATCHING for pairwise consistent triples decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a set `M ⊆ W × X × Y`, where `W`, `X`, and `Y` are disjoint sets having the same number `q` of elements, such that `M` is pairwise consistent: for all elements `a`, `b`, `c`, whenever there exist elements `w`, `x`, and `y` such that `(a, b, w) ∈ M`, `(a, x, c) ∈ M`, and `(y, b, c) ∈ M`, then `(a, b, c) ∈ M`. Question: does `M` contain a matching, i.e., a subset `M' ⊆ M` such that `|M'| = q` and no two elements of `M'` agree in any coordinate?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP1] 3-DIMENSIONAL MATCHING, comment, and the transformation from 3SAT in Section 3.1.2.
