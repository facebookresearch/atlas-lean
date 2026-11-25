# 3-DIMENSIONAL MATCHING with at most three occurrences per element is NP-complete

The 3-DIMENSIONAL MATCHING with at most three occurrences per element decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a set `M ⊆ W × X × Y`, where `W`, `X` and `Y` are disjoint sets having the same number `q` of elements, such that no element of `W ∪ X ∪ Y` occurs in more than three triples of `M`. Question: does `M` contain a matching, that is, a subset `M' ⊆ M` with `|M'| = q` such that no two elements of `M'` agree in any coordinate?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP1] 3-DIMENSIONAL MATCHING, p. 221, comment: "Also remains NP-complete if no element occurs in more than three triples, but is solvable in polynomial time if no element occurs in more than two triples [Garey and Johnson, ——]" (unpublished; the result and its attribution are those recorded by Garey and Johnson).
- M. E. Dyer and A. M. Frieze, "Planar 3DM is NP-complete", Journal of Algorithms 7(2) (1986), 174-184, doi:10.1016/0196-6774(86)90002-7.
