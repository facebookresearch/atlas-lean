# 2-DIMENSIONAL CONSECUTIVE SETS with sets of size at most 5 is NP-complete

The 2-DIMENSIONAL CONSECUTIVE SETS with sets of size at most 5 decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a finite alphabet `Σ` and a collection `C = {Σ₁, Σ₂, ..., Σₙ}` of subsets of `Σ` with `|Σⱼ| ≤ 5` for every `Σⱼ ∈ C`. Question: is there a partition of `Σ` into disjoint sets `X₁, X₂, ..., X_k` such that each `Xᵢ` has at most one element in common with each `Σⱼ` and such that, for each `Σⱼ ∈ C`, there is an index `l(j)` such that `Σⱼ` is contained in `X_{l(j)} ∪ X_{l(j)+1} ∪ ... ∪ X_{l(j)+|Σⱼ|-1}`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR19] 2-DIMENSIONAL CONSECUTIVE SETS, p. 230, comment: "Remains NP-complete if all `Σⱼ ∈ C` have `|Σⱼ| ≤ 5`, but is solvable in polynomial time if all `Σⱼ ∈ C` have `|Σⱼ| ≤ 2`" (the entry's reference is [Lipsky, 1977b]).
- W. Lipski, Jr., "One more polynomial complete consecutive retrieval problem", Information Processing Letters 6 (1977), 91-93, doi:10.1016/0020-0190(77)90034-5.
