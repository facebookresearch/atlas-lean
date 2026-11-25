# STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES is NP-complete

The STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: finite sets `F` and `P` of function and predicate symbols, a set `G` of "defined" function symbols disjoint from `F`, a specified symbol `f₀ ∈ G`, and two linear monadic recursion schemes `S₁` and `S₂`, each consisting of a defining statement for each `f ∈ G` of the form `fx = if px then αx else βx`, where `p ∈ P`, `α, β ∈ (F ∪ G)*`, and `α` and `β` each contain at most one occurrence of a symbol from `G`. Question: is there a domain set `D`, an interpretation of each `f ∈ F` as a function `f : D → D`, an interpretation of each `p ∈ P` as a function `p : D → {T, F}`, and an initial value `x₀ ∈ D` such that, as defined by the recursion schemes `S₁` and `S₂`, either the two values for `f₀(x₀)` differ or one is defined and the other isn't?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO17] STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES, p. 277 (reference [Constable, Hunt, and Sahni, 1974]; transformation from STRONG INEQUIVALENCE OF IANOV SCHEMES).
- R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031 (journal version of the 1974 Cornell report GJ cites: strong equivalence of linear monadic recursion schemes is NP-complete).
