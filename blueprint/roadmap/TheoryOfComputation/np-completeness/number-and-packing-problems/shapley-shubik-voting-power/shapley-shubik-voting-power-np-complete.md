# SHAPLEY-SHUBIK VOTING POWER is NP-complete

The SHAPLEY-SHUBIK VOTING POWER decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: an ordered set `V = {v₁, ..., vₙ}` of voters, a number of votes `w(vᵢ) ∈ ℤ⁺` for each voter, and a quota `q ∈ ℤ⁺`. Question: does voter `v₁` have nonzero Shapley-Shubik voting power, i.e., is there an ordering of the voters in which `v₁` is pivotal: the voters before `v₁` have fewer than `q` votes in total, and together with `v₁` they have at least `q`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS8] SHAPLEY-SHUBIK VOTING POWER.
- Y. Matsui and T. Matsui, "NP-completeness for calculating power indices of weighted majority games", Theoretical Computer Science 263 (2001), 305-310, doi:10.1016/S0304-3975(00)00251-6 (Theorem 3, problem SS1).
