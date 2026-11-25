# SHIFT BRIBERY for Borda is NP-complete

The SHIFT BRIBERY for Borda decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: an election `E = (C, V)` with candidates `C = {c₁, …, cₘ}`, a preferred candidate `p ∈ C`, and voters `V = (v₁, …, vₙ)`, each a strict linear order over `C`; for each voter `vᵢ` a shift-bribery price function `ρᵢ : ℕ → ℕ ∪ {+∞}`, i.e., if `p` appears in the `j`-th position of `vᵢ`, then `ρᵢ(0) = 0`, `ρᵢ(k) ≤ ρᵢ(k')` for `k < k' < j`, and `ρᵢ(k) = +∞` for `k ≥ j`; and a nonnegative integer `B` (the budget). Question: is there a sequence `(k₁, …, kₙ)` of nonnegative integers such that `∑ᵢ ρᵢ(kᵢ) ≤ B` and bribing each voter `vᵢ` to shift `p` up by `kᵢ` places ensures that `p` is a Borda winner of the resulting election?

## Sources

- E. Elkind, P. Faliszewski and A. Slinko, "Swap bribery", Algorithmic Game Theory (SAGT 2009), Lecture Notes in Computer Science 5814, Springer (2009), 299-310, doi:10.1007/978-3-642-04645-2_27 (arXiv:0905.3885), Definition 3.7 and Theorem 5.1.
