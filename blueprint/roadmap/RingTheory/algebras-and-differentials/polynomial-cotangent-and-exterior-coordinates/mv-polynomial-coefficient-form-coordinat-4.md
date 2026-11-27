# The ordered coefficient wedge has coordinate m

Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. Let `M` be an `A`-module. For every `m : M`,
`κ_s(m ⊗ (dX_(e_s 0) ∧ ⋯ ∧ dX_(e_s (n-1)))) = m`. The empty wedge is `1` when `n = 0`.
