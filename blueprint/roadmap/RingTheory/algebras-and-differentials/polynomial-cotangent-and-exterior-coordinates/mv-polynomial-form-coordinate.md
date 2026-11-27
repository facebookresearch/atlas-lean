# An ordered exterior form coordinate

Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. For `n : ℕ`, the `A`-linear map `π_s : Λ^n_A Ω →
A` is the exterior-basis coordinate at the ordered variable word `dX_(e_s 0) ∧ ⋯ ∧ dX_(e_s
(n-1))`. The empty wedge is `1` when `n = 0`.
