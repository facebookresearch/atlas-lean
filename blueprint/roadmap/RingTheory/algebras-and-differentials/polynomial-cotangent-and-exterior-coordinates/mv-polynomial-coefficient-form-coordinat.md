# An exterior coordinate with coefficients

Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. Let `M` be an `A`-module. The `A`-linear
coefficient coordinate `κ_s : M ⊗[A] Λ^n_A Ω → M` sends `m ⊗ ω` to `π_s(ω) • m`, where `π_s`
is the ordered exterior form coordinate.
