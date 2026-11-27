# A Jacobian determinant acts on the coefficient

Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. Let `M` be an `A`-module. For `m : M` and `f :
Fin n → A`, the coefficient coordinate satisfies `κ_s(m ⊗ (df_0 ∧ ⋯ ∧ df_(n-1))) =
det(∂f_i/∂X_(e_s j)) • m`, with rows indexed by `i` and ordered variable columns by `j`. The
empty wedge is `1` when `n = 0`.
