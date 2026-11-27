# Differential coordinates are Jacobian determinants

Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. For `n : ℕ` and `f : Fin n → A`, the coordinate
satisfies `π_s(df_0 ∧ ⋯ ∧ df_(n-1)) = det(∂f_i/∂X_(e_s j))`. Rows are indexed by the
differentials `f_i` and columns by the ordered variables `e_s j`. The empty wedge is `1` when
`n = 0`.
