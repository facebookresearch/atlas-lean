# Inverse coordinates of a differential-variable word

Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. Let `M` have `k`- and `A`-module structures with commuting actions
and scalar tower `k → A → M` (`SMulCommClass k A M` and `IsScalarTower k A M`). For `n : ℕ`,
`m : M`, and `f : Fin n → σ`, the inverse comparison sends `m ⊗ (dX_(f 0) ∧ ⋯ ∧ dX_(f (n-1)))`
to `m ⊗ (e_(f 0) ∧ ⋯ ∧ e_(f (n-1)))`, where `e_i = single i 1`. The empty wedge is `1` when `n
= 0`.
