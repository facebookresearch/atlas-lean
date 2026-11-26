# Coefficient variable words become forms

Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. Let `M` have `k`- and `A`-module structures with commuting actions
and scalar tower `k → A → M` (`SMulCommClass k A M` and `IsScalarTower k A M`). For `n : ℕ`,
`m : M`, and any `f : Fin n → σ`, the coefficient comparison sends `m ⊗ (e_(f 0) ∧ ⋯ ∧ e_(f
(n-1)))` to `m ⊗ (dX_(f 0) ∧ ⋯ ∧ dX_(f (n-1)))`. The empty wedge is `1` when `n = 0`.
