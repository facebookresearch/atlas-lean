# The coefficient is preserved in an exterior word

Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. Let `M` have `k`- and `A`-module structures with commuting actions
and scalar tower `k → A → M` (`SMulCommClass k A M` and `IsScalarTower k A M`). For `n : ℕ`,
`m : M`, and `v : Fin n → V`, the coefficient comparison satisfies `E^M_n(m ⊗ ιMulti_k(v)) = m
⊗ ιMulti_A(fun j ↦ G(v j))`, where `G = mvPolynomialCotangentGenerator k σ`.
