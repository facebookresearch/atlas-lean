# Coefficient-first polynomial form coordinates

Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. Let `M` have `k`- and `A`-module structures with commuting actions
and scalar tower `k → A → M` (`SMulCommClass k A M` and `IsScalarTower k A M`). For each `n :
ℕ`, this is the `A`-linear equivalence `M ⊗[k] Λ^n_k V ≃ₗ[A] M ⊗[A] Λ^n_A Ω`. Its pure-word
formula is `m ⊗ ιMulti_k(v) ↦ m ⊗ ιMulti_A(G ∘ v)`, with `G(e_i) = dX_i`.
