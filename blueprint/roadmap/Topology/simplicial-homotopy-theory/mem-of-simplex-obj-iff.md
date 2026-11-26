# Membership in a generated product-simplex subcomplex

Let `p, q, n, m : ℕ`, let `s` be an `n`-simplex of `Δ[p] ⊗ Δ[q] : SSet.{u}`, and let `t` be an
`m`-simplex of the same product. Then `s ∈ (Subcomplex.ofSimplex t).obj _` if and only if
`Set.range (objEquiv s) ⊆ Set.range (objEquiv t)`, where `objEquiv` associates to a simplex
its monotone map into `Fin (p + 1) × Fin (q + 1)`.
