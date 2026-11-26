# Map of product simplices using the minimum parameter

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the simplicial map
`minimumMap τ ρ : stdSimplex.obj L ⊗ stdSimplex.obj q ⟶ stdSimplex.obj m ⊗ stdSimplex.obj q`
in universe `u` is induced by `(x, k) ↦ (τ.toOrderHom x, min (ρ.toOrderHom x) k)` on the product ordinals.
