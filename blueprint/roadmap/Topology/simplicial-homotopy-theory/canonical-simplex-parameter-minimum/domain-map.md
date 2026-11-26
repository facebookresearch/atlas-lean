# Map of product simplices through two source maps

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the simplicial map
`domainMap τ ρ : stdSimplex.obj L ⊗ stdSimplex.obj q ⟶ stdSimplex.obj m ⊗ stdSimplex.obj q`
in universe `u` is induced by `(x, k) ↦ (τ.toOrderHom x, ρ.toOrderHom x)` on the product ordinals.
