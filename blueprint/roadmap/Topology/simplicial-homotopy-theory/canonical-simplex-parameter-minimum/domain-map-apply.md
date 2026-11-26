# Simplex formula through two source maps

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, `a : SimplexCategoryᵒᵖ`, and `p ∈ (stdSimplex.obj L ⊗ stdSimplex.obj q : SSet.{u}).obj a`,
`(domainMap τ ρ).app a p = ((stdSimplex.map τ).app a p.1, (stdSimplex.map ρ).app a p.1)`.
Both output simplices depend on the first input simplex.
