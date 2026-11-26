# Simplex formula with an unchanged parameter

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `a : SimplexCategoryᵒᵖ`, and `p ∈ (stdSimplex.obj L ⊗ stdSimplex.obj q : SSet.{u}).obj a`,
`(pullbackMap τ).app a p = ((stdSimplex.map τ).app a p.1, p.2)`.
The first simplex is mapped by `τ` and the second simplex is retained.
