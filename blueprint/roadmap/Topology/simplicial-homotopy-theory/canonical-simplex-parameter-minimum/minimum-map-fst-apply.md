# First coordinate of the minimum simplex map

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, `a : SimplexCategoryᵒᵖ`, and `p ∈ (stdSimplex.obj L ⊗ stdSimplex.obj q : SSet.{u}).obj a`,
`((minimumMap τ ρ).app a p).1 = (stdSimplex.map τ).app a p.1`.
Taking the minimum in the parameter coordinate leaves this source-map coordinate unchanged.
