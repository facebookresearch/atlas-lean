# Second coordinate of the minimum simplex map

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, `a : SimplexCategoryᵒᵖ`, `p ∈ (stdSimplex.obj L ⊗ stdSimplex.obj q : SSet.{u}).obj a`, and `i : Fin (a.unop.len + 1)`,
`asOrderHom (((minimumMap τ ρ).app a p).2) i = min (ρ.toOrderHom (asOrderHom p.1 i)) (asOrderHom p.2 i)`.
The second output simplex is the pointwise minimum of the source parameter and the independent input parameter.
