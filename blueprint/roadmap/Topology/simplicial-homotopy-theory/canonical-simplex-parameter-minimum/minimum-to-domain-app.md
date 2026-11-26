# Components of the source-coordinate comparison

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, and `p : Fin (L.len + 1) × Fin (q.len + 1)`,
`(minimumToDomain τ ρ).app p = homOfLE (minimum_le_domain τ ρ p)`.
The component is the unique arrow in the componentwise preorder category from the minimum coordinates to the source-parameter coordinates.
