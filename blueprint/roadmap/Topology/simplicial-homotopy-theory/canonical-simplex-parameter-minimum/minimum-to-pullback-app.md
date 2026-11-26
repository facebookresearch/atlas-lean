# Components of the external-coordinate comparison

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, and `p : Fin (L.len + 1) × Fin (q.len + 1)`,
`(minimumToPullback τ ρ).app p = homOfLE (minimum_le_pullback τ ρ p)`.
This is the unique preorder arrow from the minimum coordinates to the coordinates with external parameter `p.2`.
