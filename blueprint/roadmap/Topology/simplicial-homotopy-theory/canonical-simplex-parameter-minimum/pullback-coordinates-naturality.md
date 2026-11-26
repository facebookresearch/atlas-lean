# Naturality of coordinates with an unchanged parameter

For ordinal maps `τ : L ⟶ m`, `τ' : L' ⟶ m'`, `δ : L' ⟶ L`, `γ : m' ⟶ m`, and `α : q' ⟶ q` in `SimplexCategory`, suppose `δ ≫ τ = τ' ≫ γ`. Then
`(pullbackCoordinates (q := q) τ).comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) = (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp (pullbackCoordinates τ')`.
Thus changing the source and parameter ordinals commutes with applying `τ` to the first coordinate.
