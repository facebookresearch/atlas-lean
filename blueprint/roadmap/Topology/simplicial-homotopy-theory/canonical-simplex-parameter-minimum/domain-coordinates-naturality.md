# Naturality of coordinates from two source maps

For ordinal maps `τ : L ⟶ m`, `ρ : L ⟶ q`, `τ' : L' ⟶ m'`, `ρ' : L' ⟶ q'`, `δ : L' ⟶ L`, `γ : m' ⟶ m`, and `α : q' ⟶ q`, suppose `δ ≫ τ = τ' ≫ γ` and `δ ≫ ρ = ρ' ≫ α`. Then
`(domainCoordinates τ ρ).comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) = (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp (domainCoordinates τ' ρ')`.
This is an equality of monotone maps between the indicated finite product ordinals.
