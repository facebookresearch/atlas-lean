# Naturality of minimum parameter coordinates

For ordinal maps `τ : L ⟶ m`, `ρ : L ⟶ q`, `τ' : L' ⟶ m'`, `ρ' : L' ⟶ q'`, `δ : L' ⟶ L`, `γ : m' ⟶ m`, and `α : q' ⟶ q`, suppose `δ ≫ τ = τ' ≫ γ` and `δ ≫ ρ = ρ' ≫ α`. Then
`(minimumCoordinates τ ρ).comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) = (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp (minimumCoordinates τ' ρ')`.
The parameter map `α` may be noninjective; monotone maps of finite linear orders preserve minima.
