# Coordinate formula for two source maps

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, and `p : Fin (L.len + 1) × Fin (q.len + 1)`,
`domainCoordinates τ ρ p = (τ.toOrderHom p.1, ρ.toOrderHom p.1)`.
