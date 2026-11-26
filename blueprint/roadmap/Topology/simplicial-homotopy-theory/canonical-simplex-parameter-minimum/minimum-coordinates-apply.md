# Coordinate formula for the minimum parameter

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, and `p : Fin (L.len + 1) × Fin (q.len + 1)`,
`minimumCoordinates τ ρ p = (τ.toOrderHom p.1, min (ρ.toOrderHom p.1) p.2)`.
