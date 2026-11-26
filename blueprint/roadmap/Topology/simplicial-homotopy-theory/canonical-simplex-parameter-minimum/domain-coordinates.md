# Product coordinates from two source maps

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the monotone map `Fin (L.len +
1) × Fin (q.len + 1) →o Fin (m.len + 1) × Fin (q.len + 1)` given by `(x, k) ↦ (τ.toOrderHom x,
ρ.toOrderHom x)`.
