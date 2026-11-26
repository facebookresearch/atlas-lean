# Product coordinates with the minimum parameter

For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the monotone map from `Fin
(L.len + 1) × Fin (q.len + 1)` to `Fin (m.len + 1) × Fin (q.len + 1)` sending `(x, k)` to
`(τ.toOrderHom x, min (ρ.toOrderHom x) k)`.
