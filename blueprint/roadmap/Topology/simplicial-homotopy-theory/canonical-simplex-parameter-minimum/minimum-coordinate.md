# Minimum of the two parameter coordinates

For `L, q : SimplexCategory` and `ρ : L ⟶ q`, the monotone map from `Fin (L.len + 1) × Fin
(q.len + 1)` to `Fin (q.len + 1)` given by `(x, k) ↦ min (ρ.toOrderHom x) k`. It is the
pointwise infimum of `domainCoordinate ρ` and `externalCoordinate`.
