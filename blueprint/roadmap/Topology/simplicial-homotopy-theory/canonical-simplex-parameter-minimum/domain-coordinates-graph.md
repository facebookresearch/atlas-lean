# Source coordinates agree with pullback coordinates on a split graph

Let `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, and `κ : q ⟶ L` satisfy `κ ≫ ρ = 𝟙 q`. For every `k : Fin (q.len + 1)`,
`domainCoordinates τ ρ (κ.toOrderHom k, k) = pullbackCoordinates τ (κ.toOrderHom k, k)`.
The two parameter coordinates agree because `ρ(κ(k)) = k`.
