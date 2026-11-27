# Path Space eval₀ eq

The landed source evaluation `SSet.eval₀` on `pathSpace X` is
precomposition with `stdSimplex.δ 1 : Δ[0] ⟶ Δ[1]` (the inclusion
of vertex `0`), followed by evaluation at `Δ[0]`. The body of
`eval₀` is not exposed across modules, so this is proved from its
public characterization `comp_eval₀_eq_ι₀_braiding_uncurry`.
