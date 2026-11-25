# Exists is Pushout of lt with witness

Bounded one-cell attachment with explicit minimal witness.

Same orientation as `exists_isPushout_of_lt`: `IsPushout t (boundary n).ι
(homOfLE hAB.le) b` with `n` the `Nat.find` minimal missing dimension, `x` the
witnessing nondegenerate cell, `hJoin : B = A ⊔ ofSimplex x.1`, and `hMin` its
minimality. For `X := Δ[N]`, `A := boundary N`, `J := ⊤`, dimension bounds
(`dim_le_of_nonDegenerate`, `boundary_obj_eq_univ`) force `n = N`, and
`nonDegenerate_top_dim` identifies `x`; compose with
`sup_ofSimplex_top_eq_top`/`attachment_apex_eq_top` where the import layer
permits. No realized-boundary-range/complement equality, openness,
collar/shrink/chart/Serre/fibration/model, arbitrary product preservation, or
KQ3 claim.
