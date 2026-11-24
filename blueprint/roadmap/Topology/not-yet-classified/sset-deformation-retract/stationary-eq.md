# Stationary eq

Categorical form of `HomotopyRel.stationary`: the homotopy is constant on `S`
in the interval direction.

For `H : HomotopyRel f g S`, whiskering the inclusion `S.ι` with `Δ[1]`
followed by `H.h` equals the first projection followed by the inclusion and `f`:

`(S.ι ▷ Δ[1]) ≫ H.h = fst S Δ[1] ≫ S.ι ≫ f`.

This is the natural-transformation equality underlying the pointwise
stationarity condition, formulated for rewriting with `Functor.map_comp`.
