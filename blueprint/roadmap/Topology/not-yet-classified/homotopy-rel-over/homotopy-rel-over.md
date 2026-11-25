# Homotopy Rel Over

A homotopy relative to `A : X.Subcomplex` that lies over a fixed `p : Y ⟶ S`.

For `f g : X ⟶ Y`, a witness `H : HomotopyRelOver p f g A` consists of an
underlying relative homotopy `H.toHomotopyRel : HomotopyRel f g A` with homotopy
`h : X ⊗ Δ[1] ⟶ Y` satisfying `h ≫ p = fst ≫ (f ≫ p)`. Stationarity on `A`
is inherited from `HomotopyRel`. The equation implies `f ≫ p = g ≫ p`. This is
the simplicial analogue of a homotopy over a base, used for fiberwise homotopy
in the minimal-fibration development.
