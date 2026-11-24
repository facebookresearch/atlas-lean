# Strong Deformation Retract

A strong deformation retract in `SSet`.

For `f : X ⟶ Y`, a witness consists of a retraction `r : Y ⟶ X`
with `f ≫ r = 𝟙 X` and a homotopy `H : HomotopyRel (𝟙 Y) (r ≫ f) (range f)`
stationary on the simplicial image `range f ≤ Y`.

Orientation follows `TopCat` `StrongDeformationRetract`:
`H 0 = 𝟙 Y`, `H 1 = r ≫ f`, stationary on `Set.range f`.
