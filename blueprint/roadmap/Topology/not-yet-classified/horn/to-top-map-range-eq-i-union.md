# To Top map ι range eq i Union

Realized horn inclusion range as a union of realized face ranges.

For `k : Fin (n + 2)`, the horn over `Λ[n+1, k]` is the multicoequalizer of its
singleton-complement faces (`SSet.horn.multicoequalizerDiagram` and
`SSet.horn.isColimit`). Realization preserves this colimit, so joint surjectivity
of the realized legs exhibits every realized horn point in some realized face range;
each face range in turn sits in the horn range via `SSet.horn.faceι_ι`. This is a
range computation only, not a filling, anodyne, retract, product, or
model-category claim.
