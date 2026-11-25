# Ihom Vertex Equiv

The vertex dictionary for an internal hom of simplicial sets: vertices
of `(ihom X).obj C` are exactly the maps `X ⟶ C`. This is the composite of
`MonoidalClosed.curryHomEquiv'` (maps out of the tensor unit into an
internal hom) with `SSet.unitHomEquiv` (maps out of the tensor unit are
vertices).
