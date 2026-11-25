# Is Colimit of forget is Colimit

The forgetful functor reflects colimits of diagrams indexed by a
nonempty shape: a cocone in `SSet(O)` whose underlying cocone in
`SSet` is a colimit cocone is a colimit cocone. The mediating
simplicial map is compatible with the vertex identifications because
any single cocone leg is surjective (indeed bijective) on vertices.
As for limits, reflection needs only a nonempty shape, whereas
colimits themselves are computed in `SSet` only over nonempty
connected shapes — the initial object and binary coproducts are not
(see the module docstring).
