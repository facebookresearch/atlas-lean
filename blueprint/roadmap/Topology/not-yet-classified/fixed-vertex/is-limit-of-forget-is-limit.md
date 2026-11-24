# Is Limit of forget is Limit

The forgetful functor reflects limits of diagrams indexed by a
nonempty shape: a cone in `SSet(O)` whose underlying cone in `SSet`
is a limit cone is a limit cone. Indeed the mediating simplicial map
is automatically compatible with the vertex identifications, by
compatibility of any single cone leg, and uniqueness follows from
faithfulness. This is the precise form, at the level of reflection,
of Stevenson's "limits are computed in `sSet`" (arXiv:1810.05233,
§5.3): reflection needs only a nonempty shape, whereas limits
themselves are computed in `SSet` only over nonempty connected
shapes — the terminal object and binary products are not (see the
module docstring).
