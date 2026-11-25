# Discrete SSet

The discrete simplicial set on a type `S`: its simplices in every
degree are the elements of `S` (the constant simplices), and every
simplicial operator is the identity. This is the constant functor
`(Functor.const SimplexCategoryᵒᵖ).obj S`, i.e. the constant
presheaf on `S`. The definitional equalities
`discreteSSet_obj`/`discreteSSet_map_apply` below hold by `rfl` for
this model, as they did for the previous hand-built one.
