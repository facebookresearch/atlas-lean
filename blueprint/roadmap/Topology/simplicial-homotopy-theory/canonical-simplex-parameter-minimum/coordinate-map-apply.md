# Vertex coordinates of an induced simplicial map

Let `f` be a monotone map from the product of the finite ordinals of `p, q : SimplexCategory` to that of `r, s`. For `a : SimplexCategoryᵒᵖ`, a simplex `z` of `stdSimplex.obj p ⊗ stdSimplex.obj q : SSet.{u}` in degree `a`, and `i : Fin (a.unop.len + 1)`,
`(asOrderHom ((coordinateMap f).app a z).1 i, asOrderHom ((coordinateMap f).app a z).2 i) = f (asOrderHom z.1 i, asOrderHom z.2 i)`.
Here `asOrderHom` denotes the monotone-coordinate description of a standard-simplex simplex.
