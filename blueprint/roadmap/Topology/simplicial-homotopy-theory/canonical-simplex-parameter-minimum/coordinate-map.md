# Simplicial map induced by product-ordinal coordinates

For `p, q, r, s : SimplexCategory` and a monotone map `f : Fin (p.len + 1) × Fin (q.len + 1) →o Fin (r.len + 1) × Fin (s.len + 1)`, the induced simplicial map in universe `u` is
`stdSimplex.obj p ⊗ stdSimplex.obj q ⟶ stdSimplex.obj r ⊗ stdSimplex.obj s`.
It is the nerve of the lifted preorder functor of `f`, transported through the isomorphisms identifying products of standard simplices with nerves of product ordinals.
