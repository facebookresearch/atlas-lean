# Schreier prism as differences of homogeneous vertices

Let `G` be a group, `H ≤ G`, `T,U` right transversals, `t ∈ T`, `tuple : Fin n → G`, and `i :
Fin (n + 1)`. For prefix products `p_j`, put `a_j=T.schreierFactor t p_j` and
`b_j=T.changeFactor U t * U.schreierFactor (T.changeRep U t) p_j`. If
`v=SchreierPrism.vertices a b i`, then `j ↦ (v j)⁻¹ * v(j+1)` equals `T.schreierPrismTuple U t
tuple i` as an `(n+1)`-tuple in `H`.
