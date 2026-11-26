# Restriction of a trivialization inside an image

In `TopCat.{u}`, let `p : E ⟶ X₄`, `r : X₂ ⟶ X₄`, and `F : TopCat.{u}`. Suppose `h_old` is a
trivial pullback presentation of `p` with fiber `F` over `Set.range r.hom`. For `U : Set X₄`
and `h_sub : U ⊆ Set.range r.hom`, assume the pullback of `h_old.p'` along
`subspaceInclOfSubset h_sub` exists. Restricting along this inclusion gives a trivial pullback
presentation of `p` with fiber `F` over `U`.
