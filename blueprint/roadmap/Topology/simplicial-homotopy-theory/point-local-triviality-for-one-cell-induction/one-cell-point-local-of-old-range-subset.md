# Local triviality on an open subset of an image

Let `p : E ⟶ X₄` and `r : X₂ ⟶ X₄` be morphisms in `TopCat.{u}`, and let `h_old` trivialize
the pullback of `p` over `Set.range r.hom` with fiber `F`. Suppose `U : Set X₄` is open, `pt ∈
U`, and `h_sub : U ⊆ Set.range r.hom`. If the pullback of `h_old.p'` along
`subspaceInclOfSubset h_sub` exists, then `OneCellPointLocalTriviality p F pt` holds,
witnessed by the restriction to `U`.
