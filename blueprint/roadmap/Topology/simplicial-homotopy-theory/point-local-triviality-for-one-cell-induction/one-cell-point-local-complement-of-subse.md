# Restriction of a transported complement trivialization

Let `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄` form a pushout in
`TopCat.{u}`, with `r` a closed embedding, and let `IsPullback e p₃ p b` relate `p₃ : E₃ ⟶ X₃`
to `p : E ⟶ X₄`. Suppose `h_new` trivializes `p₃` with fiber `F` over `(Set.range l.hom)ᶜ`.
For `h_sub : U ⊆ (Set.range r.hom)ᶜ`, assume the pullback of the transported presentation's
projection along `subspaceInclOfSubset h_sub` exists. Transport followed by restriction gives
a trivial pullback presentation of `p` with fiber `F` over `U`.
