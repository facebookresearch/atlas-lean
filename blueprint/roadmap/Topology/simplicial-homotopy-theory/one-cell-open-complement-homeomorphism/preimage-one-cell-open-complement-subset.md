# Preimage of a pushout image complement

Let `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄` form a pushout in `TopCat.{u}`. Then
`b ⁻¹' ((Set.range r.hom)ᶜ) ⊆ (Set.range l.hom)ᶜ`:
a point of `X₃` mapping outside the image of `r` lies outside the image of `l`.
