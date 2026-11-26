# Complement preimage equality in a topological pushout

For a pushout `IsPushout t l r b` in `TopCat.{u}`, with `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄`,
`b ⁻¹' ((Set.range r.hom)ᶜ) = (Set.range l.hom)ᶜ`.
Thus the points of the new leg outside the attaching image are exactly those whose pushout images avoid the old leg.
