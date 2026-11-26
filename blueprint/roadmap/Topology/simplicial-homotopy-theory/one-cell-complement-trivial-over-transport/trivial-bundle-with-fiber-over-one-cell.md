# Transport of a trivial bundle across pushout complements

In `TopCat.{u}`, suppose `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄` form a
pushout and `r.hom` is a closed embedding. Let `p : E ⟶ X₄`, `p₃ : E₃ ⟶ X₃`, and `e : E₃ ⟶ E`
form the pullback `IsPullback e p₃ p b`. For a fixed fiber `F : TopCat.{u}`, a presentation
`h_new` trivializing `p₃` over `(Set.range l.hom)ᶜ` induces a presentation trivializing `p`
over `(Set.range r.hom)ᶜ`. Both presentations are pullbacks along the corresponding subspace
inclusions with total spaces products of their bases and `F`.
