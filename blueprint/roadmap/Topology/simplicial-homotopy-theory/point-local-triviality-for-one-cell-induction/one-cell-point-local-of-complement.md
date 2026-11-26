# Local triviality at a pushout-complement point

In `TopCat.{u}`, let `IsPushout t l r b` have legs `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶
X₄`, and `b : X₃ ⟶ X₄`, with `r` a closed embedding. Suppose `IsPullback e p₃ p b` and a
presentation `h_new` trivializes `p₃` with fiber `F` over `(Set.range l.hom)ᶜ`. Let `pt ∈
(Set.range r.hom)ᶜ`, and assume the pullback of the transported projection along the inclusion
of this complement into itself exists. Then `OneCellPointLocalTriviality p F pt` holds,
witnessed by the open complement `(Set.range r.hom)ᶜ`.
