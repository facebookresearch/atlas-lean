# Homeomorphism between pushout complements

Let `IsPushout t l r b` be a pushout in `TopCat.{u}`, where `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r :
X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄`. If `r.hom` is a closed embedding and `U = (Set.range r.hom)ᶜ`,
then `U.restrictPreimage b : b ⁻¹' U → U` is a homeomorphism for the subspace topologies.
