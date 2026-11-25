# Hom One Cochain mem ker

The homogeneous cochain lies in the kernel of the degree-one differential.

Uses `TopRep.homogeneousCochains.d_apply`, `TopRep.hom_d_succ`,
`TopRep.hom_ofHom`, `TopRep.d_zero`,
`ContRepresentation.coind₁ι_toFun`, `ContRepresentation.coind₁Map_toFun`, and
pointwise continuous-map lemmas, plus the cocycle equation.

The proof first reduces to the subtype kernel membership, derives the pointwise
cocycle identity `hF`, unfolds the homogeneous differential at `.hom`, applies
three-argument function extensionality, and only then evaluates the coinduction
terms pointwise so the pointwise identity closes the goal.
