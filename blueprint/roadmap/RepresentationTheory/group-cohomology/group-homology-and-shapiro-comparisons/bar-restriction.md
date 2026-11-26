# Bar inclusion between subgroup projective resolutions

Let `G` be a group, `k` a commutative ring, and `H ≤ G`. Write `P_G=Rep.barResolution k G`,
`P_H=Rep.barResolution k H`, and `R_H(P_G)=(Rep.resFunctor H.subtype).mapProjectiveResolution
P_G`. The chain map `barRestriction H : P_H.complex → R_H(P_G).complex` has the subgroup bar
inclusions `barRestrictionComponent H n` as its degree-`n` components.
