# Bar inclusion preserves the resolution augmentation

Let `G` be a group, `k` a commutative ring, and `H ≤ G`. Put `P_H=Rep.barResolution k H` and
`R_H(P_G)=(Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution k G)`. The
chain map `barRestriction H` satisfies `barRestriction H ≫ R_H(P_G).π = P_H.π`, as maps to the
degree-zero complex of the trivial `H`-representation.
