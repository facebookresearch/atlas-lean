# Adjoint of the unit composite is the restricted morphism

Let `G` be a group, `k` a commutative ring, `H ≤ G`, `X,A : Rep k G`, and `f : X → A`. For the
restriction–coinduction unit `η_A=(Rep.resCoindAdjunction k H.subtype).unit.app A`,
`(Rep.resCoindHomEquiv H.subtype X (Res A)).symm (f ≫ η_A) = (Rep.resFunctor H.subtype).map
f`.
