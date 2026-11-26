# Value of the unit-Shapiro cochain map

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `T` a right
transversal, and `n : ℕ`. For `z : (Fin n → G) → A` and `q : Fin n → H`, the value of
`coindUnitSchreierShapiroCochains H A T` is `(F_T.inv.f n ≫ Res_H(Rep.freeLift k G A
z))(barBasis_H n q)`, where `F_T=schreierRestrictionBarHomotopyEquiv H T` and the basis has
unit group-ring coefficient.
