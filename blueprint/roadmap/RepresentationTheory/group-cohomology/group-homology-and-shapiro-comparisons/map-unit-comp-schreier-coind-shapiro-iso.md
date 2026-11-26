# Unit followed by Shapiro is cohomological restriction

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `T` a right
transversal, and `n : ℕ`. For `η_A=(Rep.resCoindAdjunction k H.subtype).unit.app A` and
`S_T=schreierCoindShapiroIso H (Res_H A) T n`, `map (id G) η_A n ≫ S_T.hom = map H.subtype (𝟙
(Res_H A)) n` as maps `H^n(G,A) → H^n(H,Res_H A)`.
