# Cyclic diagonal followed by Shapiro is restriction

Let `G` be a group, `k` a commutative ring, `ℓ : ℕ` nonzero, `χ : G → Multiplicative (ZMod ℓ)`
surjective, `A : Rep k G`, `T` a right transversal for `J=ker χ`, and `n : ℕ`. With
`d_χ=Rep.cyclicPermutationDiagonal ℓ χ A`, `map (id G) d_χ n ≫
(schreierCyclicPermutationShapiroIso ℓ χ hχ A T n).hom = map J.subtype (𝟙 (Res_J A)) n`. The
coefficient diagonal is `a ↦ (i ↦ a)`.
