# Inverse cyclic Shapiro followed by augmentation is transfer

Let `G` be a group, `k` a commutative ring, `ℓ : ℕ` nonzero, `χ : G → Multiplicative (ZMod ℓ)`
surjective, `A : Rep k G`, `T` a right transversal for `J=ker χ`, and `n : ℕ`. For
`S_χ=schreierCyclicPermutationShapiroIso ℓ χ hχ A T n` and
`a_χ=Rep.cyclicPermutationAugmentation ℓ χ A`, `S_χ.inv ≫ map (id G) a_χ n =
corestrictionOfRightTransversal A T n`. The map `a_χ` sums the cyclic coordinates.
