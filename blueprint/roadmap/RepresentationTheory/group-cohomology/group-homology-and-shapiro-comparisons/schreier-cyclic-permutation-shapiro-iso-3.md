# Shapiro followed by corestriction is cyclic augmentation

Let `G` be a group, `k` a commutative ring, `ℓ : ℕ` nonzero, `χ : G → Multiplicative (ZMod ℓ)`
surjective, `A : Rep k G`, `T` a right transversal for `J=ker χ`, and `n : ℕ`. Then
`(schreierCyclicPermutationShapiroIso ℓ χ hχ A T n).hom ≫ schreierCorestriction J A n = map
(id G) (Rep.cyclicPermutationAugmentation ℓ χ A) n`, as maps `H^n(G,P_χ(A)) → H^n(G,A)`; the
coefficient augmentation is `p ↦ ∑ i : ZMod ℓ, p(i)`.
