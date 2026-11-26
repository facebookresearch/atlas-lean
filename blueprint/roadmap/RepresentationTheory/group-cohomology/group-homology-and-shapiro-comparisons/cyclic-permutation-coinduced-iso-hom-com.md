# Cyclic coefficient comparison carries the counit to augmentation

Let `G` be a group, `k` a commutative ring, `ℓ : ℕ` nonzero, `χ : G → Multiplicative (ZMod ℓ)`
surjective, and `A : Rep k G`. For `J=ker χ`, `F_χ=Rep.cyclicPermutationCoinducedIso ℓ χ hχ
A`, and `ε_A=corestrictionCounit J A`, `F_χ.hom ≫ ε_A = Rep.cyclicPermutationAugmentation ℓ χ
A`. The comparison sends `p` to `g ↦ ρ_A(g)p(Multiplicative.toAdd (χ g))`, and the
augmentation sends `p` to `∑ i : ZMod ℓ, p(i)`.
