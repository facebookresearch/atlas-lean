# Integral scalar restriction preserves degree-three corestriction

Let `G : Type` be a group, `H ≤ G` finite index, `n : ℕ`, and `A : Rep (ZMod n) G`. Put `J(A)
= Rep.zmodRestrictInt n A`, `E_A = H3ZModRestrictIntAddEquiv n A`, and `θ =
(zmodRestrictIntResIso n (Subgroup.subtype H) A).hom : J(Res A) → Res(J(A))`. For `x ∈
H³(H,Res A)`, `E_A(corestrictionH3 A x) = corestrictionH3 (J(A)) (map (id H) θ 3 (E_{Res A}
x))`. The identity holds for all `n`, including zero.
