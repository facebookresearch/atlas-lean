# Integral scalar restriction preserves degree-one corestriction

Let `G : Type` be a group, `H ≤ G` finite index, `n : ℕ`, and `A : Rep (ZMod n) G`. Put `J(A)
= Rep.zmodRestrictInt n A`, `E_A = H1ZModRestrictIntAddEquiv n A`, and `θ =
(zmodRestrictIntResIso n (Subgroup.subtype H) A).hom : J(Res A) → Res(J(A))`. For `x ∈
H¹(H,Res A)`, `E_A(corestrictionH1 A x) = corestrictionH1 (J(A)) (map (id H) θ 1 (E_{Res A}
x))`. This identity includes `n = 0`.
