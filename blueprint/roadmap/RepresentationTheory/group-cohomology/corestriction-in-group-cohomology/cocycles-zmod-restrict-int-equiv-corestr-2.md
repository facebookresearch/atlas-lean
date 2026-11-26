# Integral scalar restriction preserves one-cocycle transfer

Let `G : Type` be a group, `H ≤ G` finite index, `n : ℕ`, `A : Rep (ZMod n) G`, and `T` a
right transversal. Put `J(A) = Rep.zmodRestrictInt n A`, `E_A = cocycles₁ZModRestrictIntEquiv
n A`, and `θ = (zmodRestrictIntResIso n (Subgroup.subtype H) A).hom`. For `z ∈ Z¹(H,Res A)`,
`E_A(corestrictionCocyclesOne A T z) = corestrictionCocyclesOne (J(A)) T (mapCocycles₁ (id H)
θ (E_{Res A} z))`. The scalar restriction is along `ℤ → ZMod n` for every `n`, including zero.
