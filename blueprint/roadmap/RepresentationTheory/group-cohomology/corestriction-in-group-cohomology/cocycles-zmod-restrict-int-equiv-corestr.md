# Integral scalar restriction preserves three-cocycle transfer

Let `G : Type` be a group, `H ≤ G` finite index, `n : ℕ`, `A : Rep (ZMod n) G`, and `T` a
right transversal. Write `J(A) = Rep.zmodRestrictInt n A`, `E_A =
cocycles₃ZModRestrictIntEquiv n A`, and `θ = (zmodRestrictIntResIso n (Subgroup.subtype H)
A).hom`. For `z ∈ Z³(H,Res A)`, `E_A(corestrictionCocyclesThree A T z) =
corestrictionCocyclesThree (J(A)) T (mapCocycles₃ (id H) θ (E_{Res A} z))`. The scalar
restriction is along `ℤ → ZMod n` and includes `n = 0`.
