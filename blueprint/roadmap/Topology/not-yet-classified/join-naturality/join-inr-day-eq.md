# The Yoneda-element chase for `joinInr`

The composite in
`DayCat` obtained by expanding `joinInr Δ[m] Δ[n]` (left unitor,
then whiskering the unique map out of the empty simplicial set
on the left) and `joinStdSimplexIso m n` equals
`augDayStdSimplexIso` followed by the representable map of
`inr`. Mirror of `SSet.Join.joinInlDay_eq`: the
proof evaluates both sides, after precomposing with
`(augDayStdSimplexIso n).inv`, on the universal element
`ULift.up (𝟙 (of ⦋n⦌))`: `SSet.Join.leftUnitor_inv_app_of`
 writes it as an `η`-element, the whisker steps
push it through the tensor, the degree `-1` components compute
by the defining component lemmas, and `η_comp_tensorDesc_app`
finishes at `ULift.up (starInitial.to ⊗ₘ 𝟙) = ULift.up (inr ..)`
(`SSet.Join.inr_of_eq`).
