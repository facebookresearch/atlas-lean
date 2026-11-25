# The Yoneda-element chase for `joinInl`

The composite in
`DayCat` obtained by expanding `joinInl Δ[m] Δ[n]` (right unitor,
then whiskering the unique map out of the empty simplicial set)
and `joinStdSimplexIso m n` equals `augDayStdSimplexIso` followed
by the representable map of `inl`. The proof evaluates both
sides, after precomposing with `(augDayStdSimplexIso m).inv`,
on the universal element `ULift.up (𝟙 (of ⦋m⦌))`:
`Join.rightUnitor_inv_app_of` writes it as an `η`-element, the
whisker steps (`η_whiskerLeft_app`, `η_whiskerRight_app` of
`JoinProperties.lean`) push it through the tensor, the degree
`-1` components compute by the `rfl` lemmas above, and
`η_comp_tensorDesc_app` finishes at
`ULift.up (𝟙 ⊗ₘ starInitial.to) = ULift.up (inl ..)`
(`Join.inl_of_eq`).
