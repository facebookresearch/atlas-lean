# Model Category Quillen I rlp iff has Lifting Property boundary

A map is a trivial Kan fibration (`modelCategoryQuillen.I.rlp`)
if and only if it has the right lifting property against every
boundary inclusion. The forward direction is
`SSet.hasLiftingProperty_boundary_of_rlp_I` (the supporting results); the
reverse direction destructures membership in
`SSet.modelCategoryQuillen.I = .ofHoms (fun n ↦ ∂Δ[n].ι)`.
