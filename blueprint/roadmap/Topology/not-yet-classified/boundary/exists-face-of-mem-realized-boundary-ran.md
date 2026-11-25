# Exists face of mem realized Boundary Range

Every realized boundary point lies in a codimension-one face.

From `q ∈ Set.range ⇑(toTop.map (boundary N).ι)` return a face index `j`,
a realized face point `y`, and equality under the realized face inclusion.
The `N = 0` case is vacuous via `realizedBoundaryZero_range_empty`; for
`N = n + 1` the point comes from a leg of the realized multicoequalizer
colimit `isColimitToTop'` via `Types.jointly_surjective_of_isColimit`
after preservation by `forget TopCat`, left legs reduce through the
existing `homOfLE` pattern, and the right leg factors through
`SSet.boundary.faceι_ι`.
