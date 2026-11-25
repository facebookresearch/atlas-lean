# Dwyer Kan Fully Faithful Pi Zero

The `π₀`-level (homotopy-category) shadow of Stevenson
Definition 2.16(ii): `f` induces a bijection on morphism sets
`(mk x ⟶ mk y) → (mk (f x) ⟶ mk (f y))` of ordinary homotopy
categories for all vertices `x y`. For a quasicategory these morphism
sets are the standard identification of `π₀` of the mapping spaces;
this file states the property in homotopy-category form, and the
transport to `π₀ (mappingSpaceRight X _ _)` itself is
`SSet.mappingSpaceRight.piZeroEquiv` downstream
(`MappingSpacePi.lean`). Compare
`SSet.dwyerKanFullyFaithful`, the full mapping-space
statement.
