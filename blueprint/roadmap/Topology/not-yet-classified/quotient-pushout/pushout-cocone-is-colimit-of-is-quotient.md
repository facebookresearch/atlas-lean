# Pushout Cocone Is Colimit Of Is Quotient Map

A `TopCat` pushout cocone whose binary coproduct map `desc t.inl t.inr`
is a quotient map is colimiting provided every competing cocone's binary map
is constant on the fibres of that quotient map. The descended map is built by
`IsQuotientMap.lift`, the factorisation uses `IsQuotientMap.lift_comp` together
with `coprod.inl_desc_assoc` and `coprod.inr_desc_assoc`, and uniqueness uses
that a quotient map is epi via `epi_iff_surjective` and `coprod.hom_ext`.
