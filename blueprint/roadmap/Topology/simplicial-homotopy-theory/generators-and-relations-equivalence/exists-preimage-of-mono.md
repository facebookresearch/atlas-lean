# Exists preimage of mono

Mono-lifting to admissible face chains for canonical simplex objects.

Uses `SimplexCategory.le_of_mono` for the length bound, `SimplexCategory.eq_id_of_mono`
in the equal-length case, and `SimplexCategory.eq_comp_δ_of_not_surjective` after showing
non-surjectivity via epi+mono ⇒ iso in the strict case. The residual map is mono by
cancellation and the induction goes through on the strictly smaller target, forming
`DeltaChain.normalize (c.snoc i)` with `normalize_admissible`, `normalize_eval`,
functoriality, and the recursive map equality.
