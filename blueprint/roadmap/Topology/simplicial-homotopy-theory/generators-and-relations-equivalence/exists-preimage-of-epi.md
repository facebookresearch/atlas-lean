# Exists preimage of epi

Epi-lifting to pure degeneracies for canonical simplex objects.

Uses `SimplexCategory.le_of_epi` for the length bound, `SimplexCategory.eq_id_of_epi`
in the equal-length case, and `SimplexCategory.eq_σ_comp_of_not_injective` after
showing non-injectivity via mono+epi ⇒ iso in the strict case. The residual map
is epi by cancellation and the induction goes through on the strictly smaller source,
prepending the corresponding `σ` in `GenRel` with `P_σ.comp_mem`.
