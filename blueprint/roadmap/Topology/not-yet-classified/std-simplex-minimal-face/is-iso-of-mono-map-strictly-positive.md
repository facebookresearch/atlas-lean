# Is Iso of mono map strictly positive

New-carrier mono face with strictly positive image is an isomorphism.

If `φ` is mono and its simplex image is strictly positive in every
coordinate, then `φ` is surjective on vertices, hence an isomorphism.
Dimension zero needs no special case: `Fin (k + 1)` is always nonempty,
so the surjectivity argument below is uniform in `k`.

Reuse:
- `Convexity.StdSimplex.range_eq_support_of_map_strictly_positive`
  (`MathlibExt/Analysis/Convex/StdSimplex.lean`): `reuse`.
- `SimplexCategory.mono_iff_injective`, `SimplexCategory.epi_iff_surjective`,
  `CategoryTheory.isIso_of_mono_of_epi`: `reuse`.
- Pinned `Convexity.StdSimplex.weights_map`,
  `Finsupp.mapDomain_apply_of_injective`, `Set.range_eq_univ`,
  `ne_of_gt`: `reuse`.
- No new reusable construction beyond this packaging.

Nonclaim: no open-cell uniqueness, realization, quotient, compact-support,
model-category, or KQ4 result.
