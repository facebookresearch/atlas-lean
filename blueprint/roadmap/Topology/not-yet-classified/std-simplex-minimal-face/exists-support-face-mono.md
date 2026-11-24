# Exists support face mono

New-carrier support face as a simplex-category monomorphism with strictly
positive preimage.

Derived from `Convexity.StdSimplex.exists_strictly_positive_preimage` (no proof
duplication): `Finset.orderEmbOfFin` supplies the monotone support enumeration,
`SimplexCategory.Hom.mk` the morphism, `SimplexCategory.mono_iff_injective`
the monomorphism, and `Convexity.StdSimplex.map_surjective_pos` with pinned
`Convexity.StdSimplex.map_comp` the transported positivity and map equation.
Support cardinality is `k + 1` (explicitly positive, so the dimension-zero
empty case is impossible).

Reuse map:
- `Convexity.StdSimplex.exists_strictly_positive_preimage`,
  `Convexity.StdSimplex.map_surjective_pos` (`MathlibExt/Analysis/Convex/StdSimplex.lean`): `reuse`.
- `Convexity.StdSimplex.map_comp` (pinned Mathlib): `reuse`.
- `Finset.orderEmbOfFin`, `Finset.range_orderEmbOfFin`
  (`Mathlib/Data/Finset/Sort.lean`): `reuse`.
- `SimplexCategory.Hom.mk`, `SimplexCategory.mono_iff_injective`: `reuse`.
- `Finset.card_image_of_injective`, `Finset.mem_image`, `Finset.mem_coe`,
  `Nat.exists_eq_succ_of_ne_zero` (pinned Mathlib): `reuse`.

Nonclaim: no open-cell, realization, quotient, compact-support,
model-category, or KQ4 result.
