# Homogeneous Cochains boundary class eq

Generic degree-one boundary equality corollary for continuous cohomology.

If two degree-one cycles differ by a boundary, `z₁ - z₂ = b ≫ d 0 1`,
their classes under `homologyπ 1` agree. Uses the Mathlib boundary-vanishing
lemma `HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary` via
subtraction and `sub_eq_zero`; no finite comparison or ordinary-H1 bridge is used.

Nonclaims: no Kummer, motivic, étale, or isomorphism statement.
