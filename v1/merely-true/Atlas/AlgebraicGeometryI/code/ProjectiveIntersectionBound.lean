/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.ProjectiveIntersection
import Atlas.AlgebraicGeometryI.code.IntersectionDimension

noncomputable section
open Ideal MvPolynomial Classical

/-- Affine codimension bound for intersection components: a minimal prime over the span
of `s ∪ t` in a Noetherian ring has height at most `|s| + |t|`. -/
theorem affine_intersection_component_codim_bound {R : Type*} [CommRing R] [IsNoetherianRing R]
    {s t : Finset R}
    {𝔴 : Ideal R}
    (hmin : 𝔴 ∈ (Ideal.span ((s ∪ t : Finset R) : Set R)).minimalPrimes) :
    𝔴.height ≤ s.card + t.card := by
  have h := height_le_card_of_mem_minimalPrimes_span_finset hmin
  refine le_trans h ?_
  rw [show (↑(s.card) : ℕ∞) + ↑(t.card) = ↑(s.card + t.card) from by push_cast; ring]
  exact ENat.coe_le_coe.mpr (Finset.card_union_le s t)

/-- Two projective cones in `𝔸^{n+1}` (ideals contained in the irrelevant ideal) have
nontrivial intersection: their sum is not the unit ideal. -/
theorem projective_cone_intersection {k : Type*} [Field k] {n : ℕ}
    {𝔭 𝔮 : Ideal (MvPolynomial (Fin (n + 1)) k)}
    (hp : 𝔭 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
    (hq : 𝔮 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1))) :
    𝔭 ⊔ 𝔮 ≠ ⊤ :=
  MvPolynomial.sup_ne_top_of_le_variablesIdeal hp hq
