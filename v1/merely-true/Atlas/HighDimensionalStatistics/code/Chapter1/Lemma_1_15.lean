/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Archimedean

open Set Finset

/-- **Lemma 1.15 (linear maximum at vertex, single point version).** A linear
form `f` on a real vector space attains its maximum over the convex hull of a
nonempty finite set `S` at some vertex; equivalently, for every `x` in the
convex hull, `f x ≤ sup' S f`. -/
theorem lemma_1_15_linear_max_at_vertex
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] ℝ) (S : Finset E) (hS : S.Nonempty)
    (x : E) (hx : x ∈ convexHull ℝ (↑S : Set E)) :
    f x ≤ S.sup' hS f :=
  (f.convexOn (convex_convexHull ℝ (↑S : Set E))).le_sup_of_mem_convexHull
    (subset_convexHull ℝ (↑S : Set E)) hx

/-- **Lemma 1.15 (existence of a maximizing vertex).** For any linear form `f`
and finite set `S`, every point `x` in the convex hull of `S` satisfies
`f x ≤ f v` for some vertex `v ∈ S`. -/
theorem lemma_1_15_exists_vertex
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] ℝ) (S : Finset E)
    (x : E) (hx : x ∈ convexHull ℝ (↑S : Set E)) :
    ∃ v ∈ S, f x ≤ f v := by
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hx
  have h := (f.convexOn (convex_convexHull ℝ (↑S : Set E))).le_sup_of_mem_convexHull
    (subset_convexHull ℝ (↑S : Set E)) hx
  rwa [Finset.le_sup'_iff] at h

/-- **Lemma 1.15 (supremum of a linear form over a polytope).** The supremum
of a linear form `f` over the convex hull of a nonempty finite set `S` equals
the maximum of `f` over the vertices `S`. -/
theorem lemma_1_15_sSup_eq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] ℝ) (S : Finset E) (hS : S.Nonempty) :
    sSup (f '' (convexHull ℝ (↑S : Set E))) = S.sup' hS f := by
  apply le_antisymm
  ·
    apply csSup_le
    · exact image_nonempty.mpr (convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hS))
    · rintro _ ⟨x, hx, rfl⟩
      exact lemma_1_15_linear_max_at_vertex f S hS x hx
  ·
    apply Finset.sup'_le hS
    intro v hv
    apply le_csSup
    ·
      exact ⟨S.sup' hS f, fun _ ⟨x, hx, he⟩ => he ▸ lemma_1_15_linear_max_at_vertex f S hS x hx⟩
    · exact ⟨v, subset_convexHull ℝ (↑S : Set E) (Finset.mem_coe.mpr hv), rfl⟩
