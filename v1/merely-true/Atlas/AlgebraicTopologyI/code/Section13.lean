/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section11
import Atlas.AlgebraicTopologyI.code.Section12
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Module.Convex

open Finset BigOperators Set Metric

namespace AlgebraicTopologyI

/-- Lemma 13.3 (Lebesgue covering lemma). Let `M` be a compact metric space
and let `U : ι → Set M` be an open cover. Then there is `ε > 0` such that
for every `x ∈ M`, the ball `B_ε(x)` is contained in some `U i`. -/
theorem lebesgue_covering_lemma {M : Type*} [PseudoMetricSpace M] [CompactSpace M]
    {ι : Sort*} {U : ι → Set M} (hU_open : ∀ i, IsOpen (U i))
    (hU_cover : (Set.univ : Set M) ⊆ ⋃ i, U i) :
    ∃ ε > 0, ∀ x : M, ∃ i, ball x ε ⊆ U i := by
  obtain ⟨δ, hδ_pos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU_open hU_cover
  exact ⟨δ, hδ_pos, fun x => hδ x (mem_univ x)⟩

end AlgebraicTopologyI

noncomputable section

namespace SubdivisionDiameter

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The barycenter of `n + 1` points `v 0, …, v n` in a real normed space:
the average `(n + 1)⁻¹ · Σ v i`. -/
def barycenter (n : ℕ) (v : Fin (n + 1) → E) : E :=
  (↑(n + 1) : ℝ)⁻¹ • ∑ i : Fin (n + 1), v i

/-- The displacement from a vertex `v i` to the barycenter expressed as the
scaled sum of all vertex displacements `v j - v i`. -/
lemma barycenter_sub_vertex (n : ℕ) (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    barycenter n v - v i =
      (↑(n + 1) : ℝ)⁻¹ • ∑ j : Fin (n + 1), (v j - v i) := by
  unfold barycenter; rw [Finset.sum_sub_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_sub]; congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀]
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)

/-- The barycenter of vertices `v 0, …, v n` lies in the convex hull of
`range v`. -/
lemma barycenter_mem_convexHull (n : ℕ) (v : Fin (n + 1) → E) :
    barycenter n v ∈ convexHull ℝ (range v) := by
  unfold barycenter
  rw [show (↑(n + 1) : ℝ)⁻¹ • ∑ i, v i =
    Finset.univ.centerMass (fun _ : Fin (n + 1) => (1 : ℝ)) v from ?_]
  · exact centerMass_mem_convexHull _ (fun _ _ => le_of_lt one_pos)
      (by simp; positivity) (fun i _ => mem_range.mpr ⟨i, rfl⟩)
  · unfold Finset.centerMass
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_smul]

/-- The distance from the barycenter of vertices `v 0, …, v n` to any
vertex `v i` is bounded by `n / (n + 1)` times the diameter of the vertex
set. This is the key estimate used in the proof of Lemma 13.1. -/
lemma dist_barycenter_vertex_le (n : ℕ) (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    dist (barycenter n v) (v i) ≤ (n : ℝ) / (n + 1) * diam (range v) := by
  rw [dist_eq_norm, barycenter_sub_vertex]
  have hn1 : (0 : ℝ) < ↑(n + 1) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hbdd : Bornology.IsBounded (range v) := (finite_range v).isBounded
  have hsum : ∑ j : Fin (n + 1), (v j - v i) = ∑ j ∈ univ.erase i, (v j - v i) := by
    rw [← add_sum_erase _ _ (mem_univ i)]; simp
  rw [hsum]
  calc ‖(↑(n + 1) : ℝ)⁻¹ • ∑ j ∈ univ.erase i, (v j - v i)‖
      = (↑(n + 1) : ℝ)⁻¹ * ‖∑ j ∈ univ.erase i, (v j - v i)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn1)]
    _ ≤ (↑(n + 1) : ℝ)⁻¹ * ∑ j ∈ univ.erase i, ‖v j - v i‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ (↑(n + 1) : ℝ)⁻¹ * ∑ j ∈ univ.erase i, diam (range v) := by
        gcongr with j _
        rw [← dist_eq_norm]; exact dist_le_diam_of_mem hbdd ⟨j, rfl⟩ ⟨i, rfl⟩
    _ = (↑(n + 1) : ℝ)⁻¹ * (↑n * diam (range v)) := by
        congr 1; rw [sum_const, card_erase_of_mem (mem_univ i), card_univ,
            Fintype.card_fin, Nat.succ_sub_one, nsmul_eq_mul]
    _ = _ := by push_cast; ring

/-- The distance from the barycenter of vertices `v 0, …, v n` to any point
of the convex hull `conv(range v)` is bounded by `n / (n + 1)` times the
diameter of the vertex set. -/
lemma dist_barycenter_convexHull_le (n : ℕ) (v : Fin (n + 1) → E) (p : E)
    (hp : p ∈ convexHull ℝ (range v)) :
    dist (barycenter n v) p ≤ (n : ℝ) / (n + 1) * diam (range v) := by
  obtain ⟨x, hx, hpx⟩ := convexHull_exists_dist_ge hp (barycenter n v)
  obtain ⟨j, rfl⟩ := mem_range.mp hx
  calc dist (barycenter n v) p = dist p (barycenter n v) := dist_comm _ _
    _ ≤ dist (v j) (barycenter n v) := hpx
    _ = dist (barycenter n v) (v j) := dist_comm _ _
    _ ≤ _ := dist_barycenter_vertex_le n v j

/-- Inductive predicate `IsSubdivSimplex v τ` characterising the vertex
sets `τ ⊆ E` of simplices arising in the barycentric subdivision of the
affine simplex with vertices `v`. The base case is a single point; the
cone step adjoins the barycenter of `v` to a face subdivision. -/
inductive IsSubdivSimplex : {n : ℕ} → (Fin (n + 1) → E) → Set E → Prop where
  | point (v : Fin 1 → E) : IsSubdivSimplex v {v 0}
  | cone {n : ℕ} (v : Fin (n + 2) → E) (k : Fin (n + 2)) (τ : Set E)
      (hτ : IsSubdivSimplex (v ∘ Fin.succAbove k) τ) :
      IsSubdivSimplex v (insert (barycenter (n + 1) v) τ)

omit [SeminormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Removing the `k`-th vertex via `Fin.succAbove k` produces a face whose
vertex set is a subset of the original. -/
lemma range_comp_succAbove_subset {n : ℕ} (v : Fin (n + 2) → E) (k : Fin (n + 2)) :
    range (v ∘ Fin.succAbove k) ⊆ range v :=
  fun _ ⟨i, hi⟩ => ⟨Fin.succAbove k i, hi⟩

/-- Every subdivision simplex of an affine simplex `σ` with vertices `v`
is contained in the convex hull of `range v`, i.e. in `σ` itself. -/
lemma subdivSimplex_subset_convexHull :
    ∀ {n : ℕ} {v : Fin (n + 1) → E} {τ : Set E},
    IsSubdivSimplex v τ → τ ⊆ convexHull ℝ (range v) := by
  intro n v τ hτ; induction hτ with
  | point v => intro x hx; simp only [mem_singleton_iff] at hx; rw [hx]; exact subset_convexHull ℝ _ ⟨0, rfl⟩
  | cone v k τ _ ih =>
    intro x hx; simp only [mem_insert_iff] at hx
    rcases hx with rfl | hx
    · exact barycenter_mem_convexHull _ v
    · exact convexHull_mono (range_comp_succAbove_subset v k) (ih hx)

/-- Every subdivision simplex is a bounded subset of `E`. -/
lemma subdivSimplex_isBounded :
    ∀ {n : ℕ} {v : Fin (n + 1) → E} {τ : Set E},
    IsSubdivSimplex v τ → Bornology.IsBounded τ := by
  intro n v τ hτ; induction hτ with
  | point _ => exact (finite_singleton _).isBounded
  | cone _ _ _ _ ih => exact ih.insert _

omit [NormedSpace ℝ E] in
/-- The diameter of any face of the affine simplex with vertices `v` is at
most the diameter of `range v`. -/
lemma diam_face_le {n : ℕ} (v : Fin (n + 2) → E) (k : Fin (n + 2)) :
    diam (range (v ∘ Fin.succAbove k)) ≤ diam (range v) :=
  Metric.diam_mono (range_comp_succAbove_subset v k) (finite_range v).isBounded

/-- Lemma 13.1 (subdivision diameter bound). For any subdivision simplex
`τ` of the affine `n`-simplex `σ` with vertices `v`,
`diam(τ) ≤ n / (n + 1) · diam(σ)`. -/
theorem diam_subdivSimplex_le :
    ∀ {n : ℕ} {v : Fin (n + 1) → E} {τ : Set E},
    IsSubdivSimplex v τ → diam τ ≤ (n : ℝ) / (n + 1) * diam (range v) := by
  intro n v τ hτ
  induction hτ with
  | point v => simp [diam_singleton]
  | @cone n v k τ hτ_face ih =>
    have hτ_cvx : τ ⊆ convexHull ℝ (range v) := fun x hx =>
      subdivSimplex_subset_convexHull
        (IsSubdivSimplex.cone v k τ hτ_face) (mem_insert_of_mem _ hx)
    have hτ_bdd := subdivSimplex_isBounded hτ_face
    refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    intro x hx y hy
    simp only [mem_insert_iff] at hx hy
    have h_mono : (↑n : ℝ) / (↑n + 1) ≤ (↑n + 1) / (↑n + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h_diam_nn : (0 : ℝ) ≤ diam (range v) := diam_nonneg
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · simp only [dist_self]; positivity
    · exact dist_barycenter_convexHull_le (n + 1) v y (hτ_cvx hy)
    · rw [dist_comm]
      exact dist_barycenter_convexHull_le (n + 1) v x (hτ_cvx hx)
    · calc dist x y ≤ diam τ := dist_le_diam_of_mem hτ_bdd hx hy
        _ ≤ ↑n / (↑n + 1) * diam (range (v ∘ Fin.succAbove k)) := ih
        _ ≤ ↑n / (↑n + 1) * diam (range v) := by
            gcongr; exact diam_face_le v k
        _ ≤ (↑n + 1) / (↑n + 2) * diam (range v) :=
            mul_le_mul_of_nonneg_right h_mono h_diam_nn
        _ = ↑(n + 1) / (↑(n + 1) + 1) * diam (range v) := by push_cast; ring

end SubdivisionDiameter

namespace LocalityPrinciple

open CategoryTheory AlgebraicTopology BarycentricSubdivision

/-- The `k`-fold composition of a chain-complex endomorphism `f : C ⟶ C`,
i.e. `f^k`. Used to express iterates of the subdivision operator
`$^k : S_*(X) → S_*(X)` from Lemma 13.4. -/
def endoPow {C : ChainComplex AddCommGrpCat ℕ}
    (f : C ⟶ C) : ℕ → (C ⟶ C)
  | 0 => 𝟙 C
  | n + 1 => f ≫ endoPow f n

/-- The `0`-th iterate of `f` is the identity. -/
@[simp]
theorem endoPow_zero
    {C : ChainComplex AddCommGrpCat ℕ} (f : C ⟶ C) :
    endoPow f 0 = 𝟙 C := rfl

/-- The `(n + 1)`-th iterate of `f` factors as `f` followed by `f^n`. -/
@[simp]
theorem endoPow_succ
    {C : ChainComplex AddCommGrpCat ℕ} (f : C ⟶ C) (n : ℕ) :
    endoPow f (n + 1) = f ≫ endoPow f n := rfl



end LocalityPrinciple

end
