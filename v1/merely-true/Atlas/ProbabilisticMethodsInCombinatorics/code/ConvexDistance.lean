/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Topology

set_option maxHeartbeats 800000

open scoped BigOperators
open Finset

namespace ConvexDistance

variable {n : ℕ}

/-- The $n$-dimensional unit cube $[0,1]^n$ as a subset of $\mathbb{R}^n$. -/
def unitCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i : Fin n, 0 ≤ x i ∧ x i ≤ 1}

/-- Weighted Hamming distance from $x$ to $y$ with weight vector $\alpha$:
$\sum_{i : x_i \neq y_i} |\alpha_i|$. -/
noncomputable def weightedHammingDist (α x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, if x i ≠ y i then |α i| else 0

/-- Weighted Hamming distance from $x$ to a set $A$: the infimum of `weightedHammingDist α x y`
as $y$ ranges over $A$. -/
noncomputable def weightedHammingDistSet (α x : EuclideanSpace ℝ (Fin n))
    (A : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf ((weightedHammingDist α x) '' A)

/-- Talagrand's convex distance from $x$ to a set $A$: the supremum over unit vectors
$\alpha$ of the $\alpha$-weighted Hamming distance from $x$ to $A$. -/
noncomputable def talagrandDist (x : EuclideanSpace ℝ (Fin n))
    (A : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sSup ((fun α => weightedHammingDistSet α x A) '' {α | ‖α‖ = 1})

/-- The weighted Hamming distance is non-negative, as a sum of absolute values and zeros. -/
lemma weightedHammingDist_nonneg (α x y : EuclideanSpace ℝ (Fin n)) :
    0 ≤ weightedHammingDist α x y := by
  simp only [weightedHammingDist]
  apply Finset.sum_nonneg; intro i _; split_ifs with h
  · exact abs_nonneg _
  · exact le_refl _

/-- Each coordinate of a vector in Euclidean space is bounded in absolute value by the
Euclidean norm: $|\alpha_i| \le \|\alpha\|$. -/
lemma abs_component_le_norm (α : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |α i| ≤ ‖α‖ := by
  have h1 : (α i) ^ 2 ≤ ∑ j : Fin n, (α j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (α j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ‖α‖ ^ 2 = ∑ j : Fin n, (α j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    congr 1; funext j; rw [Real.norm_eq_abs, sq_abs]
  exact abs_le_of_sq_le_sq (h2 ▸ h1) (norm_nonneg _)

/-- For a unit-norm weight vector $\alpha$, the weighted Hamming distance between any two
points is at most $n$. -/
lemma weightedHammingDist_le_of_unit_norm (α x y : EuclideanSpace ℝ (Fin n))
    (hα : ‖α‖ = 1) : weightedHammingDist α x y ≤ ↑n := by
  simp only [weightedHammingDist]
  calc ∑ i : Fin n, (if x i ≠ y i then |α i| else (0 : ℝ))
      ≤ ∑ _ : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro i _
        split_ifs with h
        · exact (abs_component_le_norm α i).trans (le_of_eq hα)
        · linarith
    _ = ↑n := by simp [Finset.sum_const]

/-- For $x, y$ in the unit cube and any weight vector $\alpha$, the inner product
$\langle x - y, \alpha\rangle$ is bounded by the weighted Hamming distance
$\mathrm{whd}_\alpha(x,y)$. -/
lemma inner_le_weightedHammingDist (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ unitCube n) (hy : y ∈ unitCube n)
    (α : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ _ _ (x - y) α ≤ weightedHammingDist α x y := by
  simp only [weightedHammingDist]
  rw [show @inner ℝ _ _ (x - y) α = ∑ i : Fin n, (x i - y i) * α i from by
    rw [PiLp.inner_apply]; congr 1; ext i; simp [PiLp.sub_apply, inner, mul_comm]]
  apply Finset.sum_le_sum; intro i _
  by_cases h : x i = y i
  · simp [h]
  · simp only [h, ↓reduceIte, ne_eq, not_false_eq_true]
    calc (x i - y i) * α i
        ≤ |(x i - y i) * α i| := le_abs_self _
      _ = |x i - y i| * |α i| := abs_mul _ _
      _ ≤ 1 * |α i| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          rw [abs_le]; constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
      _ = |α i| := one_mul _

/-- The set whose supremum defines `talagrandDist` is bounded above by $n$, hence the
supremum is attainable in the extended sense (used to apply `csSup` lemmas). -/
lemma talagrandDist_bddAbove (x : EuclideanSpace ℝ (Fin n))
    (A : Set (EuclideanSpace ℝ (Fin n))) (hAne : A.Nonempty) :
    BddAbove ((fun α => weightedHammingDistSet α x A) '' {α | ‖α‖ = 1}) := by
  refine ⟨↑n, ?_⟩
  rintro r ⟨α, (hα : ‖α‖ = 1), rfl⟩
  unfold weightedHammingDistSet
  obtain ⟨y₀, hy₀⟩ := hAne
  have hbdd : BddBelow ((weightedHammingDist α x) '' A) :=
    ⟨0, fun b ⟨y, _, hb⟩ => hb ▸ weightedHammingDist_nonneg α x y⟩
  exact (csInf_le hbdd (Set.mem_image_of_mem _ hy₀)).trans
    (weightedHammingDist_le_of_unit_norm α x y₀ hα)

/-- Talagrand's convex distance is non-negative. -/
lemma talagrandDist_nonneg (x : EuclideanSpace ℝ (Fin n))
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    0 ≤ talagrandDist x A := by
  unfold talagrandDist
  apply Real.sSup_nonneg
  rintro r ⟨α, _, rfl⟩
  unfold weightedHammingDistSet
  apply Real.sInf_nonneg
  rintro b ⟨y, _, rfl⟩
  exact weightedHammingDist_nonneg α x y

/-- Lemma 9.5.12 / Corollary 9.5.13 (convex distance bound). If $A \subseteq [0,1]^n$ and
$x \in [0,1]^n$, then the Euclidean distance from $x$ to the convex hull of $A$ is at most
Talagrand's convex distance $d_T(x, A)$. -/
theorem convex_dist_upper_bounds_euclidean_dist
    (A : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n))
    (hA : A ⊆ unitCube n) (hx : x ∈ unitCube n)
    (hAne : A.Nonempty) :
    Metric.infDist x (convexHull ℝ A) ≤ talagrandDist x A := by

  set K := closure (convexHull ℝ A)
  have hKne : K.Nonempty := hAne.mono fun a ha => subset_closure (subset_convexHull ℝ A ha)
  have hKconvex : Convex ℝ K := (convex_convexHull ℝ A).closure

  rw [← Metric.infDist_closure]

  obtain ⟨v, hv, hvmin⟩ := exists_norm_eq_iInf_of_complete_convex
    hKne isClosed_closure.isComplete hKconvex x

  have hdist_eq : Metric.infDist x K = ‖x - v‖ := by
    rw [Metric.infDist_eq_iInf]; simp only [dist_eq_norm]; exact hvmin.symm
  rw [hdist_eq]

  by_cases hxv : x = v
  · subst hxv; rw [sub_self, norm_zero]; exact talagrandDist_nonneg x A
  ·
    set α := (‖x - v‖⁻¹ : ℝ) • (x - v)
    have hnorm_pos : 0 < ‖x - v‖ := by
      rw [norm_pos_iff]; intro h; exact hxv (eq_of_sub_eq_zero h)
    have hα_norm : ‖α‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hnorm_pos)]

    have hA_sub_K : A ⊆ K := fun a ha => subset_closure (subset_convexHull ℝ A ha)

    have hinner_ge : ∀ y ∈ A, ‖x - v‖ ≤ @inner ℝ _ _ (x - y) α := by
      intro y hy
      show ‖x - v‖ ≤ @inner ℝ _ _ (x - y) (‖x - v‖⁻¹ • (x - v))
      rw [inner_smul_right]
      rw [real_inner_comm]
      rw [le_inv_mul_iff₀ hnorm_pos, ← sq]
      have hproj := ((norm_eq_iInf_iff_real_inner_le_zero hKconvex hv).mp hvmin) y (hA_sub_K hy)
      have key : x - y = (x - v) - (y - v) := by abel
      rw [key, inner_sub_right, real_inner_self_eq_norm_mul_norm, sq]; linarith

    have hbound : ∀ y ∈ A, ‖x - v‖ ≤ weightedHammingDist α x y := fun y hy =>
      (hinner_ge y hy).trans (inner_le_weightedHammingDist x y hx (hA hy) α)

    have hle_whdSet : ‖x - v‖ ≤ weightedHammingDistSet α x A := by
      unfold weightedHammingDistSet
      exact le_csInf (hAne.image _) (fun b ⟨y, hy, hb⟩ => hb ▸ hbound y hy)

    exact le_csSup_of_le (talagrandDist_bddAbove x A hAne) ⟨α, hα_norm, rfl⟩ hle_whdSet

end ConvexDistance
