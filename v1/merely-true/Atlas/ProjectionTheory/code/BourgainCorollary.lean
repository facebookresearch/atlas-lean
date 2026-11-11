/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace BourgainProjection

open MeasureTheory Real Set

/-- Orthogonal projection of a point $x \in \mathbb{R}^2$ onto the line through the origin
making angle $\theta$ with the $x$-axis: $\pi_\theta(x) = x_0 \cos\theta + x_1 \sin\theta$. -/
noncomputable def orthogonalProjection (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  x 0 * Real.cos θ + x 1 * Real.sin θ


/-- The $\delta$-covering number $|A|_\delta$ of a set $A$ in a pseudo-extended metric space,
returned as a real number (via the external covering number from Mathlib). -/
noncomputable def coveringNum (δ : NNReal) {α : Type*} [PseudoEMetricSpace α]
    (A : Set α) : ℝ :=
  ((Metric.externalCoveringNumber δ A).toNat : ℝ)

/-- The average $\delta$-covering number of a one-parameter family of projections
$f_t : \mathbb{R}^2 \to \mathbb{R}$ applied to $X$, averaged over the parameter
$t \in [a,b]$: $\frac{1}{b-a} \int_a^b |f_t(X)|_\delta \, dt$. -/
noncomputable def avgFamilyCovering (f : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ) (δ : NNReal)
    (X : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ) : ℝ :=
  (b - a)⁻¹ * (∫ t in Set.Icc a b, coveringNum δ (f t '' X))

/-- The average $\delta$-covering number of the orthogonal projections of $X \subset \mathbb{R}^2$
over angles $\theta \in [0, \pi]$. -/
noncomputable def avgProjectionCovering (δ : NNReal)
    (X : Set (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  avgFamilyCovering orthogonalProjection δ X 0 π



/-- Iterative scale growth: if at every scale $j$ the covering number of $X_{j+1}$ dominates
$C_1 \delta^{-1}$ times the average family covering of $X_j$, and the average family covering
of $X_j$ is at least $C_2 |X_j|_\delta^{1/2}$, then $|X_{j+1}|_\delta \geq (C_1 C_2)\, \delta^{-1}\,
|X_j|_\delta^{1/2}$ for every $j$. -/
theorem avg_projection_covering_bound
    (f : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (X : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (δ : NNReal) (hδ : (0 : ℝ) < δ)
    (C₁ : ℝ) (hC₁ : C₁ > 0)
    (hdecomp : ∀ j, coveringNum δ (X (j + 1)) ≥
      C₁ * (δ : ℝ)⁻¹ * avgFamilyCovering f δ (X j) 0 1)
    (C₂ : ℝ) (hC₂ : C₂ > 0)
    (havgest : ∀ j, avgFamilyCovering f δ (X j) 0 1 ≥
      C₂ * (coveringNum δ (X j)) ^ (1/2 : ℝ)) :
    ∃ C : ℝ, C > 0 ∧ ∀ j,
      coveringNum δ (X (j + 1)) ≥ C * (δ : ℝ)⁻¹ * (coveringNum δ (X j)) ^ (1/2 : ℝ) := by
  refine ⟨C₁ * C₂, by positivity, fun j => ?_⟩
  calc coveringNum δ (X (j + 1))
      ≥ C₁ * (δ : ℝ)⁻¹ * avgFamilyCovering f δ (X j) 0 1 := hdecomp j
    _ ≥ C₁ * (δ : ℝ)⁻¹ * (C₂ * (coveringNum δ (X j)) ^ (1/2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (havgest j)
        apply mul_nonneg (le_of_lt hC₁) (le_of_lt (inv_pos.mpr hδ))
    _ = C₁ * C₂ * (δ : ℝ)⁻¹ * (coveringNum δ (X j)) ^ (1/2 : ℝ) := by ring

end BourgainProjection
