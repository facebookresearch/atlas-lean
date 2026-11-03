/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.LevyIsoperimetric
set_option maxHeartbeats 400000

noncomputable section

open Real Set MeasureTheory

namespace SphericalCap

/-- The $(n-1)$-dimensional Hausdorff measure on the unit sphere $S^{n-1}$, serving as the
unnormalized surface-area measure used to define `normalizedSphereMeasure`. -/
def sphereVolume (n : ℕ) :
    Measure (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
  Measure.hausdorffMeasure (↑(n - 1) : ℝ)


/-- The **uniform probability measure** on $S^{n-1}$, defined by normalizing the
$(n-1)$-Hausdorff surface measure: $\mu(A) = \operatorname{vol}(A) / \operatorname{vol}(S^{n-1})$. -/
def normalizedSphereMeasure {n : ℕ}
    (A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))) : ℝ :=
  (sphereVolume n A).toReal / (sphereVolume n Set.univ).toReal



/-- The normalized measure of the spherical cap $\{x \in S^{n-1} \mid x_1 \ge \varepsilon\}$,
i.e. $\mathbb{P}_{x \sim S^{n-1}}(x_1 \ge \varepsilon)$ (with the convention that the value is
$0$ when $n = 0$). -/
def sphericalCapMeasure (n : ℕ) (ε : ℝ) : ℝ :=
  if h : 0 < n then
    normalizedSphereMeasure
      {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) |
        (x : EuclideanSpace ℝ (Fin n)) ⟨0, h⟩ ≥ ε}
  else 0

set_option maxHeartbeats 800000 in
/-- For $\varepsilon > 1$ the cap $\{x \in S^{n-1} \mid x_1 \ge \varepsilon\}$ is empty,
hence has measure $0$. -/
theorem sphericalCapMeasure_eq_zero_of_gt_one (n : ℕ) (ε : ℝ) (hε : ε > 1) :
    sphericalCapMeasure n ε = 0 := by
  unfold sphericalCapMeasure
  split
  case isTrue h =>
    unfold normalizedSphereMeasure
    have h_empty : {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) |
        (x : EuclideanSpace ℝ (Fin n)) ⟨0, h⟩ ≥ ε} = ∅ := by
      ext ⟨x, hx_mem⟩
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      rw [Metric.mem_sphere, dist_zero_right] at hx_mem
      have hx_norm : ‖x‖ = 1 := hx_mem
      have h_norm_sq : ‖x‖ ^ 2 = ∑ i : Fin n, ‖x i‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq x
      have h1 : ‖x ⟨0, h⟩‖ ^ 2 ≤ ∑ i : Fin n, ‖x i‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ (⟨0, h⟩ : Fin n))
      have h2 : ∑ i : Fin n, ‖x i‖ ^ 2 = 1 := by
        rw [← h_norm_sq, hx_norm]; norm_num
      have h3 : ‖x ⟨0, h⟩‖ ^ 2 ≤ 1 := by linarith
      have h4 : ‖x ⟨0, h⟩‖ ≤ 1 := by
        nlinarith [norm_nonneg (x ⟨0, h⟩)]
      have h5 : |x ⟨0, h⟩| ≤ 1 := by rwa [Real.norm_eq_abs] at h4
      linarith [le_abs_self (x ⟨0, h⟩)]
    rw [h_empty, show sphereVolume n ∅ = 0 from measure_empty]
    simp
  case isFalse => rfl



/-- Real analysis lemma: $\sqrt{1 - \varepsilon^{2}} \le \exp(-\varepsilon^{2}/2)$,
obtained from $1 - x \le e^{-x}$ and the identity $\sqrt{e^{-t}} = e^{-t/2}$. -/
theorem sqrt_one_sub_sq_le_exp (ε : ℝ) :
    Real.sqrt (1 - ε ^ 2) ≤ Real.exp (-(ε ^ 2 / 2)) := by
  have h_key : 1 - ε ^ 2 ≤ Real.exp (-(ε ^ 2)) := by
    have h := Real.add_one_le_exp (-(ε ^ 2))
    linarith
  have h_sqrt_exp : Real.sqrt (Real.exp (-(ε ^ 2))) = Real.exp (-(ε ^ 2 / 2)) := by
    rw [← Real.exp_half (-(ε ^ 2))]
    ring_nf
  calc Real.sqrt (1 - ε ^ 2)
      ≤ Real.sqrt (Real.exp (-(ε ^ 2))) := Real.sqrt_le_sqrt h_key
    _ = Real.exp (-(ε ^ 2 / 2)) := h_sqrt_exp

/-- Real analysis lemma: for $1/\sqrt{2} \le \varepsilon \le 1$,
$1/(2\varepsilon) \le \exp(-\varepsilon^{2}/2)$. -/
theorem inv_two_mul_le_exp (ε : ℝ) (hε_lb : 1 / Real.sqrt 2 ≤ ε) (hε_ub : ε ≤ 1) :
    1 / (2 * ε) ≤ Real.exp (-(ε ^ 2 / 2)) := by
  have hε_pos : (0 : ℝ) < ε := by
    have : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
    linarith
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num)
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2)
  have hε_sq_lb : (1 : ℝ) / 2 ≤ ε ^ 2 := by
    have h1 : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) ≤ ε * ε :=
      mul_le_mul hε_lb hε_lb (by positivity) (le_of_lt hε_pos)
    have h2 : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / 2 := by
      rw [← sq, div_pow, one_pow, hsqrt2_sq]
    nlinarith
  suffices h_main : Real.exp (ε ^ 2 / 2) ≤ 2 * ε by
    have h_exp_inv : Real.exp (-(ε ^ 2 / 2)) = (Real.exp (ε ^ 2 / 2))⁻¹ := by
      rw [Real.exp_neg]
    rw [h_exp_inv, show (1 : ℝ) / (2 * ε) = (2 * ε)⁻¹ from one_div _]
    exact inv_anti₀ (Real.exp_pos _) h_main
  have hε2_half_nonneg : (0 : ℝ) ≤ ε ^ 2 / 2 := by positivity
  have hε2_half_lt_one : ε ^ 2 / 2 < 1 := by nlinarith
  have h_exp_bound : Real.exp (ε ^ 2 / 2) ≤ 1 / (1 - ε ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hε2_half_nonneg hε2_half_lt_one
  suffices h2 : 1 / (1 - ε ^ 2 / 2) ≤ 2 * ε from le_trans h_exp_bound h2
  have h_denom_pos : (0 : ℝ) < 1 - ε ^ 2 / 2 := by nlinarith
  rw [div_le_iff₀ h_denom_pos]
  nlinarith [sq_nonneg (1 - ε)]

/-- Raising the bound $r \le e^{-\varepsilon^{2}/2}$ to the $n$-th power yields
$r^{n} \le \exp(-n \varepsilon^{2}/2)$. -/
theorem pow_le_exp_of_le {r ε : ℝ} {n : ℕ} (hr : 0 ≤ r)
    (h : r ≤ Real.exp (-(ε ^ 2 / 2))) :
    r ^ n ≤ Real.exp (-(↑n * ε ^ 2 / 2)) := by
  calc r ^ n
      ≤ (Real.exp (-(ε ^ 2 / 2))) ^ n := pow_le_pow_left₀ hr h n
    _ = Real.exp (↑n * (-(ε ^ 2 / 2))) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (-(↑n * ε ^ 2 / 2)) := by congr 1; ring


end SphericalCap

namespace SphericalCap

/-- Contrapositive helper: if the normalized measure of some set $A$ is positive, then the
total surface volume of $S^{n-1}$ is nonzero (i.e. the sphere is genuinely $(n-1)$-dimensional). -/
theorem sphereVolume_pos_of_normalizedSphereMeasure_pos {n : ℕ}
    {A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))}
    (h : normalizedSphereMeasure A > 0) : sphereVolume n Set.univ ≠ 0 := by
  intro h0
  have : normalizedSphereMeasure A = 0 := by
    unfold normalizedSphereMeasure
    have : (sphereVolume n Set.univ).toReal = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mpr (Or.inl h0)
    rw [this, div_zero]
  linarith


/-- A set of positive normalized sphere measure is nonempty. -/
theorem normalizedSphereMeasure_nonempty_of_pos {n : ℕ}
    (A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
    (h : normalizedSphereMeasure A > 0) : A.Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have : normalizedSphereMeasure A = 0 := by
    unfold normalizedSphereMeasure
    rw [hempty, measure_empty, ENNReal.toReal_zero, zero_div]
  linarith







end SphericalCap
