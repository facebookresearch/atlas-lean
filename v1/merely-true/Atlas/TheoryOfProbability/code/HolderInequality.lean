/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Hölder's inequality**. For Hölder-conjugate exponents `p, q ≥ 1` with
`1/p + 1/q = 1`, and `f ∈ L^p(μ)`, `g ∈ L^q(μ)`:
`∫ |f · g| dμ ≤ (∫ |f|^p dμ)^{1/p} · (∫ |g|^q dμ)^{1/q}`,
i.e. `‖fg‖_1 ≤ ‖f‖_p · ‖g‖_q`. -/
theorem holder_inequality {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ x, |f x * g x| ∂μ ≤
      (∫ x, |f x| ^ p ∂μ) ^ (1 / p) * (∫ x, |g x| ^ q ∂μ) ^ (1 / q) := by
  have h1 : ∀ x, |f x * g x| = ‖f x‖ * ‖g x‖ := by
    intro x
    rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 : ∀ x, |f x| ^ p = ‖f x‖ ^ p := by
    intro x
    rw [Real.norm_eq_abs]
  have h3 : ∀ x, |g x| ^ q = ‖g x‖ ^ q := by
    intro x
    rw [Real.norm_eq_abs]
  simp_rw [h1, h2, h3]
  exact integral_mul_norm_le_Lp_mul_Lq hpq hf hg
