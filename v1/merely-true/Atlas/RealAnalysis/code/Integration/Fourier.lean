/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Integration

open MeasureTheory Real Filter Set intervalIntegral Topology

/-- The `n`-th cosine Fourier coefficient of a function `f : ℝ → ℝ`, defined as
`(1/π) ∫_{-π}^{π} f(x) · cos(n·x) dx`. This corresponds to the coefficient `bₙ`
in the Fourier series expansion of `f`. -/
noncomputable def fourierCoefficientCos (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (1 / Real.pi) * ∫ x in (-Real.pi)..Real.pi, f x * Real.cos (n * x)

/-- **Riemann–Lebesgue lemma** (for continuously differentiable functions on `[-π, π]`).

If `f : ℝ → ℝ` is continuously differentiable on `[-π, π]`, then both Fourier-coefficient
integrals tend to zero as `n → ∞`:
- `(1/π) ∫_{-π}^{π} f(x) · sin(n·x) dx → 0`, and
- `(1/π) ∫_{-π}^{π} f(x) · cos(n·x) dx → 0`.

The proof uses integration by parts to express each integral in terms of a bounded
antiderivative of `sin(n·x)` (resp. `cos(n·x)`) of size `O(1/n)`, then squeezes to zero. -/
theorem riemann_lebesgue (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Icc (-Real.pi) Real.pi)) :
    Filter.Tendsto (fun n : ℕ => (1/Real.pi) * ∫ x in (-Real.pi)..Real.pi, f x * Real.sin (n * x))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n : ℕ => (1/Real.pi) * ∫ x in (-Real.pi)..Real.pi, f x * Real.cos (n * x))
      Filter.atTop (nhds 0) := by
  have hpi : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hIcc_uIcc : Set.Icc (-Real.pi) Real.pi = Set.uIcc (-Real.pi) Real.pi :=
    (Set.uIcc_of_le hpi).symm
  have hf_ac : AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi := by
    rw [hIcc_uIcc] at hf
    obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
      (convex_uIcc (-Real.pi) Real.pi) isCompact_uIcc
    exact hK.absolutelyContinuousOnInterval
  have hf_deriv_int : IntervalIntegrable (deriv f) volume (-Real.pi) Real.pi :=
    hf_ac.intervalIntegrable_deriv
  constructor
  ·
    set C := ‖f Real.pi‖ + ‖f (-Real.pi)‖ + ∫ x in (-Real.pi)..Real.pi, ‖deriv f x‖
    suffices h : Tendsto (fun n : ℕ => ∫ x in (-Real.pi)..Real.pi, f x * Real.sin (↑n * x))
        atTop (nhds 0) by
      have h2 := h.const_mul (1 / Real.pi)
      simp only [mul_zero] at h2; exact h2
    apply squeeze_zero_norm (a := fun n : ℕ => C / ↑n)
    · intro n
      by_cases hn : n = 0
      · simp [hn]
      · have hn' : 0 < n := Nat.pos_of_ne_zero hn
        have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn'
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        let g := fun x : ℝ => -Real.cos (↑n * x) / (↑n : ℝ)
        have hg_deriv : deriv g = fun x => Real.sin (↑n * x) := by
          ext x
          have h1 : HasDerivAt (fun x => (n : ℝ) * x) (n : ℝ) x := by
            simpa using (hasDerivAt_id' x).const_mul (n : ℝ)
          have h2 : HasDerivAt (fun x => Real.cos ((n : ℝ) * x)) (-Real.sin ((n : ℝ) * x) * n) x :=
            (Real.hasDerivAt_cos ((n : ℝ) * x)).comp x h1
          have h3 : HasDerivAt (fun x => -Real.cos ((n : ℝ) * x)) (Real.sin ((n : ℝ) * x) * n) x := by
            convert h2.neg using 1; ring
          have h4 : HasDerivAt g (Real.sin ((n : ℝ) * x) * n / n) x := h3.div_const (n : ℝ)
          rw [h4.deriv]; field_simp
        have hg_ac : AbsolutelyContinuousOnInterval g (-Real.pi) Real.pi := by
          have hgc : ContDiff ℝ 1 g := by
            apply ContDiff.div_const; apply ContDiff.neg
            exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
          obtain ⟨K, hK⟩ := hgc.contDiffOn.exists_lipschitzOnWith
            (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
            (convex_uIcc (-Real.pi) Real.pi) isCompact_uIcc
          exact hK.absolutelyContinuousOnInterval
        have hg_bound : ∀ x : ℝ, ‖g x‖ ≤ 1 / (↑n : ℝ) := by
          intro x
          simp only [g, norm_div, norm_neg, Real.norm_natCast]
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
          rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
        have ibp := hf_ac.integral_mul_deriv_eq_deriv_mul hg_ac
        have hrw : ∫ x in (-Real.pi)..Real.pi, f x * Real.sin (↑n * x) =
            ∫ x in (-Real.pi)..Real.pi, f x * deriv g x := by
          congr 1; ext x; rw [hg_deriv]
        rw [hrw, ibp]
        calc ‖f Real.pi * g Real.pi - f (-Real.pi) * g (-Real.pi) -
                ∫ x in (-Real.pi)..Real.pi, deriv f x * g x‖
            ≤ ‖f Real.pi * g Real.pi‖ + ‖f (-Real.pi) * g (-Real.pi)‖ +
              ‖∫ x in (-Real.pi)..Real.pi, deriv f x * g x‖ := by
              calc _ ≤ ‖f Real.pi * g Real.pi - f (-Real.pi) * g (-Real.pi)‖ +
                  ‖∫ x in (-Real.pi)..Real.pi, deriv f x * g x‖ := norm_sub_le _ _
                _ ≤ _ := by gcongr; exact norm_sub_le _ _
          _ ≤ ‖f Real.pi‖ / ↑n + ‖f (-Real.pi)‖ / ↑n +
              (∫ x in (-Real.pi)..Real.pi, ‖deriv f x‖) / ↑n := by
              gcongr
              · calc ‖f Real.pi * g Real.pi‖ = ‖f Real.pi‖ * ‖g Real.pi‖ := norm_mul _ _
                  _ ≤ ‖f Real.pi‖ * (1 / ↑n) := by gcongr; exact hg_bound _
                  _ = ‖f Real.pi‖ / ↑n := by ring
              · calc ‖f (-Real.pi) * g (-Real.pi)‖ =
                      ‖f (-Real.pi)‖ * ‖g (-Real.pi)‖ := norm_mul _ _
                  _ ≤ ‖f (-Real.pi)‖ * (1 / ↑n) := by gcongr; exact hg_bound _
                  _ = ‖f (-Real.pi)‖ / ↑n := by ring
              · calc ‖∫ x in (-Real.pi)..Real.pi, deriv f x * g x‖
                    ≤ ∫ x in (-Real.pi)..Real.pi, ‖deriv f x‖ * (1 / ↑n) := by
                      apply intervalIntegral.norm_integral_le_of_norm_le hpi
                      · filter_upwards with x; intro _
                        calc ‖deriv f x * g x‖ = ‖deriv f x‖ * ‖g x‖ := norm_mul _ _
                          _ ≤ ‖deriv f x‖ * (1 / ↑n) := by gcongr; exact hg_bound _
                      · exact hf_deriv_int.norm.mul_const _
                  _ = (∫ x in (-Real.pi)..Real.pi, ‖deriv f x‖) * (1 / ↑n) :=
                      intervalIntegral.integral_mul_const _ _
                  _ = (∫ x in (-Real.pi)..Real.pi, ‖deriv f x‖) / ↑n := by ring
          _ = C / ↑n := by ring
    · have : Tendsto (fun n : ℕ => C * (1 / (↑n : ℝ))) atTop (nhds (C * 0)) :=
        tendsto_one_div_atTop_nhds_zero_nat.const_mul C
      simp only [mul_zero, mul_one_div] at this; exact this
  ·
    set C := ‖f Real.pi‖ + ‖f (-Real.pi)‖ + ∫ x in (-Real.pi)..Real.pi, ‖deriv f x‖
    suffices h : Tendsto (fun n : ℕ => ∫ x in (-Real.pi)..Real.pi, f x * Real.cos (↑n * x))
        atTop (nhds 0) by
      have h2 := h.const_mul (1 / Real.pi)
      simp only [mul_zero] at h2; exact h2
    apply squeeze_zero_norm' (a := fun n : ℕ => C / ↑n)
    ·
      filter_upwards [Ici_mem_atTop 1] with n (hn : 1 ≤ n)
      have hn' : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn'
      have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos

      let g := fun x : ℝ => Real.sin (↑n * x) / (↑n : ℝ)
      have hg_deriv : deriv g = fun x => Real.cos (↑n * x) := by
        ext x
        have h1 : HasDerivAt (fun x => (n : ℝ) * x) (n : ℝ) x := by
          simpa using (hasDerivAt_id' x).const_mul (n : ℝ)
        have h2 : HasDerivAt (fun x => Real.sin ((n : ℝ) * x)) (Real.cos ((n : ℝ) * x) * n) x :=
          (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x h1
        have h3 : HasDerivAt g (Real.cos ((n : ℝ) * x) * n / n) x := h2.div_const (n : ℝ)
        rw [h3.deriv]; field_simp
      have hg_ac : AbsolutelyContinuousOnInterval g (-Real.pi) Real.pi := by
        have hgc : ContDiff ℝ 1 g := by
          apply ContDiff.div_const
          exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
        obtain ⟨K, hK⟩ := hgc.contDiffOn.exists_lipschitzOnWith
          (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
          (convex_uIcc (-Real.pi) Real.pi) isCompact_uIcc
        exact hK.absolutelyContinuousOnInterval
      have hg_bound : ∀ x : ℝ, ‖g x‖ ≤ 1 / (↑n : ℝ) := by
        intro x
        simp only [g, norm_div, Real.norm_natCast]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _

      have hg_pi : g Real.pi = 0 := by
        simp [g, Real.sin_nat_mul_pi]
      have hg_neg_pi : g (-Real.pi) = 0 := by
        simp [g, Real.sin_nat_mul_pi, mul_neg]
      have ibp := hf_ac.integral_mul_deriv_eq_deriv_mul hg_ac
      have hrw : ∫ x in (-Real.pi)..Real.pi, f x * Real.cos (↑n * x) =
          ∫ x in (-Real.pi)..Real.pi, f x * deriv g x := by
        congr 1; ext x; rw [hg_deriv]
      rw [hrw, ibp, hg_pi, hg_neg_pi]
      simp only [mul_zero, sub_zero, zero_sub, norm_neg]

      calc ‖∫ x in (-Real.pi)..Real.pi, deriv f x * g x‖
          ≤ ∫ x in (-Real.pi)..Real.pi, ‖deriv f x‖ * (1 / ↑n) := by
            apply intervalIntegral.norm_integral_le_of_norm_le hpi
            · filter_upwards with x; intro _
              calc ‖deriv f x * g x‖ = ‖deriv f x‖ * ‖g x‖ := norm_mul _ _
                _ ≤ ‖deriv f x‖ * (1 / ↑n) := by gcongr; exact hg_bound _
            · exact hf_deriv_int.norm.mul_const _
        _ = (∫ x in (-Real.pi)..Real.pi, ‖deriv f x‖) * (1 / ↑n) :=
            intervalIntegral.integral_mul_const _ _
        _ = (∫ x in (-Real.pi)..Real.pi, ‖deriv f x‖) / ↑n := by ring
        _ ≤ C / ↑n := by
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
            linarith [norm_nonneg (f Real.pi), norm_nonneg (f (-Real.pi))]
    · have : Tendsto (fun n : ℕ => C * (1 / (↑n : ℝ))) atTop (nhds (C * 0)) :=
        tendsto_one_div_atTop_nhds_zero_nat.const_mul C
      simp only [mul_zero, mul_one_div] at this; exact this

end Integration
