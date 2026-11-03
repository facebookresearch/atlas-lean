/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.EllipticLowerBound

open scoped SchwartzMap
open TemperedDistribution MvPolynomial

noncomputable section

namespace DifferentialOperators

variable {n : ℕ}

/-- A smooth radial cutoff on `Fin n → ℝ`: a continuous function taking values
in `[0, 1]` that is identically `1` on the closed unit ball and has compact
support.  Used to remove the singularity of `1/P_m(ξ)` at the origin in
the parametrix construction. -/
structure SmoothCutoff (n : ℕ) where
  toFun : (Fin n → ℝ) → ℝ
  eq_one_near_zero : ∀ ξ : Fin n → ℝ, ‖ξ‖ ≤ 1 → toFun ξ = 1
  hasCompactSupport : HasCompactSupport toFun
  nonneg : ∀ ξ, 0 ≤ toFun ξ
  le_one : ∀ ξ, toFun ξ ≤ 1
  continuous_toFun : Continuous toFun

/-- The parametrix symbol associated to a polynomial `P` of order `m` and a
smooth cutoff `φ`: `q(ξ) = (1 − φ(ξ)) / P_m(ξ)` where `P_m` is the principal
symbol, with the convention `q(ξ) = 0` wherever the principal symbol
vanishes. -/
def parametrixSymbol (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (φ : SmoothCutoff n) : (Fin n → ℝ) → ℂ :=
  fun ξ =>
    if evalPrincipalSymbolReal m P ξ = 0 then 0
    else (1 - (φ.toFun ξ : ℂ)) / evalPrincipalSymbolReal m P ξ

/-- The parametrix symbol vanishes on the closed unit ball, since the cutoff
`φ` is identically `1` there. -/
theorem parametrixSymbol_eq_zero_near_zero (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (φ : SmoothCutoff n) (ξ : Fin n → ℝ) (hξ : ‖ξ‖ ≤ 1) :
    parametrixSymbol m P φ ξ = 0 := by
  unfold parametrixSymbol
  have hφ : φ.toFun ξ = 1 := φ.eq_one_near_zero ξ hξ
  split_ifs with h
  · rfl
  · simp [hφ]

/-- For an elliptic polynomial `P` of order `m`, the parametrix symbol is
bounded by `C / ‖ξ‖^m` outside the support of the cutoff.  The constant `C`
comes from the elliptic lower bound on the principal symbol. -/
theorem parametrixSymbol_bound (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (φ : SmoothCutoff n) (hP : IsElliptic n m P) (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Fin n → ℝ,
      ‖parametrixSymbol m P φ ξ‖ ≤ C / ‖ξ‖ ^ m := by
  obtain ⟨c, hc_pos, hc_bound⟩ := elliptic_lower_bound m P hP hn
  refine ⟨c⁻¹, inv_pos.mpr hc_pos, fun ξ => ?_⟩
  by_cases hξ_small : ‖ξ‖ ≤ 1
  · rw [parametrixSymbol_eq_zero_near_zero m P φ ξ hξ_small, norm_zero]
    positivity
  · have hξ_large : 1 < ‖ξ‖ := not_le.mp hξ_small
    have hξ_pos : 0 < ‖ξ‖ := by linarith
    have hξ_ne : ξ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hξ_pos)
    have hPm_ne : evalPrincipalSymbolReal m P ξ ≠ 0 := hP ξ hξ_ne
    have hQ : parametrixSymbol m P φ ξ =
        (1 - (φ.toFun ξ : ℂ)) / evalPrincipalSymbolReal m P ξ := by
      unfold parametrixSymbol; rw [if_neg hPm_ne]
    rw [hQ, norm_div]
    have hPm_pos : 0 < ‖evalPrincipalSymbolReal m P ξ‖ := norm_pos_iff.mpr hPm_ne


    rw [div_le_div_iff₀ hPm_pos (pow_pos hξ_pos m)]

    have hnum_le : ‖(1 : ℂ) - (φ.toFun ξ : ℂ)‖ ≤ 1 := by
      have h1 : (1 : ℂ) - (φ.toFun ξ : ℂ) = ((1 - φ.toFun ξ : ℝ) : ℂ) := by push_cast; ring
      rw [h1, Complex.norm_of_nonneg (by linarith [φ.le_one ξ])]
      linarith [φ.nonneg ξ]

    calc ‖(1 : ℂ) - (φ.toFun ξ : ℂ)‖ * ‖ξ‖ ^ m
        ≤ 1 * ‖ξ‖ ^ m :=
          mul_le_mul_of_nonneg_right hnum_le (pow_nonneg (norm_nonneg _) _)
      _ = ‖ξ‖ ^ m := one_mul _
      _ = c⁻¹ * (c * ‖ξ‖ ^ m) :=
          (inv_mul_cancel_left₀ (ne_of_gt hc_pos) _).symm
      _ ≤ c⁻¹ * ‖evalPrincipalSymbolReal m P ξ‖ :=
          mul_le_mul_of_nonneg_left (hc_bound ξ) (le_of_lt (inv_pos.mpr hc_pos))

/-- The parametrix symbol is continuous on all of `Fin n → ℝ`: locally
constant zero on the unit ball, and continuous as `(1 − φ)/P_m` away
from it (using ellipticity to ensure `P_m ≠ 0`). -/
theorem continuous_parametrixSymbol (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (φ : SmoothCutoff n) (hP : IsElliptic n m P) :
    Continuous (parametrixSymbol m P φ) := by
  rw [continuous_iff_continuousAt]
  intro ξ₀
  by_cases hξ₀ : ‖ξ₀‖ < 1
  ·
    have : parametrixSymbol m P φ =ᶠ[nhds ξ₀] fun _ => (0 : ℂ) := by
      apply Filter.eventually_of_mem
        (Metric.ball_mem_nhds ξ₀ (show 0 < 1 - ‖ξ₀‖ by linarith))
      intro ξ hξ
      rw [Metric.mem_ball] at hξ
      exact parametrixSymbol_eq_zero_near_zero m P φ ξ
        (by linarith [dist_eq_norm ξ ξ₀, norm_sub_norm_le ξ ξ₀])
    exact continuousAt_const.congr this.symm
  ·
    push_neg at hξ₀
    have hξ₀_ne : ξ₀ ≠ 0 := by
      intro h; subst h; simp at hξ₀; linarith
    have hPm_ne : evalPrincipalSymbolReal m P ξ₀ ≠ 0 := hP ξ₀ hξ₀_ne

    have hev : parametrixSymbol m P φ =ᶠ[nhds ξ₀]
        (fun ξ => (1 - (φ.toFun ξ : ℂ)) / evalPrincipalSymbolReal m P ξ) := by
      apply Filter.eventually_of_mem
        ((continuous_evalPrincipalSymbolReal m P).isOpen_preimage {0}ᶜ isOpen_compl_singleton
          |>.mem_nhds (by simp [hPm_ne]))
      intro ξ hξ
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hξ
      simp only [parametrixSymbol, if_neg hξ]

    have hnum_cont : Continuous (fun ξ => (1 : ℂ) - (φ.toFun ξ : ℂ)) :=
      continuous_const.sub (Complex.continuous_ofReal.comp φ.continuous_toFun)
    exact (hnum_cont.continuousAt.div
      (continuous_evalPrincipalSymbolReal m P).continuousAt hPm_ne).congr hev.symm

/-- The parametrix symbol decays like `(1 + ‖ξ‖)^{-m}`: a uniform polynomial
decay estimate, which is the relevant tempered-symbol bound. -/
theorem parametrixSymbol_polynomial_decay (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (φ : SmoothCutoff n) (hP : IsElliptic n m P) (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Fin n → ℝ,
      ‖parametrixSymbol m P φ ξ‖ ≤ C * (1 + ‖ξ‖)⁻¹ ^ m := by
  obtain ⟨C, hC_pos, hC_bound⟩ := parametrixSymbol_bound m P φ hP hn
  refine ⟨C * 2 ^ m, by positivity, fun ξ => ?_⟩
  by_cases hξ_small : ‖ξ‖ ≤ 1
  · rw [parametrixSymbol_eq_zero_near_zero m P φ ξ hξ_small, norm_zero]
    positivity
  · push_neg at hξ_small
    have hξ_pos : 0 < ‖ξ‖ := by linarith


    calc ‖parametrixSymbol m P φ ξ‖
        ≤ C / ‖ξ‖ ^ m := hC_bound ξ
      _ = C * (‖ξ‖⁻¹ ^ m) := by rw [div_eq_mul_inv, inv_pow]
      _ ≤ C * (2 * (1 + ‖ξ‖)⁻¹) ^ m := by
          gcongr
          rw [inv_le_comm₀ hξ_pos (by positivity)]
          rw [mul_inv_rev, inv_inv]
          linarith
      _ = C * 2 ^ m * (1 + ‖ξ‖)⁻¹ ^ m := by rw [mul_pow, mul_assoc]


end DifferentialOperators

end
