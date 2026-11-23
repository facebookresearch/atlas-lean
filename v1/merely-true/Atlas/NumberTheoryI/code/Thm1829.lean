/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Real Asymptotics Filter
open scoped Topology

namespace HarmonicSumAsymptotics

lemma abs_harmonic_sub_log_sub_euler (n : ℕ) (hn : 1 ≤ n) :
    |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant| ≤ 1 / n := by
  have hn_ne : n ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_le]
  refine ⟨?_, ?_⟩
  ·
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
    simp only [Real.eulerMascheroniSeq', hn_ne, ↓reduceIte] at h
    linarith [show (0 : ℝ) ≤ 1 / n from by positivity]
  ·
    have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
    unfold Real.eulerMascheroniSeq at h


    have log_bound : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / (n : ℝ) := by
      rw [← Real.log_div (by linarith) (by linarith)]
      have : ((n : ℝ) + 1) / n = 1 + 1 / n := by field_simp
      rw [this]
      linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / n)]
    linarith

lemma log_sub_log_floor_le (x : ℝ) (hx : 1 ≤ x) :
    Real.log x - Real.log ⌊x⌋₊ ≤ 1 / ⌊x⌋₊ := by
  have hn_pos : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hx
  calc Real.log x - Real.log ⌊x⌋₊
      = Real.log (x / ⌊x⌋₊) := by rw [Real.log_div (by linarith) (by linarith)]
    _ ≤ Real.log ((⌊x⌋₊ + 1) / ⌊x⌋₊) := by
        apply Real.log_le_log (div_pos (by linarith) hn_pos)
        exact div_le_div_of_nonneg_right (Nat.lt_floor_add_one x).le hn_pos.le
    _ = Real.log (1 + 1 / ⌊x⌋₊) := by congr 1; field_simp
    _ ≤ 1 / ⌊x⌋₊ := by
        linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ⌊x⌋₊)]

theorem harmonic_floor_eq_log_add_euler_mascheroni_add_bigO :
    (fun x : ℝ ↦ (harmonic ⌊x⌋₊ : ℝ) - Real.log x - Real.eulerMascheroniConstant) =O[atTop]
    (fun x ↦ x⁻¹) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  simp only [Real.norm_eq_abs, abs_inv]
  have hx1 : 1 ≤ x := by linarith
  have hx_pos : 0 < x := by linarith
  rw [abs_of_pos hx_pos]

  have hn : 1 ≤ ⌊x⌋₊ := Nat.floor_pos.mpr hx1
  have hn_pos : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hn

  have part1_lower : 0 ≤ (harmonic ⌊x⌋₊ : ℝ) - Real.log ⌊x⌋₊ - eulerMascheroniConstant := by
    have h := eulerMascheroniConstant_lt_eulerMascheroniSeq' ⌊x⌋₊
    simp only [eulerMascheroniSeq', show ⌊x⌋₊ ≠ 0 from by omega, ↓reduceIte] at h
    linarith
  have part1_upper :
      (harmonic ⌊x⌋₊ : ℝ) - Real.log ⌊x⌋₊ - eulerMascheroniConstant ≤ 1 / ⌊x⌋₊ := by
    have h := eulerMascheroniSeq_lt_eulerMascheroniConstant ⌊x⌋₊
    unfold eulerMascheroniSeq at h
    have : Real.log ((⌊x⌋₊ : ℝ) + 1) - Real.log ⌊x⌋₊ ≤ 1 / (⌊x⌋₊ : ℝ) := by
      rw [← Real.log_div (by linarith) (by linarith)]
      have : ((⌊x⌋₊ : ℝ) + 1) / ⌊x⌋₊ = 1 + 1 / ⌊x⌋₊ := by field_simp
      rw [this]
      linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ⌊x⌋₊)]
    linarith

  have part2_lower : 0 ≤ Real.log x - Real.log ⌊x⌋₊ :=
    sub_nonneg.mpr (Real.log_le_log hn_pos (Nat.floor_le (by linarith)))
  have part2_upper : Real.log x - Real.log ⌊x⌋₊ ≤ 1 / ⌊x⌋₊ :=
    log_sub_log_floor_le x hx1

  have key : |(harmonic ⌊x⌋₊ : ℝ) - Real.log x - eulerMascheroniConstant| ≤ 1 / ⌊x⌋₊ := by
    rw [abs_le]; constructor <;> nlinarith

  have floor_bound : (1 : ℝ) / ⌊x⌋₊ ≤ 2 / x := by
    rw [div_le_div_iff₀ hn_pos hx_pos]
    nlinarith [Nat.lt_floor_add_one x]
  linarith [show 2 / x = 2 * x⁻¹ from by ring]

theorem euler_mascheroni_eq_lim_harmonic_sub_log :
    Tendsto (fun n : ℕ ↦ (harmonic n : ℝ) - Real.log n) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
  Real.tendsto_harmonic_sub_log

end HarmonicSumAsymptotics


namespace Theorem1829
  export HarmonicSumAsymptotics (abs_harmonic_sub_log_sub_euler log_sub_log_floor_le
    harmonic_floor_eq_log_add_euler_mascheroni_add_bigO euler_mascheroni_eq_lim_harmonic_sub_log)
end Theorem1829
