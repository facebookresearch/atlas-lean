/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.FKN
import Atlas.BooleanFunctions.code.Influence
import Atlas.BooleanFunctions.code.InfluenceFourier
import Atlas.BooleanFunctions.code.MonotoneFourier
import Atlas.BooleanFunctions.code.FourierConcentration
import Atlas.BooleanFunctions.code.Stability
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace BooleanFourier

def IsBoolFnJunta {n : ℕ} (g : (Fin n → Bool) → Bool) (J : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ J ∧
    ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → g x = g y

noncomputable def boolL2Dist {n : ℕ} (f g : (Fin n → Bool) → Bool) : ℝ :=
  lpNorm 2 (fun x => liftPM f x - liftPM g x)

def restrictToCoords {n : ℕ} (f : (Fin n → Bool) → Bool)
    (J : Finset (Fin n)) : (Fin n → Bool) → Bool :=
  fun x => f (fun i => if i ∈ J then x i else false)

lemma isBoolFnJunta_restrictToCoords {n : ℕ} (f : (Fin n → Bool) → Bool)
    (J : Finset (Fin n)) : IsBoolFnJunta (restrictToCoords f J) J.card := by
  refine ⟨J, le_refl _, fun x y h => ?_⟩
  simp only [restrictToCoords]
  congr 1
  funext i
  split_ifs with hi
  · exact h i hi
  · rfl

lemma log_two_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
  linarith [Real.log_two_gt_d9]

lemma le_rpow_two_of_nonneg (x : ℝ) (hx : 0 ≤ x) : x ≤ (2 : ℝ) ^ x := by
  by_cases hx1 : x ≤ 1
  · calc x ≤ 1 := hx1
      _ = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2 : ℝ) ^ x :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hx
  · simp only [not_le] at hx1
    have hln2_half : (1 : ℝ) / 2 < Real.log 2 := log_two_gt_half
    have heq : (2 : ℝ) ^ x = Real.exp (Real.log 2 * x) :=
      Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) x
    have h_lower : 1 + Real.log 2 * x ≤ (2 : ℝ) ^ x := by
      rw [heq]; linarith [Real.add_one_le_exp (Real.log 2 * x)]
    by_cases hx2 : x ≤ 2
    · nlinarith
    · simp only [not_le] at hx2
      have h_chain : (2 : ℝ) ^ x ≥ 4 * (1 + Real.log 2 * (x - 2)) := by
        have heq2 : (2 : ℝ) ^ x = (2:ℝ)^(2:ℝ) * (2:ℝ)^(x-2) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; ring_nf
        rw [heq2]
        have h22' : (2:ℝ)^(2:ℝ) = 4 := by
          rw [show (2:ℝ) ^ (2:ℝ) = ((2:ℝ)^(2:ℕ) : ℝ) from by norm_cast]; norm_num
        rw [h22']
        have hlower2 : 1 + Real.log 2 * (x-2) ≤ (2:ℝ) ^ (x-2) := by
          have heq3 : (2 : ℝ) ^ (x-2) = Real.exp (Real.log 2 * (x-2)) :=
            Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) (x-2)
          rw [heq3]; linarith [Real.add_one_le_exp (Real.log 2 * (x-2))]
        linarith [mul_le_mul_of_nonneg_left hlower2 (by norm_num : (0:ℝ) ≤ 4)]
      nlinarith

open Real Finset in
noncomputable def fourierTrunc {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (J : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (· ⊆ J),
    fourierCoeff f S * chi S x

noncomputable def fourierTruncBool {n : ℕ} (f : (Fin n → Bool) → Bool)
    (J : Finset (Fin n)) : (Fin n → Bool) → Bool :=
  fun x => if (0 : ℝ) ≤ fourierTrunc (liftPM f) J x then true else false

lemma isBoolFnJunta_fourierTruncBool {n : ℕ} (f : (Fin n → Bool) → Bool)
    (J : Finset (Fin n)) : IsBoolFnJunta (fourierTruncBool f J) J.card := by
  refine ⟨J, le_refl _, fun x y h => ?_⟩
  unfold fourierTruncBool

  have htrunc : fourierTrunc (liftPM f) J x = fourierTrunc (liftPM f) J y := by
    unfold fourierTrunc
    apply Finset.sum_congr rfl
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    congr 1
    unfold chi
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    exact h i (hS hi)
  rw [htrunc]

lemma sign_rounding_sq_bound (a r : ℝ) (ha : a = 1 ∨ a = -1) :
    (a - (if (0:ℝ) ≤ r then 1 else -1))^2 ≤ 4 * (a - r)^2 := by
  rcases ha with ha | ha <;> subst ha <;> split_ifs with hr
  · simp; positivity
  · push_neg at hr; nlinarith [sq_nonneg (1 - r)]
  · nlinarith [sq_nonneg (-1 - r)]
  · push_neg at hr; simp; positivity

lemma liftPM_values {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    liftPM f x = 1 ∨ liftPM f x = -1 := by
  simp only [liftPM, boolToReal]; cases f x <;> simp

lemma lpNorm_two_eq_sqrt {n : ℕ} (h : (Fin n → Bool) → ℝ) :
    lpNorm 2 h = Real.sqrt ((1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, (h x) ^ 2) := by
  simp only [lpNorm, Real.sqrt_eq_rpow]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [show (2:ℝ) = (↑(2:ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  exact sq_abs (h x)

lemma fourierCoeff_of_chi_sum {n : ℕ} (F : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun x => ∑ T ∈ F, c T * chi T x) S =
      if S ∈ F then c S else 0 := by
  simp only [fourierCoeff]

  have hstep1 : ∀ x : Fin n → Bool,
      (∑ T ∈ F, c T * chi T x) * chi S x =
      ∑ T ∈ F, c T * (chi T x * chi S x) := by
    intro x; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro T _; ring
  simp_rw [hstep1]

  rw [show (1 / (2:ℝ)^n) * ∑ x : Fin n → Bool, ∑ T ∈ F, c T * (chi T x * chi S x) =
      ∑ T ∈ F, c T * ((1 / (2:ℝ)^n) * ∑ x : Fin n → Bool, chi T x * chi S x) from by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro T _
    rw [← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _; ring]
  simp_rw [sum_chi_mul_chi_eq]
  simp_rw [show ∀ T : Finset (Fin n),
      c T * (1 / (2:ℝ)^n * if T = S then (2:ℝ)^n else 0) =
      if T = S then c T else 0 from by
    intro T; split_ifs with h
    · field_simp
    · ring]
  rw [Finset.sum_ite_eq']

open Finset in
theorem friedgut_l2_bridge {n : ℕ} (f : (Fin n → Bool) → Bool) (J : Finset (Fin n)) :
    ∃ g : (Fin n → Bool) → Bool,
      IsBoolFnJunta g J.card ∧
      boolL2Dist f g ≤ 2 * Real.sqrt (∑ S ∈ (univ : Finset (Finset (Fin n))).filter
        (fun S => ¬(S ⊆ J)), fourierCoeff (liftPM f) S ^ 2) := by
  classical
  refine ⟨fourierTruncBool f J, isBoolFnJunta_fourierTruncBool f J, ?_⟩
  set g := fourierTruncBool f J
  set W := ∑ S ∈ (univ : Finset (Finset (Fin n))).filter
    (fun S => ¬(S ⊆ J)), fourierCoeff (liftPM f) S ^ 2

  have h_l2_sqrt : boolL2Dist f g =
      Real.sqrt ((1 / (2:ℝ)^n) * ∑ x : Fin n → Bool,
        (liftPM f x - liftPM g x) ^ 2) :=
    lpNorm_two_eq_sqrt _
  rw [h_l2_sqrt]

  have h_pointwise : ∀ x : Fin n → Bool,
      (liftPM f x - liftPM g x) ^ 2 ≤
        4 * (liftPM f x - fourierTrunc (liftPM f) J x) ^ 2 := by
    intro x
    have ha := liftPM_values f x
    have hg_val : liftPM g x =
        if (0:ℝ) ≤ fourierTrunc (liftPM f) J x then 1 else -1 := by
      show boolToReal (g x) = _
      simp only [g, fourierTruncBool]
      split_ifs <;> simp [boolToReal]
    rw [hg_val]
    exact sign_rounding_sq_bound (liftPM f x) (fourierTrunc (liftPM f) J x) ha

  have h_diff_expansion : ∀ x : Fin n → Bool,
      liftPM f x - fourierTrunc (liftPM f) J x =
        ∑ S ∈ univ.filter (fun S => ¬(S ⊆ J)),
          fourierCoeff (liftPM f) S * chi S x := by
    intro x
    have hfe := fourier_expansion (liftPM f) x
    have hsplit : ∑ S : Finset (Fin n), fourierCoeff (liftPM f) S * chi S x =
        (∑ S ∈ univ.filter (· ⊆ J), fourierCoeff (liftPM f) S * chi S x) +
        (∑ S ∈ univ.filter (fun S => ¬(S ⊆ J)), fourierCoeff (liftPM f) S * chi S x) := by
      rw [← Finset.sum_filter_add_sum_filter_not univ (· ⊆ J)]
    rw [hfe, hsplit]; simp only [fourierTrunc]; ring

  have h_parseval_tail : (1 / (2:ℝ)^n) * ∑ x : Fin n → Bool,
      (liftPM f x - fourierTrunc (liftPM f) J x)^2 = W := by
    set F := univ.filter (fun S : Finset (Fin n) => ¬(S ⊆ J))
    set tail : (Fin n → Bool) → ℝ := fun x =>
      ∑ S ∈ F, fourierCoeff (liftPM f) S * chi S x
    have h_eq_tail : ∀ x,
        (liftPM f x - fourierTrunc (liftPM f) J x)^2 = (tail x)^2 := by
      intro x; congr 1; exact h_diff_expansion x
    simp_rw [h_eq_tail]
    rw [← parseval tail]

    have h_coeff : ∀ S : Finset (Fin n),
        fourierCoeff tail S = if S ∈ F then fourierCoeff (liftPM f) S else 0 :=
      fun S => fourierCoeff_of_chi_sum F _ S
    simp_rw [h_coeff]

    have : ∑ S : Finset (Fin n),
        (if S ∈ F then fourierCoeff (liftPM f) S else 0) ^ 2 = W := by
      conv_lhs =>
        arg 2; ext S
        rw [show (if S ∈ F then fourierCoeff (liftPM f) S else 0)^2 =
            if S ∈ F then fourierCoeff (liftPM f) S ^ 2 else 0 from by
          split_ifs <;> simp]
      simp_rw [show ∀ S : Finset (Fin n), S ∈ F ↔ ¬(S ⊆ J) from
        fun S => by simp [F, Finset.mem_filter]]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    exact this

  have h_sum_bound : (1 / (2:ℝ)^n) * ∑ x,
      (liftPM f x - liftPM g x)^2 ≤ 4 * W := by
    have hc : (0:ℝ) ≤ 1 / (2:ℝ)^n := by positivity
    calc (1 / (2:ℝ)^n) * ∑ x, (liftPM f x - liftPM g x)^2
        ≤ (1 / (2:ℝ)^n) * ∑ x, (4 * (liftPM f x - fourierTrunc (liftPM f) J x)^2) := by
          apply mul_le_mul_of_nonneg_left _ hc
          exact Finset.sum_le_sum (fun x _ => h_pointwise x)
      _ = 4 * ((1 / (2:ℝ)^n) * ∑ x, (liftPM f x - fourierTrunc (liftPM f) J x)^2) := by
          simp_rw [Finset.mul_sum]; ring_nf
      _ = 4 * W := by rw [h_parseval_tail]

  have hW_nonneg : 0 ≤ W := Finset.sum_nonneg (fun S _ => sq_nonneg _)
  calc Real.sqrt ((1 / (2:ℝ)^n) * ∑ x, (liftPM f x - liftPM g x)^2)
      ≤ Real.sqrt (4 * W) := Real.sqrt_le_sqrt h_sum_bound
    _ = 2 * Real.sqrt W := by
        have h4W : (4:ℝ) * W = (2 * Real.sqrt W)^2 := by
          rw [mul_pow, Real.sq_sqrt hW_nonneg]; ring
        rw [h4W, Real.sqrt_sq (by positivity)]

end BooleanFourier
