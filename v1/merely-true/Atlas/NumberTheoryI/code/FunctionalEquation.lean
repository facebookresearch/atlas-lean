/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Complex hiding exp continuous_exp
open Real Filter Topology Asymptotics

noncomputable section

namespace FunctionalEquation

theorem jacobiTheta_modular_S_transform (τ : UpperHalfPlane) :
    jacobiTheta ↑(ModularGroup.S • τ) =
      (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * jacobiTheta (τ : ℂ) :=
  jacobiTheta_S_smul τ

abbrev completedZeta (s : ℂ) : ℂ := completedRiemannZeta s

abbrev completedZeta₀ (s : ℂ) : ℂ := completedRiemannZeta₀ s

theorem gamma_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -↑m) :
    Gamma s ≠ 0 :=
  Complex.Gamma_ne_zero hs

def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

theorem xi_differentiable : Differentiable ℂ xi := by
  apply Differentiable.add
  · apply Differentiable.mul
    · exact (differentiable_id.mul (differentiable_id.sub (differentiable_const 1))).div_const 2
    · exact differentiable_completedZeta₀
  · exact differentiable_const _

theorem xi_eq_mul_completedZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  unfold xi
  rw [completedRiemannZeta_eq]
  have : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

theorem xi_functional_equation (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

lemma completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs_re : 1 ≤ s.re) (hs0 : s ≠ 0) :
    completedRiemannZeta s ≠ 0 := by
  intro h
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs_re
  rw [riemannZeta_def_of_ne_zero hs0, h, zero_div] at hζ
  exact hζ rfl

theorem completedRiemannZeta_zero_re_in_critical_strip (s : ℂ)
    (hs : completedRiemannZeta s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  ·
    by_contra h
    push Not at h
    have h1s_re : 1 ≤ (1 - s).re := by simp [sub_re, one_re]; linarith
    have h1s_ne0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    have hΛ : completedRiemannZeta (1 - s) = 0 := by
      rw [completedRiemannZeta_one_sub]; exact hs
    exact completedRiemannZeta_ne_zero_of_one_le_re h1s_re h1s_ne0 hΛ
  ·
    by_contra h
    push Not at h
    exact completedRiemannZeta_ne_zero_of_one_le_re h hs0 hs

theorem xi_zero_re_in_critical_strip (s : ℂ) (hs : xi s = 0) :
    0 < s.re ∧ s.re < 1 := by

  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; unfold xi at hs; simp at hs
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; unfold xi at hs; simp at hs

  rw [xi_eq_mul_completedZeta hs0 hs1] at hs
  have hfac : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero
  have hΛ : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp hs with h | h
    · exact absurd h hfac
    · exact h
  exact completedRiemannZeta_zero_re_in_critical_strip s hΛ hs0 hs1

theorem xi_entire_functional_equation_and_critical_strip :
    (Differentiable ℂ xi) ∧
    (∀ s : ℂ, xi (1 - s) = xi s) ∧
    (∀ s : ℂ, xi s = 0 → 0 < s.re ∧ s.re < 1) :=
  ⟨xi_differentiable, xi_functional_equation, xi_zero_re_in_critical_strip⟩

end FunctionalEquation
