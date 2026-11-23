/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Atlas.DifferentialAnalysis.code.SchwartzTranslation

open scoped SchwartzMap Topology
open Metric Filter

noncomputable section

namespace SchwartzMap

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quantitative continuity of translation on Schwartz space: for any `(k, n)`, the Schwartz
`(k,n)`-seminorm of the difference `τ_h φ − φ` is controlled linearly by `‖h‖` for `‖h‖ ≤ 1`,
with constant given by a finite supremum of Schwartz seminorms of `φ`. Used to deduce
continuity of `h ↦ τ_h φ` in `h`. -/
theorem seminorm_translate_sub_le (φ : 𝓢(E, ℂ)) (k n : ℕ) (h : E) (hh : ‖h‖ ≤ 1) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ h φ - φ) ≤
      2 ^ k * (Finset.Iic (k, n + 1)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ * ‖h‖ := by
  set S := (Finset.Iic (k, n + 1)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ
  apply SchwartzMap.seminorm_le_bound ℂ k n
  · positivity
  intro y
  have hcoerce : ⇑(SchwartzMap.compSubConstCLM ℂ h φ - φ) = fun z => φ (z - h) - φ z := by
    ext z; simp [SchwartzMap.compSubConstCLM_apply]
  rw [hcoerce]
  have hsmooth1 : ContDiff ℝ ↑n (fun z => φ (z - h)) :=
    (φ.smooth n).comp (contDiff_id.sub contDiff_const)
  have key_eq : (fun z => φ (z - h) - φ z) = (fun z => φ (z - h)) - (⇑φ) := by ext; rfl
  rw [key_eq, iteratedFDeriv_sub hsmooth1 (φ.smooth n)]
  simp only [Pi.sub_apply, iteratedFDeriv_comp_sub]
  set g := iteratedFDeriv ℝ n (⇑φ)
  by_cases hyk : ‖y‖ = 0
  · by_cases hk : k = 0
    · subst hk; simp only [pow_zero, one_mul]
      have hdiff : ∀ x : E, DifferentiableAt ℝ g x :=
        fun x => (φ.smooth (n + 1)).differentiable_iteratedFDeriv
          (by exact_mod_cast Nat.lt_succ_of_le le_rfl) x
      have hbd : ∀ x : E, ‖fderiv ℝ g x‖ ≤ SchwartzMap.seminorm ℂ 0 (n + 1) φ := by
        intro x; rw [norm_fderiv_iteratedFDeriv]
        simpa using SchwartzMap.le_seminorm ℂ 0 (n + 1) φ x
      have mvt0 := convex_univ (𝕜 := ℝ) |>.norm_image_sub_le_of_norm_fderiv_le
        (fun x _ => hdiff x) (fun x _ => hbd x) (Set.mem_univ y) (Set.mem_univ (y - h))
      have : y - h - y = -h := by abel
      rw [this, norm_neg] at mvt0
      calc ‖g (y - h) - g y‖ ≤ SchwartzMap.seminorm ℂ 0 (n + 1) φ * ‖h‖ := mvt0
        _ ≤ S * ‖h‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            have hsle := Finset.le_sup
              (f := fun m => SchwartzMap.seminorm (𝕜 := ℂ) (E := E) (F := ℂ) m.1 m.2)
              (Finset.mem_Iic.mpr (le_refl (0, n + 1)))
            exact hsle φ
    · simp only [hyk, zero_pow (Nat.pos_of_ne_zero hk).ne', zero_mul]
      positivity
  have hy_pos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hyk)
  have hyk_pos : 0 < ‖y‖ ^ k := pow_pos hy_pos k
  have hdiff : ∀ z ∈ closedBall y 1, DifferentiableAt ℝ g z := by
    intro z _; exact (φ.smooth (n + 1)).differentiable_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_of_le le_rfl) z
  have hfderiv_bound : ∀ z ∈ closedBall y 1,
      ‖fderiv ℝ g z‖ ≤ 2 ^ k * S / ‖y‖ ^ k := by
    intro z hz
    rw [norm_fderiv_iteratedFDeriv (f := ⇑φ)]
    have hsup : (1 + ‖z‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) (⇑φ) z‖ ≤ 2 ^ k * S :=
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n + 1)) le_rfl le_rfl φ z
    have hzy : ‖y‖ ≤ 1 + ‖z‖ := by
      have hd := mem_closedBall.mp hz
      rw [dist_eq_norm] at hd
      calc ‖y‖ = ‖z - (z - y)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖z‖ + ‖z - y‖ := norm_sub_le _ _
        _ ≤ ‖z‖ + 1 := by linarith
        _ = 1 + ‖z‖ := by ring
    have hpow : ‖y‖ ^ k ≤ (1 + ‖z‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) hzy k
    rw [le_div_iff₀ hyk_pos]
    calc ‖iteratedFDeriv ℝ (n + 1) (⇑φ) z‖ * ‖y‖ ^ k
        ≤ ‖iteratedFDeriv ℝ (n + 1) (⇑φ) z‖ * (1 + ‖z‖) ^ k :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (1 + ‖z‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) (⇑φ) z‖ := by ring
      _ ≤ 2 ^ k * S := hsup
  have hyh_mem : y - h ∈ closedBall y 1 := by
    rw [mem_closedBall, dist_comm, dist_eq_norm, sub_sub_cancel]; exact hh
  have mvt := (convex_closedBall y 1).norm_image_sub_le_of_norm_fderiv_le
    hdiff hfderiv_bound (mem_closedBall_self zero_le_one) hyh_mem
  have : y - h - y = -h := by abel
  rw [this, norm_neg] at mvt
  calc ‖y‖ ^ k * ‖g (y - h) - g y‖
      ≤ ‖y‖ ^ k * (2 ^ k * S / ‖y‖ ^ k * ‖h‖) :=
        mul_le_mul_of_nonneg_left mvt (by positivity)
    _ = 2 ^ k * S * ‖h‖ := by field_simp

/-- Cocycle identity for Schwartz translation: the difference of two translates of `φ` at
points `x` and `x₀` factors through translation by `x₀` of the difference `τ_{x − x₀} φ − φ`. -/
theorem compSubConstCLM_sub_eq (φ : 𝓢(E, ℂ)) (x x₀ : E) :
    SchwartzMap.compSubConstCLM ℂ x φ - SchwartzMap.compSubConstCLM ℂ x₀ φ =
    SchwartzMap.compSubConstCLM ℂ x₀ (SchwartzMap.compSubConstCLM ℂ (x - x₀) φ - φ) := by
  have : SchwartzMap.compSubConstCLM ℂ x φ =
      SchwartzMap.compSubConstCLM ℂ x₀ (SchwartzMap.compSubConstCLM ℂ (x - x₀) φ) := by
    rw [SchwartzMap.compSubConstCLM_comp]; congr 1; abel
  rw [this, map_sub]

end SchwartzMap

end
