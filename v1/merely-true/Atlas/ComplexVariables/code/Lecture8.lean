/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Complex MeasureTheory intervalIntegral Set

noncomputable def complexLineIntegral (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : ℂ :=
  ∫ t in a..b, f (γ t) * deriv γ t

theorem complex_line_integral_substitution
    (f : ℂ → ℂ) (φ : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hφ : DifferentiableOn ℂ φ Ω)
    (hγ_diff : ∀ t ∈ uIcc a b, DifferentiableAt ℝ γ t)
    (hγ_mem : ∀ t ∈ uIcc a b, γ t ∈ Ω) :
    complexLineIntegral f (φ ∘ γ) a b =
    complexLineIntegral (fun z => f (φ z) * deriv φ z) γ a b := by
  unfold complexLineIntegral
  simp only [Function.comp_def]
  apply integral_congr
  intro t ht
  dsimp only
  have hγt : DifferentiableAt ℝ γ t := hγ_diff t ht
  have hφγt : DifferentiableAt ℂ φ (γ t) :=
    hφ.differentiableAt (hΩ.mem_nhds (hγ_mem t ht))
  have hchain : deriv (fun t => φ (γ t)) t = deriv φ (γ t) * deriv γ t :=
    (hφγt.hasDerivAt.comp t hγt.hasDerivAt).deriv
  rw [hchain]
  ring

open Function Real in
lemma circleMap_zero_add_pi (R θ : ℝ) :
    circleMap 0 R (θ + π) = -circleMap 0 R θ := by
  simp only [circleMap_zero, ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

open Function Real in
theorem circleIntegral_comp_sq_eq_zero (f : ℂ → ℂ) (R : ℝ) :
    (∮ z in C(0, R), f (z ^ 2)) = 0 := by
  simp only [circleIntegral]
  set g : ℝ → ℂ := fun θ => deriv (circleMap 0 R) θ • f ((circleMap 0 R θ) ^ 2)


  have hanti : ∀ θ, g (θ + π) = -g θ := by
    intro θ
    show deriv (circleMap 0 R) (θ + π) • f ((circleMap 0 R (θ + π)) ^ 2) =
      -(deriv (circleMap 0 R) θ • f ((circleMap 0 R θ) ^ 2))
    rw [deriv_circleMap, deriv_circleMap, circleMap_zero_add_pi]
    simp only [smul_eq_mul, neg_pow_two]
    ring

  have h2pi : (2 : ℝ) * π = π + π := by ring
  rw [h2pi]
  by_cases hint : IntervalIntegrable g volume 0 (π + π)
  ·
    have hpi_pos : (0 : ℝ) ≤ π := le_of_lt pi_pos
    have hint1 : IntervalIntegrable g volume 0 π := by
      apply hint.mono_set
      rw [uIcc_of_le hpi_pos, uIcc_of_le (by linarith)]
      exact Icc_subset_Icc_right (by linarith)
    have hint2 : IntervalIntegrable g volume π (π + π) := by
      apply hint.mono_set
      rw [uIcc_of_le (by linarith : π ≤ π + π), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc_left hpi_pos
    rw [← integral_add_adjacent_intervals hint1 hint2]


    have hsub : ∫ x in π..(π + π), g x = ∫ x in (0 : ℝ)..π, g (x + π) := by
      rw [integral_comp_add_right]
      simp only [zero_add]
    rw [hsub]


    have hcongr : (∫ θ in (0 : ℝ)..π, g (θ + π)) = -(∫ θ in (0 : ℝ)..π, g θ) := by
      rw [show (fun θ => g (θ + π)) = fun θ => -g θ from funext (fun θ => hanti θ)]
      exact intervalIntegral.integral_neg
    rw [hcongr]

    simp
  ·
    exact integral_undef hint
