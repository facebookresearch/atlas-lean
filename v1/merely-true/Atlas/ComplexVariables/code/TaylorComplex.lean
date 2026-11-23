/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Complex Topology Filter Finset MeasureTheory

noncomputable def complexTaylorPoly (f : ℂ → ℂ) (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ range n, (iteratedDeriv k f a / (Nat.factorial k : ℂ)) * (z - a) ^ k

theorem dslope_expansion_identity (f : ℂ → ℂ) (a z : ℂ) (n : ℕ) :
    f z = ∑ k ∈ range n, (Function.swap dslope a)^[k] f a * (z - a) ^ k +
      (Function.swap dslope a)^[n] f z * (z - a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Function.iterate_succ', Function.comp_apply]
    set g := (Function.swap dslope a)^[n] f
    have key : (z - a) • dslope g a z = g z - g a := sub_smul_dslope g a z
    simp only [smul_eq_mul] at key
    rw [ih]
    have : dslope g a z * (z - a) ^ (n + 1) = (g z - g a) * (z - a) ^ n := by
      rw [pow_succ]; linear_combination (z - a) ^ n * key
    rw [this]; ring

theorem iterate_dslope_differentiableOn {f : ℂ → ℂ} {Ω : Set ℂ} {a : ℂ}
    (hΩ : IsOpen Ω) (ha : a ∈ Ω) (hf : DifferentiableOn ℂ f Ω) (n : ℕ) :
    DifferentiableOn ℂ ((Function.swap dslope a)^[n] f) Ω := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact (differentiableOn_dslope (hΩ.mem_nhds ha)).mpr ih

theorem iterate_dslope_eq_iteratedDeriv_div_factorial
    {f : ℂ → ℂ} {a : ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hpf : HasFPowerSeriesAt f p a) (k : ℕ) :
    (Function.swap dslope a)^[k] f a = iteratedDeriv k f a / (Nat.factorial k : ℂ) := by

  have h_series := hpf.has_fpower_series_iterate_dslope_fslope k

  have h_val : (Function.swap dslope a)^[k] f a =
      (FormalMultilinearSeries.fslope^[k] p).coeff 0 := by
    have h0 := h_series.coeff_zero (fun _ => (1 : ℂ))
    simp only [FormalMultilinearSeries.coeff] at h0 ⊢
    exact h0.symm

  rw [h_val, FormalMultilinearSeries.coeff_iterate_fslope, zero_add]


  obtain ⟨r, hpfball⟩ := hpf
  have h_ifd := hpfball.iteratedFDeriv_eq_sum_of_completeSpace (fun (_ : Fin k) => (1 : ℂ))
  simp only [FormalMultilinearSeries.coeff]
  rw [iteratedDeriv_eq_iteratedFDeriv, h_ifd]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have : (1 : Fin k → ℂ) = (fun _ => (1 : ℂ)) := by ext; simp
  rw [this, mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)

theorem taylor_complex {f : ℂ → ℂ} {Ω : Set ℂ} {a : ℂ} (n : ℕ)
    (hΩ : IsOpen Ω) (ha : a ∈ Ω) (hf : DifferentiableOn ℂ f Ω) :
    ∃ fₙ : ℂ → ℂ, DifferentiableOn ℂ fₙ Ω ∧
      ∀ z ∈ Ω, f z = complexTaylorPoly f a n z + fₙ z * (z - a) ^ n := by
  refine ⟨(Function.swap dslope a)^[n] f,
    iterate_dslope_differentiableOn hΩ ha hf n, fun z _ => ?_⟩

  rw [dslope_expansion_identity f a z n]
  congr 1

  simp only [complexTaylorPoly]
  congr 1; ext k; congr 1
  have hfa : AnalyticAt ℂ f a := hf.analyticAt (hΩ.mem_nhds ha)
  obtain ⟨p, hp⟩ := hfa
  exact iterate_dslope_eq_iteratedDeriv_div_factorial hp k
