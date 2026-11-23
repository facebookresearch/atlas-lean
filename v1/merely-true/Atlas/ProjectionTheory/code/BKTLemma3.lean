/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace BKTProof

open Finset Complex

/-- The squared $L^2$-norm of the high-frequency part of `f` on a finite set `S`,
i.e. `∑_{x ∈ S} |f(x) − μ_S(f)|²`, where `μ_S(f) = (1/|S|) ∑_{y ∈ S} f(y)` is the average
of `f` over `S`. This is `‖f_h‖_{L^2(S)}²` in the notation of BKT. -/
noncomputable def l2NormSqHighFreq {α : Type*} (S : Finset α) (f : α → ℂ) : ℝ :=
  ∑ x ∈ S, ‖f x - ((S.card : ℂ)⁻¹ * ∑ y ∈ S, f y)‖ ^ 2

/-- Monotonicity of the high-frequency squared norm under enlarging the domain:
if `S ⊆ T` and `S` is nonempty, then `‖f_h‖²_{L^2(S)} ≤ ‖f_h‖²_{L^2(T)}`. The proof
expands the mean of `f` on `T` versus the mean on `S` and uses that the cross-term
vanishes because `∑_{x ∈ S} (f(x) − μ_S) = 0`. -/
theorem l2NormSqHighFreq_mono_of_subset {α : Type*} [DecidableEq α]
    {S T : Finset α} (hST : S ⊆ T) (hS : S.Nonempty)
    (f : α → ℂ) :
    l2NormSqHighFreq S f ≤ l2NormSqHighFreq T f := by
  unfold l2NormSqHighFreq
  set μS := (S.card : ℂ)⁻¹ * ∑ y ∈ S, f y
  set μT := (T.card : ℂ)⁻¹ * ∑ y ∈ T, f y

  have step1 : ∑ x ∈ S, ‖f x - μS‖ ^ 2 ≤ ∑ x ∈ S, ‖f x - μT‖ ^ 2 := by
    have decomp : ∀ x ∈ S, ‖f x - μT‖ ^ 2 = ‖f x - μS‖ ^ 2 + ‖μS - μT‖ ^ 2 +
        2 * @inner ℝ ℂ _ (f x - μS) (μS - μT) := by
      intro x _
      have eq : f x - μT = (f x - μS) + (μS - μT) := by ring
      rw [eq, norm_add_sq_real]; ring
    have cross_zero : ∑ x ∈ S, @inner ℝ ℂ _ (f x - μS) (μS - μT) = 0 := by
      rw [← sum_inner (𝕜 := ℝ)]
      have sum_zero : ∑ x ∈ S, (f x - μS) = 0 := by
        simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, μS]
        have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
        field_simp; ring
      rw [sum_zero, inner_zero_left]
    calc ∑ x ∈ S, ‖f x - μS‖ ^ 2
        ≤ ∑ x ∈ S, ‖f x - μS‖ ^ 2 + (↑S.card * ‖μS - μT‖ ^ 2 +
          2 * ∑ x ∈ S, @inner ℝ ℂ _ (f x - μS) (μS - μT)) := by
          rw [cross_zero, mul_zero, add_zero]
          linarith [mul_nonneg (Nat.cast_nonneg' S.card) (sq_nonneg ‖μS - μT‖)]
      _ = ∑ x ∈ S, ‖f x - μT‖ ^ 2 := by
          rw [show ∑ x ∈ S, ‖f x - μT‖ ^ 2 = ∑ x ∈ S, (‖f x - μS‖ ^ 2 + ‖μS - μT‖ ^ 2 +
              2 * @inner ℝ ℂ _ (f x - μS) (μS - μT)) from sum_congr rfl decomp]
          simp only [sum_add_distrib, sum_const, nsmul_eq_mul, ← Finset.mul_sum]
          ring

  have step2 : ∑ x ∈ S, ‖f x - μT‖ ^ 2 ≤ ∑ x ∈ T, ‖f x - μT‖ ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => by positivity)
  linarith

/-- The high-frequency $L^2$-norm of `f` on a finite set `S`, namely
`‖f_h‖_{L^2(S)} = √(∑_{x ∈ S} |f(x) − μ_S(f)|²)`. -/
noncomputable def l2NormHighFreq {α : Type*} (S : Finset α) (f : α → ℂ) : ℝ :=
  Real.sqrt (l2NormSqHighFreq S f)

/-- Square-root version of monotonicity: `‖f_h‖_{L^2(S)} ≤ ‖f_h‖_{L^2(T)}` whenever
`S ⊆ T` and `S` is nonempty. -/
theorem l2NormHighFreq_mono_of_subset {α : Type*} [DecidableEq α]
    {S T : Finset α} (hST : S ⊆ T) (hS : S.Nonempty)
    (f : α → ℂ) :
    l2NormHighFreq S f ≤ l2NormHighFreq T f := by
  unfold l2NormHighFreq
  exact Real.sqrt_le_sqrt (l2NormSqHighFreq_mono_of_subset hST hS f)

/-- BKT Lemma 3 (Subsection 7.3 of BKT): the high-frequency $L^2$-norm of `f` restricted to
the units `ℤ_q^*` is at most its high-frequency $L^2$-norm on all of `ℤ_q`, i.e.
`‖f_h^*‖_{L^2(ℤ_q^*)} ≤ ‖f_h‖_{L^2(ℤ_q)}`. -/
theorem bkt_lemma3 (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    l2NormHighFreq (univ.filter (fun x : ZMod q => IsUnit x)) f ≤
    l2NormHighFreq (univ : Finset (ZMod q)) f :=
  l2NormHighFreq_mono_of_subset (filter_subset _ _)
    ⟨1, mem_filter.mpr ⟨mem_univ _, isUnit_one⟩⟩ f

end BKTProof
