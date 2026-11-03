/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Atlas.NumberTheoryI.code.RiemannZeta
import Atlas.NumberTheoryI.code.Lem168
open Chebyshev Asymptotics Filter Topology MeasureTheory Finset
open Nat (primeCounting)
open Real (log exp)

namespace Chapter16

theorem lem_16_7_chebyshev_bound {x : ℝ} (hx : 0 ≤ x) : θ x ≤ log 4 * x :=
  Chebyshev.theta_le_log4_mul_x hx

theorem lem_16_7_chebyshev_bound_book {x : ℝ} (hx : 0 ≤ x) : θ x ≤ 4 * log 2 * x := by
  calc θ x ≤ log 4 * x := theta_le_log4_mul_x hx
    _ = 2 * log 2 * x := by
        rw [show (4:ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; ring
    _ ≤ 4 * log 2 * x := by
        have hlog2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
        nlinarith

lemma div_log_sq_isLittleO_div_log :
    (fun x : ℝ => x / log x ^ 2) =o[atTop] (fun x => x / log x) := by
  rw [isLittleO_iff_tendsto']
  · refine Tendsto.congr' ?_ (Real.tendsto_log_atTop.inv_tendsto_atTop)
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    show (log x)⁻¹ = x / log x ^ 2 / (x / log x)
    rw [div_div, sq]; field_simp
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx h
    linarith [div_pos (lt_trans one_pos hx) (Real.log_pos hx)]

lemma primeCounting_sub_theta_div_log_isLittleO :
    (fun x : ℝ => (↑(⌊x⌋₊.primeCounting) : ℝ) - θ x / log x) =o[atTop]
    (fun x => x / log x) :=
  Chebyshev.primeCounting_sub_theta_div_log_isBigO.trans_isLittleO div_log_sq_isLittleO_div_log

theorem thm_16_6_forward
    (htheta : (fun x : ℝ => θ x) ~[atTop] (fun x => x)) :
    (fun x : ℝ => (↑(⌊x⌋₊.primeCounting) : ℝ)) ~[atTop] (fun x => x / log x) := by
  rw [Asymptotics.IsEquivalent] at htheta ⊢
  have h1 : (fun x : ℝ => (↑(⌊x⌋₊.primeCounting) : ℝ) - θ x / log x) =o[atTop]
      (fun x => x / log x) := primeCounting_sub_theta_div_log_isLittleO
  have h2 : (fun x : ℝ => (θ x - x) / log x) =o[atTop] (fun x => x / log x) := by
    show (fun x => (θ x - x) * (log x)⁻¹) =o[atTop] (fun x => x * (log x)⁻¹)
    have h_sub : (fun x : ℝ => θ x - x) =o[atTop] (fun x => x) :=
      htheta.congr (fun x => by simp [Pi.sub_apply]) (fun x => rfl)
    exact h_sub.mul_isBigO (isBigO_refl _ _)
  exact (h1.add h2).congr (fun x => by simp [Pi.sub_apply]; ring) (fun x => rfl)

theorem thm_16_6_backward
    (hpi : (fun x : ℝ => (↑(⌊x⌋₊.primeCounting) : ℝ)) ~[atTop] (fun x => x / log x)) :
    (fun x : ℝ => θ x) ~[atTop] (fun x => x) := by
  rw [Asymptotics.IsEquivalent] at hpi ⊢
  have hpi' : (fun x : ℝ => (↑(⌊x⌋₊.primeCounting) : ℝ) - x / log x) =o[atTop]
      (fun x => x / log x) :=
    hpi.congr (fun x => by simp [Pi.sub_apply]) (fun x => rfl)

  have step1 : (fun x : ℝ => ((↑(⌊x⌋₊.primeCounting) : ℝ) - x / log x) * log x) =o[atTop]
      (fun x => x) := by
    have h := hpi'.mul_isBigO (isBigO_refl (fun x : ℝ => log x) atTop)
    exact h.congr' EventuallyEq.rfl (by
      filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      have hlog : log x ≠ 0 := ne_of_gt (Real.log_pos hx)
      field_simp)

  have step2 : (fun x : ℝ => -((↑(⌊x⌋₊.primeCounting) : ℝ) - θ x / log x) * log x) =o[atTop]
      (fun x => x) := by
    have h := primeCounting_sub_theta_div_log_isLittleO.neg_left.mul_isBigO
      (isBigO_refl (fun x : ℝ => log x) atTop)
    exact h.congr' EventuallyEq.rfl (by
      filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      have hlog : log x ≠ 0 := ne_of_gt (Real.log_pos hx)
      field_simp)

  exact (step2.add step1).congr' (by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    simp only [Pi.sub_apply]
    have hlog : log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    field_simp; ring) EventuallyEq.rfl

theorem thm_16_6_chebyshev_equiv :
    ((fun x : ℝ => (↑(⌊x⌋₊.primeCounting) : ℝ)) ~[atTop] (fun x => x / log x)) ↔
    ((fun x : ℝ => θ x) ~[atTop] (fun x => x)) :=
  ⟨thm_16_6_backward, thm_16_6_forward⟩

theorem lem_16_8_integral_criterion
    (f : ℝ → ℝ) (hf_mono : Monotone f)
    (hf_conv : ∃ L : ℝ, Tendsto (fun x => ∫ t in Set.Ioc 1 x,
      (f t - t) / t ^ 2) atTop (𝓝 L)) :
    (fun x : ℝ => f x) ~[atTop] (fun x => x) :=
  Lem168.lem_16_8_integral_criterion f hf_mono hf_conv

noncomputable def laplace_transform (h : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), (Complex.exp (-s * ↑t) : ℂ) * ↑(h t)

noncomputable def Phi (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (Real.log ↑(↑p : ℕ) : ℂ) * (↑(↑p : ℕ) : ℂ) ^ (-s)

lemma theta_exp_eq_tsum (t : ℝ) :
    θ (exp t) = ∑' p : Nat.Primes, if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ) else 0 := by
  set S := Finset.subtype Nat.Prime (Ioc 0 ⌊exp t⌋₊)

  have h1 : θ (exp t) = ∑ p ∈ S, Real.log ↑(↑p : ℕ) := by
    rw [Chebyshev.theta, ← sum_subtype_eq_sum_filter]

  have h2 : (∑' p : Nat.Primes, if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ) else 0) =
      ∑ p ∈ S, if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ) else 0 := by
    apply tsum_eq_sum
    intro p hp
    have hmem : ¬((↑p : ℕ) ∈ Ioc 0 ⌊exp t⌋₊) := by rwa [← Finset.mem_subtype]
    rw [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hmem
    simp only [ite_eq_right_iff]
    intro hlog
    exfalso
    have hp_pos : (0 : ℕ) < ↑p := p.2.pos
    rcases hmem with h | h
    · omega
    · have hle : (↑↑p : ℝ) ≤ exp t := by
        rw [← Real.log_le_iff_le_exp (by exact_mod_cast hp_pos : (0 : ℝ) < ↑↑p)]
        exact hlog
      exact absurd (Nat.le_floor hle) (not_le.mpr h)

  rw [h1, h2]
  apply Finset.sum_congr rfl
  intro p hp
  have hmem : (↑p : ℕ) ∈ Ioc 0 ⌊exp t⌋₊ := Finset.mem_subtype.mp hp
  rw [Finset.mem_Ioc] at hmem
  have hp_pos : (0 : ℝ) < (↑↑p : ℝ) := by exact_mod_cast hmem.1
  have hlog : Real.log ↑(↑p : ℕ) ≤ t := by
    rw [Real.log_le_iff_le_exp hp_pos]
    exact le_trans (by exact_mod_cast hmem.2) (Nat.floor_le (le_of_lt (Real.exp_pos t)))
  rw [if_pos hlog]

lemma exp_neg_mul_log_eq_cpow (p : ℕ) (hp : 0 < p) (s : ℂ) :
    Complex.exp (-s * ↑(Real.log (↑p : ℝ))) = (↑p : ℂ) ^ (-s) := by
  have hp_ne : (↑p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Complex.cpow_def_of_ne_zero hp_ne]
  congr 1
  rw [← Complex.natCast_log (n := p)]
  ring

theorem integral_indicator_prime (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (hs : 0 < s.re) :
    ∫ t in Set.Ioi (Real.log (↑p : ℝ)), Complex.exp (-s * ↑t) =
    (↑p : ℂ) ^ (-s) / s := by
  have hs_ne : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hns_re : (-s).re < 0 := by simp; linarith
  rw [integral_exp_mul_complex_Ioi hns_re (Real.log (↑p : ℝ))]
  rw [exp_neg_mul_log_eq_cpow p (Nat.Prime.pos hp) s]
  field_simp

lemma prime_log_pos (p : Nat.Primes) : 0 < Real.log ↑(↑p : ℕ) := by
  rw [Real.log_pos_iff (by exact_mod_cast p.2.pos.le : (0 : ℝ) ≤ ↑(↑p : ℕ))]
  exact_mod_cast p.2.one_lt

lemma abel_norm_summand_eq (c : ℝ) (hc : 0 ≤ c) (s : ℂ) (t : ℝ) :
    ‖Complex.exp (-s * ↑t) * ↑(if c ≤ t then c else 0 : ℝ)‖ =
    if c ≤ t then c * Real.exp (-(s.re) * t) else 0 := by
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.norm_real]
  split_ifs with h
  · simp [Real.norm_of_nonneg hc, mul_comm]
  · simp

lemma abel_indicator_integral_real (c : ℝ) (hc : 0 < c) (σ : ℝ) (hσ : 0 < σ) :
    ∫ t in Set.Ioi (0 : ℝ), (if c ≤ t then c * Real.exp (-σ * t) else 0) =
    c * Real.exp (-σ * c) / σ := by
  have h_eq : ∀ t : ℝ, (if c ≤ t then c * Real.exp (-σ * t) else 0) =
      (Set.Ici c).indicator (fun t => c * Real.exp (-σ * t)) t := by
    intro t; simp [Set.indicator, Set.mem_Ici]
  simp_rw [h_eq]
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hIci : Set.Ici c ∩ Set.Ioi (0 : ℝ) = Set.Ici c := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
    exact ⟨And.left, fun hx => ⟨hx, lt_of_lt_of_le hc hx⟩⟩
  rw [hIci, integral_Ici_eq_integral_Ioi, integral_const_mul]
  rw [integral_exp_mul_Ioi (by linarith : -σ < 0) c]; field_simp

lemma abel_indicator_integral_complex (c : ℝ) (hc : 0 < c) (s : ℂ) :
    ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-s * ↑t) *
      ↑(if c ≤ t then c else 0 : ℝ) =
    (↑c : ℂ) * ∫ t in Set.Ioi c, Complex.exp (-s * ↑t) := by
  have h_eq : ∀ t : ℝ, Complex.exp (-s * ↑t) * ↑(if c ≤ t then c else 0 : ℝ) =
      (Set.Ici c).indicator (fun t : ℝ => (↑c : ℂ) * Complex.exp (-s * ↑t)) t := by
    intro t; simp only [Set.indicator, Set.mem_Ici]; split_ifs with h <;> simp [mul_comm]
  simp_rw [h_eq]
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hIci : Set.Ici c ∩ Set.Ioi (0 : ℝ) = Set.Ici c := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
    exact ⟨And.left, fun hx => ⟨hx, lt_of_lt_of_le hc hx⟩⟩
  rw [hIci, ← integral_Ici_eq_integral_Ioi]
  exact integral_const_mul _ _

lemma abel_summable_primes_log_rpow (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => Real.log ↑(↑p : ℕ) * (↑(↑p : ℕ) : ℝ) ^ (-σ)) := by
  have hε : (0 : ℝ) < (σ - 1) / 2 := by linarith
  have hexp : (σ - 1) / 2 - σ < -1 := by linarith
  apply Summable.of_nonneg_of_le
  · intro p; positivity
  · intro p
    have hp_pos : (0 : ℝ) < ↑(↑p : ℕ) := by exact_mod_cast p.2.pos
    calc Real.log ↑(↑p : ℕ) * (↑(↑p : ℕ) : ℝ) ^ (-σ)
        ≤ ((↑(↑p : ℕ) : ℝ) ^ ((σ - 1) / 2) / ((σ - 1) / 2)) * (↑(↑p : ℕ) : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hp_pos.le hε) (by positivity)
      _ = (1 / ((σ - 1) / 2)) * (↑(↑p : ℕ) : ℝ) ^ ((σ - 1) / 2 - σ) := by
          rw [div_mul_eq_mul_div, ← Real.rpow_add hp_pos]; ring_nf
  · exact (Nat.Primes.summable_rpow.mpr hexp).const_smul (1 / ((σ - 1) / 2))

lemma abel_integrableOn_prime_summand (p : Nat.Primes) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * ↑t) *
      ↑(if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ) else 0 : ℝ))
      (Set.Ioi 0) := by
  have hlog_pos := prime_log_pos p
  have h_eq : (fun t : ℝ => Complex.exp (-s * ↑t) * ↑(if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ) else 0 : ℝ)) =
      (Set.Ici (Real.log ↑(↑p : ℕ))).indicator (fun t : ℝ => (↑(Real.log ↑(↑p : ℕ)) : ℂ) * Complex.exp (-s * ↑t)) := by
    ext t; simp only [Set.indicator, Set.mem_Ici]; split_ifs with h <;> simp [mul_comm]
  rw [h_eq, integrableOn_indicator_iff measurableSet_Ici]
  have hIci : Set.Ici (Real.log ↑(↑p : ℕ)) ∩ Set.Ioi (0 : ℝ) = Set.Ici (Real.log ↑(↑p : ℕ)) := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
    exact ⟨And.left, fun hx => ⟨hx, lt_of_lt_of_le hlog_pos hx⟩⟩
  rw [hIci]
  have h_base : IntegrableOn (fun t : ℝ => Complex.exp ((-s) * ↑t)) (Set.Ici (Real.log ↑(↑p : ℕ))) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_complex_Ioi (by simp; linarith) _
  exact h_base.const_mul (↑(Real.log ↑(↑p : ℕ)) : ℂ)

theorem abel_summation_laplace_theta (s : ℂ) (hs : 1 < s.re) :
    laplace_transform (fun t => θ (exp t)) s =
    ∑' p : Nat.Primes, ((Real.log ↑(↑p : ℕ) : ℂ) * (↑(↑p : ℕ) : ℂ) ^ (-s)) / s := by
  have hs0 : 0 < s.re := by linarith
  unfold laplace_transform

  simp_rw [theta_exp_eq_tsum]

  conv_lhs =>
    arg 2; ext t
    rw [show Complex.exp (-s * ↑t) *
        ↑(∑' p : Nat.Primes,
          if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ) else 0 : ℝ) =
      ∑' p : Nat.Primes, Complex.exp (-s * ↑t) *
        ↑(if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ) else 0 : ℝ) from by
      push_cast; rw [tsum_mul_left]]

  have h_int : ∀ p : Nat.Primes, Integrable (fun t : ℝ => Complex.exp (-s * ↑t) *
      ↑(if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ) else 0 : ℝ))
      (volume.restrict (Set.Ioi 0)) :=
    fun p => abel_integrableOn_prime_summand p s hs0
  have h_norm_eq : ∀ p : Nat.Primes, ∫ t in Set.Ioi (0 : ℝ),
      ‖Complex.exp (-s * ↑t) * ↑(if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ) else 0 : ℝ)‖ =
      Real.log ↑(↑p : ℕ) * (↑(↑p : ℕ) : ℝ) ^ (-s.re) / s.re := by
    intro p
    simp_rw [abel_norm_summand_eq _ (prime_log_pos p).le s]
    rw [abel_indicator_integral_real _ (prime_log_pos p) _ hs0]
    congr 1; congr 1
    rw [Real.rpow_def_of_pos (by exact_mod_cast p.2.pos : (0 : ℝ) < ↑(↑p : ℕ))]; ring_nf
  have h_summ : Summable (fun p : Nat.Primes => ∫ t in Set.Ioi (0 : ℝ),
      ‖Complex.exp (-s * ↑t) * ↑(if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ) else 0 : ℝ)‖) := by
    simp_rw [h_norm_eq]
    exact (abel_summable_primes_log_rpow s.re hs).div_const s.re
  rw [(integral_tsum_of_summable_integral_norm h_int h_summ).symm]

  congr 1; ext p
  rw [abel_indicator_integral_complex _ (prime_log_pos p) s]
  rw [integral_indicator_prime _ p.2 s hs0]
  ring

theorem lem_16_10_laplace_theta (s : ℂ) (hs : 1 < s.re) :
    laplace_transform (fun t => θ (exp t)) s = Phi s / s := by
  rw [abel_summation_laplace_theta s hs, Phi, tsum_div_const]

lemma integrableOn_mul_exp_neg_Ioi' {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-r * t)) (Set.Ioi (0 : ℝ)) := by
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  apply integrable_of_isBigO_exp_neg hr2
  · exact (continuous_id.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id'))).continuousOn
  · rw [Asymptotics.isBigO_iff]; use 2 / r
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht (Real.exp_nonneg _))]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hle : t ≤ (2 / r) * Real.exp (r / 2 * t) :=
      calc t = (2 / r) * (r / 2 * t) := by field_simp
        _ ≤ (2 / r) * Real.exp (r / 2 * t) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [Real.add_one_le_exp (r / 2 * t)]
    calc t * Real.exp (-r * t)
        = t * (Real.exp (-(r/2) * t) * Real.exp (-(r/2) * t)) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ (2 / r) * Real.exp (r / 2 * t) *
            (Real.exp (-(r / 2) * t) * Real.exp (-(r/2) * t)) := by
          apply mul_le_mul_of_nonneg_right hle
            (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ = (2 / r) * (Real.exp (r / 2 * t) * Real.exp (-(r / 2) * t)) *
            Real.exp (-(r / 2) * t) := by ring
      _ = 2 / r * Real.exp (-(r / 2) * t) := by
          rw [← Real.exp_add]; simp only [neg_mul, add_neg_cancel, Real.exp_zero]; ring

set_option maxHeartbeats 400000 in
theorem laplace_holomorphic_of_exp_bound
    (h : ℝ → ℝ) (a C : ℝ) (hC : 0 < C)
    (hbound : ∀ t : ℝ, 0 ≤ t → |h t| ≤ C * exp (a * t)) :
    DifferentiableOn ℂ (fun s => laplace_transform h s) {s | a < s.re} := by
  by_cases hm : AEStronglyMeasurable (fun t : ℝ => (h t : ℂ))
      (volume.restrict (Set.Ioi (0 : ℝ)))
  ·
    intro s₀ hs₀
    simp only [Set.mem_setOf_eq] at hs₀
    apply DifferentiableAt.differentiableWithinAt
    set μ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ_def
    set δ := (s₀.re - a) / 2 with hδ_def
    set b := (s₀.re + a) / 2 with hb_def
    have hδ : 0 < δ := by simp only [δ]; linarith
    have hba : 0 < b - a := by simp only [b]; linarith
    have hball_re : ∀ z ∈ Metric.ball s₀ δ, b ≤ z.re := by
      intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have habs_re : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have : |z.re - s₀.re| < δ := lt_of_le_of_lt habs_re hz
      have := abs_lt.mp this
      simp only [b, δ] at *; linarith

    have hmeas_F : ∀ z : ℂ, AEStronglyMeasurable
        (fun t : ℝ => Complex.exp (-z * ↑t) * ↑(h t)) μ := by
      intro z
      apply AEStronglyMeasurable.mul _ hm
      exact (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable

    have hF_int : Integrable (fun t : ℝ => Complex.exp (-s₀ * ↑t) * ↑(h t)) μ := by
      have hpos : 0 < s₀.re - a := by linarith
      have hbound_int : IntegrableOn (fun t : ℝ => C * exp (-(s₀.re - a) * t))
          (Set.Ioi (0 : ℝ)) := (exp_neg_integrableOn_Ioi 0 hpos).const_mul C
      apply Integrable.mono hbound_int (hmeas_F s₀)
      rw [ae_restrict_iff' measurableSet_Ioi]
      apply ae_of_all; intro t ht
      simp only [Set.mem_Ioi] at ht
      rw [norm_mul, Complex.norm_exp]
      have hre : (-s₀ * ↑t).re = -s₀.re * t := by
        simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [hre, Complex.norm_real]
      calc exp (-s₀.re * t) * |h t|
          ≤ exp (-s₀.re * t) * (C * exp (a * t)) :=
            mul_le_mul_of_nonneg_left (hbound t (le_of_lt ht)) (Real.exp_nonneg _)
        _ = C * exp (-(s₀.re - a) * t) := by
            rw [show -(s₀.re - a) * t = -s₀.re * t + a * t from by ring]
            rw [Real.exp_add]; ring
        _ ≤ ‖C * exp (-(s₀.re - a) * t)‖ := by
            rw [Real.norm_of_nonneg (mul_nonneg (le_of_lt hC) (Real.exp_nonneg _))]

    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ)
      (F := fun (s : ℂ) (t : ℝ) => Complex.exp (-s * ↑t) * ↑(h t))
      (F' := fun (s : ℂ) (t : ℝ) => -↑t * Complex.exp (-s * ↑t) * ↑(h t))
      (bound := fun t => C * |t| * exp (-(b - a) * t))
      (s := Metric.ball s₀ δ)
      (x₀ := s₀)
      (Metric.ball_mem_nhds s₀ hδ)
      (Filter.Eventually.of_forall (fun z => hmeas_F z))
      hF_int
      (by
        have hcont : Continuous (fun t : ℝ => -↑t * Complex.exp (-s₀ * ↑t) : ℝ → ℂ) :=
          Complex.continuous_ofReal.neg.mul
            (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
        exact hcont.aestronglyMeasurable.mul hm)
      ?_ ?_ ?_
    · exact key.2.differentiableAt
    ·
      rw [ae_restrict_iff' measurableSet_Ioi]
      apply ae_of_all; intro t ht z hz
      simp only [Set.mem_Ioi] at ht
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_exp]
      have hre : (-z * ↑t).re = -z.re * t := by
        simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [hre, Complex.norm_real]
      have hht : |h t| ≤ C * exp (a * t) := hbound t (le_of_lt ht)
      have hb : b ≤ z.re := hball_re z hz
      calc |t| * exp (-z.re * t) * |h t|
          ≤ |t| * exp (-b * t) * |h t| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_right (neg_le_neg hb) (le_of_lt ht)))
              (abs_nonneg _)
        _ ≤ |t| * exp (-b * t) * (C * exp (a * t)) := by
            apply mul_le_mul_of_nonneg_left hht
              (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
        _ = C * |t| * exp (-(b - a) * t) := by
            rw [show -(b - a) * t = -b * t + a * t from by ring]
            rw [Real.exp_add]; ring
    ·
      show IntegrableOn (fun t => C * |t| * exp (-(b - a) * t)) (Set.Ioi (0 : ℝ))
      have h1 : IntegrableOn (fun t => C * (t * exp (-(b - a) * t)))
          (Set.Ioi (0 : ℝ)) := (integrableOn_mul_exp_neg_Ioi' hba).const_mul C
      apply h1.congr_fun _ measurableSet_Ioi
      intro t ht
      simp only [Set.mem_Ioi] at ht
      show C * (t * exp (-(b - a) * t)) = C * |t| * exp (-(b - a) * t)
      rw [abs_of_pos ht]; ring
    ·
      apply ae_of_all; intro t z _
      have h1 : HasDerivAt (fun s => -s * (↑t : ℂ)) (-(↑t : ℂ)) z := by
        have := (hasDerivAt_neg (𝕜 := ℂ) z).mul_const (↑t : ℂ)
        simp only [neg_one_mul] at this; exact this
      have h2 := h1.cexp.mul_const (↑(h t) : ℂ)
      convert h2 using 1; ring
  ·
    have heq : (fun s : ℂ => ∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (-s * ↑t) * ↑(h t)) = fun _ => 0 := by
      ext s
      apply integral_undef
      intro ⟨hasm, _⟩
      apply hm
      have h1 : AEStronglyMeasurable (fun t : ℝ => Complex.exp (s * ↑t))
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
        apply Continuous.aestronglyMeasurable
        exact (continuous_const.mul Complex.continuous_ofReal).cexp
      have h2 : AEStronglyMeasurable
          (fun t : ℝ => Complex.exp (s * ↑t) * (Complex.exp (-s * ↑t) * ↑(h t)))
          (volume.restrict (Set.Ioi (0 : ℝ))) := h1.mul hasm
      convert h2 using 1
      ext t
      simp only [← mul_assoc]
      rw [show Complex.exp (s * ↑t) * Complex.exp (-s * ↑t) = 1 from by
        rw [← Complex.exp_add]; simp]
      simp
    simp only [laplace_transform]
    rw [show (fun s => ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-s * ↑t) * ↑(h t)) =
      fun _ => (0 : ℂ) from heq]
    exact differentiableOn_const 0

theorem lem_16_10_holomorphic :
    DifferentiableOn ℂ (fun s => laplace_transform (fun t => θ (exp t)) s)
      {s | 1 < s.re} := by
  refine laplace_holomorphic_of_exp_bound (fun t => θ (exp t)) 1 (Real.log 4) ?_ ?_
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 4)
  · intro t ht
    have hexp_pos : 0 < exp t := Real.exp_pos t
    have htheta_bound := theta_le_log4_mul_x (le_of_lt hexp_pos)
    have htheta_nonneg := theta_nonneg (exp t)
    rw [abs_of_nonneg htheta_nonneg, one_mul]
    exact htheta_bound

noncomputable def PhiCorrection (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (Real.log ↑(↑p : ℕ) : ℂ) /
    ((↑(↑p : ℕ) : ℂ) ^ s * ((↑(↑p : ℕ) : ℂ) ^ s - 1))

noncomputable def G₀ : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * riemannZeta s) 1 1

lemma G₀_eq_of_ne {s : ℂ} (hs : s ≠ 1) : G₀ s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs ..

lemma G₀_one : G₀ 1 = 1 := Function.update_self 1 1 _

lemma G₀_differentiableAt_of_ne {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ G₀ s :=
  ((differentiableAt_id.sub (differentiableAt_const 1)).mul
    (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq
    (by filter_upwards [eventually_ne_nhds hs] with t ht; exact G₀_eq_of_ne ht)

lemma G₀_analyticAt_one : AnalyticAt ℂ G₀ 1 :=
  Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    (by filter_upwards [self_mem_nhdsWithin] with z hz; exact G₀_differentiableAt_of_ne hz)
    (by simp only [G₀, continuousAt_update_same]; exact riemannZeta_residue_one)

lemma G₀_differentiable : Differentiable ℂ G₀ := by
  intro s; rcases ne_or_eq s 1 with hs | rfl
  · exact G₀_differentiableAt_of_ne hs
  · exact G₀_analyticAt_one.differentiableAt

lemma G₀_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : G₀ s ≠ 0 := by
  rcases ne_or_eq s 1 with hsne | rfl
  · rw [G₀_eq_of_ne hsne]
    exact mul_ne_zero (sub_ne_zero.mpr hsne) (riemannZeta_ne_zero_of_one_le_re hs)
  · rw [G₀_one]; exact one_ne_zero

noncomputable def F₀ : ℂ → ℂ := fun z => (z - 1) * G₀ z

lemma F₀_eq : F₀ = fun z => (z - 1) ^ (2 : ℤ) • riemannZeta z := by
  ext z; simp only [F₀]
  by_cases hz : z = 1
  · subst hz; simp [G₀, Function.update_self]; norm_num [zpow_natCast, smul_eq_mul]
  · rw [G₀_eq_of_ne hz, show (2 : ℤ) = (2 : ℕ) from rfl, zpow_natCast, smul_eq_mul, sq]; ring

lemma meromorphicAt_riemannZeta_one : MeromorphicAt riemannZeta 1 :=
  ⟨2, F₀_eq ▸ (analyticAt_id.sub analyticAt_const).mul G₀_analyticAt_one⟩

lemma meromorphicAt_riemannZeta (s : ℂ) : MeromorphicAt riemannZeta s := by
  rcases ne_or_eq s 1 with hs | rfl
  · exact (Complex.analyticAt_iff_eventually_differentiableAt.mpr
      (by filter_upwards [eventually_ne_nhds hs] with z hz
          exact differentiableAt_riemannZeta hz)).meromorphicAt
  · exact meromorphicAt_riemannZeta_one

lemma rpow_sub_one_bound {p σ : ℝ} (hp : 2 ≤ p) (hσ : 0 < σ) :
    (1 - (2 : ℝ) ^ (-σ)) * p ^ (2 * σ) ≤ p ^ σ * (p ^ σ - 1) := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have h2σ : p ^ (2 * σ) = p ^ σ * p ^ σ := by
    rw [← Real.rpow_add hp_pos]; ring_nf
  rw [h2σ, mul_comm (1 - _), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_of_lt hp_pos) _)
  suffices h : 1 ≤ p ^ σ * (2 : ℝ) ^ (-σ) by linarith
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)]
  simp only [one_mul]
  exact Real.rpow_le_rpow (by norm_num) hp (le_of_lt hσ)

lemma summable_primes_rpow_neg {α : ℝ} (hα : 1 < α) :
    Summable (fun p : Nat.Primes => ((↑↑p : ℝ) ^ (-α))) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ (-α))) :=
    Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)])
      (Real.summable_nat_rpow_inv.mpr hα)
  exact h.comp_injective Subtype.val_injective

lemma prime_rpow_sub_one_pos (p : Nat.Primes) (σ : ℝ) (hσ : 1 / 2 < σ) :
    0 < (↑↑p : ℝ) ^ σ - 1 := by
  have hp : (1 : ℝ) < (↑↑p : ℝ) := Nat.one_lt_cast.mpr (Nat.Prime.one_lt p.2)
  have : (1 : ℝ) < (↑↑p : ℝ) ^ σ := by
    have h0 : (1 : ℝ) = (↑↑p : ℝ) ^ (0 : ℝ) := by simp
    rw [h0]; exact Real.rpow_lt_rpow_of_exponent_lt hp (by linarith)
  linarith

set_option maxHeartbeats 400000 in
lemma phiCorrection_term_differentiableOn (p : Nat.Primes) (σ : ℝ) (hσ : 1 / 2 < σ) :
    DifferentiableOn ℂ (fun w => (Real.log (↑↑p : ℝ) : ℂ) /
      ((↑↑p : ℂ) ^ w * ((↑↑p : ℂ) ^ w - 1))) {s : ℂ | σ < s.re} := by
  have hp_pos : (0 : ℕ) < ↑p := Nat.Prime.pos p.2
  have hp1 : (1 : ℝ) < (↑↑p : ℝ) := Nat.one_lt_cast.mpr (Nat.Prime.one_lt p.2)
  have hcpow_diff : Differentiable ℂ (fun w : ℂ => (↑↑p : ℂ) ^ w) := by
    intro w
    apply DifferentiableAt.cpow (differentiableAt_const _) differentiableAt_id (Or.inl ?_)
    simp; exact_mod_cast hp_pos
  apply DifferentiableOn.div (differentiableOn_const _)
  · exact (hcpow_diff.differentiableOn.mul
      (hcpow_diff.differentiableOn.sub (differentiableOn_const _)))
  · intro w hw
    simp only [Set.mem_setOf_eq] at hw
    have hpσ : (1 : ℝ) < (↑↑p : ℝ) ^ σ := by
      have h0 : (1 : ℝ) = (↑↑p : ℝ) ^ (0 : ℝ) := by simp
      rw [h0]; exact Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
    have hpw : (1 : ℝ) < (↑↑p : ℝ) ^ w.re :=
      lt_trans hpσ (Real.rpow_lt_rpow_of_exponent_lt hp1 hw)
    have hnorm : 1 < ‖(↑↑p : ℂ) ^ w‖ := by
      rw [Complex.norm_natCast_cpow_of_pos hp_pos]; exact hpw
    exact mul_ne_zero
      (fun h => by rw [h, norm_zero] at hnorm; linarith)
      (fun h => by rw [sub_eq_zero] at h; rw [h, norm_one] at hnorm; linarith)

set_option maxHeartbeats 400000 in
lemma phiCorrection_term_norm_bound (p : Nat.Primes) (σ : ℝ) (hσ : 1 / 2 < σ)
    (w : ℂ) (hw : σ < w.re) :
    ‖(Real.log (↑↑p : ℝ) : ℂ) / ((↑↑p : ℂ) ^ w * ((↑↑p : ℂ) ^ w - 1))‖ ≤
    Real.log (↑↑p : ℝ) / ((↑↑p : ℝ) ^ σ * ((↑↑p : ℝ) ^ σ - 1)) := by
  have hp_pos : (0 : ℕ) < ↑p := Nat.Prime.pos p.2
  have hp1 : (1 : ℝ) < (↑↑p : ℝ) := Nat.one_lt_cast.mpr (Nat.Prime.one_lt p.2)
  have hp_rpos : (0 : ℝ) < (↑↑p : ℝ) := by linarith
  have hnorm_pw : ‖(↑↑p : ℂ) ^ w‖ = (↑↑p : ℝ) ^ w.re := Complex.norm_natCast_cpow_of_pos hp_pos w
  have hpw_ge : (↑↑p : ℝ) ^ σ ≤ (↑↑p : ℝ) ^ w.re :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hp1) (le_of_lt hw)
  have hpσ_gt1 : (1 : ℝ) < (↑↑p : ℝ) ^ σ := by
    calc (1:ℝ) = (↑↑p:ℝ) ^ (0:ℝ) := by simp
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hnorm_sub : (↑↑p : ℝ) ^ σ - 1 ≤ ‖(↑↑p : ℂ) ^ w - 1‖ :=
    calc (↑↑p : ℝ) ^ σ - 1 ≤ (↑↑p : ℝ) ^ w.re - 1 := by linarith [hpw_ge]
      _ = ‖(↑↑p : ℂ) ^ w‖ - ‖(1 : ℂ)‖ := by rw [hnorm_pw]; simp
      _ ≤ ‖(↑↑p : ℂ) ^ w - 1‖ := by linarith [norm_sub_norm_le ((↑↑p : ℂ) ^ w) 1]
  have hdenom_bound : (↑↑p : ℝ) ^ σ * ((↑↑p : ℝ) ^ σ - 1) ≤
      ‖(↑↑p : ℂ) ^ w * ((↑↑p : ℂ) ^ w - 1)‖ := by
    rw [norm_mul]
    exact mul_le_mul (by rw [hnorm_pw]; exact hpw_ge) hnorm_sub (by linarith) (norm_nonneg _)
  have hdenom_pos : 0 < (↑↑p : ℝ) ^ σ * ((↑↑p : ℝ) ^ σ - 1) :=
    mul_pos (Real.rpow_pos_of_pos hp_rpos _) (by linarith)
  have hlog_nn : 0 ≤ Real.log (↑↑p : ℝ) := Real.log_nonneg (by linarith)
  calc ‖(Real.log (↑↑p : ℝ) : ℂ) / ((↑↑p : ℂ) ^ w * ((↑↑p : ℂ) ^ w - 1))‖
      = ‖(Real.log (↑↑p : ℝ) : ℂ)‖ / ‖(↑↑p : ℂ) ^ w * ((↑↑p : ℂ) ^ w - 1)‖ := norm_div _ _
    _ = Real.log (↑↑p : ℝ) / ‖(↑↑p : ℂ) ^ w * ((↑↑p : ℂ) ^ w - 1)‖ := by
        congr 1; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog_nn]
    _ ≤ Real.log (↑↑p : ℝ) / ((↑↑p : ℝ) ^ σ * ((↑↑p : ℝ) ^ σ - 1)) :=
        div_le_div_of_nonneg_left hlog_nn hdenom_pos hdenom_bound

set_option maxHeartbeats 800000 in
lemma phiCorrection_summable_bound (σ : ℝ) (hσ : 1 / 2 < σ) :
    Summable (fun p : Nat.Primes =>
      Real.log (↑↑p : ℝ) / ((↑↑p : ℝ) ^ σ * ((↑↑p : ℝ) ^ σ - 1))) := by
  set ε := (2 * σ - 1) / 2
  have hε_pos : 0 < ε := by simp only [ε]; linarith
  set α := 2 * σ - ε
  have hα_gt : 1 < α := by simp only [α, ε]; linarith
  set c := 1 - (2 : ℝ) ^ (-σ)
  have hc_pos : 0 < c := by
    simp only [c, sub_pos, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ (by
      calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by simp
        _ < (2 : ℝ) ^ σ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith))
  apply Summable.of_nonneg_of_le
  · intro p
    apply div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.Prime.one_le p.2))
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (le_of_lt (prime_rpow_sub_one_pos p σ hσ))
  · intro p
    have hp : (2 : ℝ) ≤ (↑↑p : ℝ) := Nat.ofNat_le_cast.mpr (Nat.Prime.two_le p.2)
    have hp_pos : (0 : ℝ) < (↑↑p : ℝ) := by linarith
    have hlog : Real.log (↑↑p : ℝ) ≤ (↑↑p : ℝ) ^ ε / ε :=
      Real.log_le_rpow_div (le_of_lt hp_pos) hε_pos
    have hdenom : c * (↑↑p : ℝ) ^ (2 * σ) ≤ (↑↑p : ℝ) ^ σ * ((↑↑p : ℝ) ^ σ - 1) :=
      rpow_sub_one_bound hp (by linarith)
    have hdenom_pos : 0 < (↑↑p : ℝ) ^ σ * ((↑↑p : ℝ) ^ σ - 1) :=
      lt_of_lt_of_le (mul_pos hc_pos (Real.rpow_pos_of_pos hp_pos _)) hdenom
    calc Real.log (↑↑p : ℝ) / ((↑↑p : ℝ) ^ σ * ((↑↑p : ℝ) ^ σ - 1))
        ≤ ((↑↑p : ℝ) ^ ε / ε) / ((↑↑p : ℝ) ^ σ * ((↑↑p : ℝ) ^ σ - 1)) :=
          div_le_div_of_nonneg_right hlog (le_of_lt hdenom_pos)
      _ ≤ ((↑↑p : ℝ) ^ ε / ε) / (c * (↑↑p : ℝ) ^ (2 * σ)) := by
          apply div_le_div_of_nonneg_left _ (mul_pos hc_pos (Real.rpow_pos_of_pos hp_pos _)) hdenom
          exact div_nonneg (Real.rpow_nonneg (le_of_lt hp_pos) _) (le_of_lt hε_pos)
      _ = (1 / (ε * c)) * ((↑↑p : ℝ) ^ (-α)) := by
          rw [Real.rpow_neg (le_of_lt hp_pos)]
          field_simp
          rw [← Real.rpow_add hp_pos]
          congr 1; simp only [α]; ring
  · exact (summable_primes_rpow_neg hα_gt).const_smul (1 / (ε * c))

set_option maxHeartbeats 800000 in
theorem phiCorrection_holomorphic :
    DifferentiableOn ℂ PhiCorrection {s : ℂ | 1/2 < s.re} := by
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  obtain ⟨σ, hσ1, hσ2⟩ : ∃ σ : ℝ, 1 / 2 < σ ∧ σ < s.re :=
    ⟨(s.re + 1/2) / 2, by linarith, by linarith⟩
  have hU : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ PhiCorrection {w : ℂ | σ < w.re} := by
    unfold PhiCorrection
    exact Complex.differentiableOn_tsum_of_summable_norm
      (phiCorrection_summable_bound σ hσ1)
      (fun p => phiCorrection_term_differentiableOn p σ hσ1)
      hU
      (fun p w hw => phiCorrection_term_norm_bound p σ hσ1 w hw)
  exact (hdiff.differentiableAt (hU.mem_nhds hσ2)).differentiableWithinAt

lemma tsum_eq_tsum_primes_of_support_subset_prime_powers {f : ℕ → ℂ}
    (hf : Summable f)
    (hsupp : Function.support f ⊆ {n : ℕ | IsPrimePow n}) :
    ∑' n, f n = ∑' (p : Nat.Primes) (k : ℕ), f (p.val ^ (k + 1)) := by
  let φ : Nat.Primes × ℕ → ℕ := fun pk => pk.1.val ^ (pk.2 + 1)
  have hφ_inj : Function.Injective φ := by
    intro ⟨p, k⟩ ⟨q, l⟩ h
    have := Nat.Prime.pow_inj p.prop q.prop h
    exact Prod.ext (Subtype.ext this.1) (by omega)
  have step1 : ∑' n, f n = ∑' pk : Nat.Primes × ℕ, (f ∘ φ) pk := by
    apply tsum_eq_tsum_of_ne_zero_bij (fun ⟨pk, hpk⟩ => φ pk)
    · intro ⟨pk1, _⟩ ⟨pk2, _⟩ h; exact Subtype.ext (hφ_inj h)
    · intro n hn
      have hipp : IsPrimePow n := hsupp hn
      rw [isPrimePow_nat_iff] at hipp
      obtain ⟨p, k, hp, hk, hpk⟩ := hipp
      refine ⟨⟨(⟨p, hp⟩, k - 1), ?_⟩, ?_⟩
      · simp only [Function.comp_def, Function.mem_support, φ]
        have hk1 : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
        rw [hk1, hpk]; exact hn
      · simp only [φ]
        have hk1 : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
        rw [hk1, hpk]
    · intro ⟨pk, _⟩; rfl
  rw [step1, (hf.comp_injective hφ_inj).tsum_prod]
  simp only [Function.comp_def, φ]

lemma vonMangoldt_LSeries_eq_double_sum (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => ↑(ArithmeticFunction.vonMangoldt n)) s =
    ∑' p : Nat.Primes, ∑' k : ℕ,
      (Real.log ↑(↑p : ℕ) : ℂ) / (↑(↑p : ℕ) : ℂ) ^ ((↑(k + 1) : ℕ) • s) := by

  unfold LSeries
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs) _]
  ·
    congr 1
    ext p
    congr 1
    ext k
    have hpk_ne : (↑p : ℕ) ^ (k + 1) ≠ 0 := pow_ne_zero _ p.prop.ne_zero
    rw [LSeries.term_of_ne_zero hpk_ne]
    congr 1
    ·
      simp [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k + 1 ≠ 0),
            ArithmeticFunction.vonMangoldt_apply_prime p.prop]
    ·
      rw [Nat.cast_pow, nsmul_eq_mul, ← Complex.natCast_cpow_natCast_mul]
  ·
    intro n hn
    simp only [Function.mem_support, Set.mem_setOf_eq] at hn ⊢
    by_contra h_not
    apply hn
    simp only [LSeries.term]
    split_ifs with h0
    · rfl
    · have : ArithmeticFunction.vonMangoldt n = 0 :=
        ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h_not
      simp [this]

theorem vonMangoldt_LSeries_eq_Phi_add_PhiCorrection (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => ↑(ArithmeticFunction.vonMangoldt n)) s = Phi s + PhiCorrection s := by

  set Λ := fun n => (↑(ArithmeticFunction.vonMangoldt n) : ℂ) with hΛ_def


  have hr_norm : ∀ p : Nat.Primes, ‖(↑(p.val) : ℂ) ^ (-s)‖ < 1 := by
    intro p
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
    rw [Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)

  rw [vonMangoldt_LSeries_eq_double_sum s hs]


  conv_lhs =>
    arg 1; ext p; arg 1; ext k
    rw [nsmul_eq_mul, mul_comm, Complex.cpow_mul_nat,
        div_eq_mul_inv, ← inv_pow, ← Complex.cpow_neg]


  conv_lhs =>
    arg 1; ext p
    rw [show (∑' k, (↑(log ↑(↑p : ℕ)) : ℂ) * ((↑(↑p : ℕ) : ℂ) ^ (-s)) ^ (k + 1)) =
        (↑(log ↑(↑p : ℕ)) : ℂ) * ∑' k, ((↑(↑p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) from tsum_mul_left]


  have hgeom : ∀ p : Nat.Primes,
      ∑' k, ((↑(↑p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) =
      (↑(↑p : ℕ) : ℂ) ^ (-s) / (1 - (↑(↑p : ℕ) : ℂ) ^ (-s)) := by
    intro p
    have := hasSum_geometric_of_norm_lt_one (hr_norm p)
    conv_lhs => arg 1; ext k; rw [pow_succ']
    rw [tsum_mul_left, this.tsum_eq, div_eq_mul_inv]
  simp_rw [hgeom]


  have hpf : ∀ p : Nat.Primes,
      (↑(log ↑(↑p : ℕ)) : ℂ) * ((↑(↑p : ℕ) : ℂ) ^ (-s) / (1 - (↑(↑p : ℕ) : ℂ) ^ (-s))) =
      (↑(log ↑(↑p : ℕ)) : ℂ) * (↑(↑p : ℕ) : ℂ) ^ (-s) +
      (↑(log ↑(↑p : ℕ)) : ℂ) / ((↑(↑p : ℕ) : ℂ) ^ s * ((↑(↑p : ℕ) : ℂ) ^ s - 1)) := by
    intro p
    have hr0 : (↑(↑p : ℕ) : ℂ) ^ (-s) ≠ 0 := by
      have : ‖(↑(↑p : ℕ) : ℂ) ^ (-s)‖ > 0 := by
        rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
        exact Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos : (0 : ℝ) < ↑(↑p : ℕ)) _
      exact norm_pos_iff.mp this
    have hr1 : (↑(↑p : ℕ) : ℂ) ^ (-s) ≠ 1 := by
      intro h; have := hr_norm p; rw [h, norm_one] at this; linarith
    have h1r : 1 - (↑(↑p : ℕ) : ℂ) ^ (-s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
    have hq_eq : (↑(↑p : ℕ) : ℂ) ^ s = ((↑(↑p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      rw [Complex.cpow_neg, inv_inv]
    rw [hq_eq]
    field_simp
    ring
  simp_rw [hpf]


  unfold Phi PhiCorrection

  have hsPhi : Summable (fun p : Nat.Primes =>
      (↑(log ↑(↑p : ℕ)) : ℂ) * (↑(↑p : ℕ) : ℂ) ^ (-s)) := by
    apply Summable.of_norm
    simp_rw [Complex.norm_mul]
    have : ∀ p : Nat.Primes,
        ‖(↑(log ↑(↑p : ℕ)) : ℂ)‖ * ‖(↑(↑p : ℕ) : ℂ) ^ (-s)‖ =
        log ↑(↑p : ℕ) * (↑(↑p : ℕ) : ℝ) ^ (-s.re) := by
      intro p
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast Nat.Prime.one_le p.prop)),
          Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
    simp_rw [this]
    exact abel_summable_primes_log_rpow s.re hs
  have hsCorr : Summable (fun p : Nat.Primes =>
      (↑(log ↑(↑p : ℕ)) : ℂ) / ((↑(↑p : ℕ) : ℂ) ^ s * ((↑(↑p : ℕ) : ℂ) ^ s - 1))) := by
    apply Summable.of_norm
    set σ₀ := s.re / 2 + 1 / 4 with hσ₀_def
    have hσ₀ : 1 / 2 < σ₀ := by linarith
    have hσ₀_lt : σ₀ < s.re := by linarith
    exact Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => phiCorrection_term_norm_bound p σ₀ hσ₀ s hσ₀_lt)
      (phiCorrection_summable_bound σ₀ hσ₀)
  exact hsPhi.tsum_add hsCorr

theorem euler_product_log_deriv (s : ℂ) (hs : 1 < s.re) :
    -(deriv riemannZeta s) / riemannZeta s = Phi s + PhiCorrection s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  exact vonMangoldt_LSeries_eq_Phi_add_PhiCorrection s hs

theorem log_deriv_zeta_meromorphic_on_pos_re :
    MeromorphicOn (fun s => -(deriv riemannZeta s) / riemannZeta s) {s : ℂ | 0 < s.re} :=
  fun s _ => ((meromorphicAt_riemannZeta s).deriv.neg).div (meromorphicAt_riemannZeta s)

theorem log_deriv_zeta_minus_pole_holomorphic :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h {s : ℂ | 1 ≤ s.re} ∧
    ∀ s : ℂ, 1 < s.re → h s = -(deriv riemannZeta s) / riemannZeta s - 1 / (s - 1) := by
  refine ⟨fun s => -(deriv G₀ s) / G₀ s, ?_, ?_⟩
  ·
    have hGanalytic : AnalyticOnNhd ℂ G₀ Set.univ :=
      G₀_differentiable.differentiableOn.analyticOnNhd isOpen_univ
    apply DifferentiableOn.div
    · exact (hGanalytic.deriv.differentiableOn.mono (Set.subset_univ _)).neg
    · exact G₀_differentiable.differentiableOn.mono (Set.subset_univ _)
    · intro s hs; exact G₀_ne_zero_of_one_le_re hs
  ·
    intro s hre
    have hs : s ≠ 1 := fun h => by simp [h] at hre
    have hG_eq : G₀ =ᶠ[𝓝 s] (fun t => (t - 1) * riemannZeta t) := by
      filter_upwards [eventually_ne_nhds hs] with t ht; exact G₀_eq_of_ne ht
    have hderiv : HasDerivAt (fun t => (t - 1) * riemannZeta t)
        (riemannZeta s + (s - 1) * deriv riemannZeta s) s := by
      simpa using ((hasDerivAt_id s).sub_const 1).mul
        (differentiableAt_riemannZeta hs).hasDerivAt
    have hderivG : deriv G₀ s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
      rw [hG_eq.deriv_eq]; exact hderiv.deriv
    simp only []
    rw [hderivG, G₀_eq_of_ne hs]
    have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hre)
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    field_simp; ring

theorem lem_16_11_Phi_holomorphic :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s : ℂ | 1 ≤ s.re} ∧
    ∀ s : ℂ, 1 < s.re → g s = Phi s - 1 / (s - 1) := by
  obtain ⟨h, hh_diff, hh_eq⟩ := log_deriv_zeta_minus_pole_holomorphic
  refine ⟨fun s => h s - PhiCorrection s, ?_, ?_⟩
  · exact hh_diff.sub (phiCorrection_holomorphic.mono (fun s (hs : 1 ≤ s.re) => by
      show (1 : ℝ) / 2 < s.re; linarith))
  · intro s hs
    simp only []
    rw [hh_eq s hs, euler_product_log_deriv s hs]
    ring

theorem lem_16_11_Phi_meromorphic :
    ∃ g : ℂ → ℂ, MeromorphicOn g {s : ℂ | 1/2 < s.re} ∧
    ∀ s : ℂ, 1 < s.re → g s = Phi s - 1 / (s - 1) := by
  refine ⟨fun s => -(deriv riemannZeta s) / riemannZeta s -
    PhiCorrection s - 1 / (s - 1), ?_, ?_⟩
  · have hopen : IsOpen {s : ℂ | (1:ℝ)/2 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h1 : MeromorphicOn (fun s => -(deriv riemannZeta s) / riemannZeta s)
        {s : ℂ | (1:ℝ)/2 < s.re} :=
      log_deriv_zeta_meromorphic_on_pos_re.mono_set
        (fun s (hs : (1:ℝ)/2 < s.re) => by show 0 < s.re; linarith)
    have h2 : MeromorphicOn PhiCorrection {s : ℂ | (1:ℝ)/2 < s.re} :=
      (phiCorrection_holomorphic.analyticOnNhd hopen).meromorphicOn
    have h3 : MeromorphicOn (fun s : ℂ => 1 / (s - 1)) {s : ℂ | (1:ℝ)/2 < s.re} :=
      (MeromorphicOn.const 1).div (MeromorphicOn.id.sub (MeromorphicOn.const 1))
    exact (h1.sub h2).sub h3
  · intro s hs
    simp only []
    rw [euler_product_log_deriv s hs]
    ring

noncomputable def boundedProj (z : ℂ) (C : ℝ) : ℂ :=
  if ‖z‖ ≤ C then z else ((C : ℂ) / (‖z‖ : ℂ)) * z

lemma norm_boundedProj_le (z : ℂ) (C : ℝ) (hC : 0 ≤ C) : ‖boundedProj z C‖ ≤ C := by
  unfold boundedProj; split_ifs with h
  · exact h
  · push Not at h
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z),
        div_mul_cancel₀ _ (ne_of_gt (lt_of_le_of_lt hC h))]

noncomputable def right_semicircle_integrand
    (g : ℂ → ℂ) (f : ℝ → ℝ) (r : ℝ) (τ u : ℝ) : ℂ :=
  let R : ℂ := (r : ℂ)
  let s : ℂ := R * Complex.exp (Complex.I * ↑u)
  boundedProj
    ((g s - ∫ t in (0:ℝ)..τ, (Complex.exp (-s * ↑t) : ℂ) * ↑(f t)) *
      Complex.exp (s * ↑τ) * (s⁻¹ + s / R ^ 2) * (R * Complex.I * Complex.exp (Complex.I * ↑u)))
    (2 / r)

noncomputable def newman_cif_I_right
    (f : ℝ → ℝ) (M : ℝ) (hM : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {s : ℂ | 0 ≤ s.re})
    (hg_laplace : ∀ s : ℂ, 0 < s.re → g s = laplace_transform f s)
    (r : ℝ) (hr : 0 < r) : ℝ → ℂ :=
  fun τ =>
    (1 / (2 * ↑Real.pi * Complex.I)) *
      ∫ u in (-(Real.pi/2))..(Real.pi/2),
        right_semicircle_integrand g f r τ u

noncomputable def left_semicircle_integrand
    (g : ℂ → ℂ) (f : ℝ → ℝ) (r : ℝ) (τ u : ℝ) : ℂ :=
  let R : ℂ := (r : ℂ)
  let s : ℂ := R * Complex.exp (Complex.I * ↑u)
  boundedProj
    ((g s - ∫ t in (0:ℝ)..τ, (Complex.exp (-s * ↑t) : ℂ) * ↑(f t)) *
      Complex.exp (s * ↑τ) * (s⁻¹ + s / R ^ 2) * (R * Complex.I * Complex.exp (Complex.I * ↑u)))
    (2 / r)

noncomputable def newman_cif_I_left
    (f : ℝ → ℝ) (M : ℝ) (hM : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {s : ℂ | 0 ≤ s.re})
    (hg_laplace : ∀ s : ℂ, 0 < s.re → g s = laplace_transform f s)
    (r : ℝ) (hr : 0 < r) : ℝ → ℂ :=
  fun τ =>
    (1 / (2 * ↑Real.pi * Complex.I)) *
      ∫ u in (Real.pi/2)..(3*Real.pi/2),
        left_semicircle_integrand g f r τ u



theorem newman_right_semicircle_bound
    (f : ℝ → ℝ) (M : ℝ) (hM : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {s : ℂ | 0 ≤ s.re})
    (hg_laplace : ∀ s : ℂ, 0 < s.re → g s = laplace_transform f s)
    (r : ℝ) (hr : 0 < r) :
    ∀ τ : ℝ, ‖newman_cif_I_right f M hM g hg_holo hg_laplace r hr τ‖ ≤ 1 / r := by
  intro τ
  unfold newman_cif_I_right
  calc ‖(1 / (2 * ↑Real.pi * Complex.I)) *
        ∫ u in (-(Real.pi/2))..(Real.pi/2), right_semicircle_integrand g f r τ u‖
      ≤ ‖(1 : ℂ) / (2 * ↑Real.pi * Complex.I)‖ *
        ‖∫ u in (-(Real.pi/2))..(Real.pi/2), right_semicircle_integrand g f r τ u‖ :=
          norm_mul_le _ _
    _ ≤ ‖(1 : ℂ) / (2 * ↑Real.pi * Complex.I)‖ *
        ((2 / r) * |Real.pi / 2 - (-(Real.pi / 2))|) := by
          gcongr
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro u _
          exact norm_boundedProj_le _ _ (by positivity)
    _ = 1 / r := by
          have hpi : Real.pi > 0 := Real.pi_pos
          rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_mul,
              Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hpi, Complex.norm_I, mul_one]
          rw [abs_of_pos (by linarith : Real.pi / 2 - -(Real.pi / 2) > 0)]
          field_simp
          ring

theorem newman_left_semicircle_bound
    (f : ℝ → ℝ) (M : ℝ) (hM : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {s : ℂ | 0 ≤ s.re})
    (hg_laplace : ∀ s : ℂ, 0 < s.re → g s = laplace_transform f s)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ τ in atTop, ‖newman_cif_I_left f M hM g hg_holo hg_laplace r hr τ‖ ≤ 1 / r := by
  apply Filter.Eventually.of_forall
  intro τ
  unfold newman_cif_I_left
  calc ‖(1 / (2 * ↑Real.pi * Complex.I)) *
        ∫ u in (Real.pi/2)..(3*Real.pi/2), left_semicircle_integrand g f r τ u‖
      ≤ ‖(1 : ℂ) / (2 * ↑Real.pi * Complex.I)‖ *
        ‖∫ u in (Real.pi/2)..(3*Real.pi/2), left_semicircle_integrand g f r τ u‖ :=
          norm_mul_le _ _
    _ ≤ ‖(1 : ℂ) / (2 * ↑Real.pi * Complex.I)‖ *
        ((2 / r) * |3 * Real.pi / 2 - Real.pi / 2|) := by
          gcongr
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro u _
          exact norm_boundedProj_le _ _ (by positivity)
    _ = 1 / r := by
          have hpi : Real.pi > 0 := Real.pi_pos
          rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_mul,
              Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hpi, Complex.norm_I, mul_one]
          rw [abs_of_pos (by linarith : 3 * Real.pi / 2 - Real.pi / 2 > 0)]
          field_simp
          ring






noncomputable def H (t : ℝ) : ℝ := θ (exp t) * exp (-t) - 1

theorem H_bounded : ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → |H t| ≤ M := by
  use log 4 + 1
  intro t ht
  simp only [H]
  have hexp : 0 < exp t := Real.exp_pos t
  have htheta_bound : θ (exp t) ≤ log 4 * exp t := theta_le_log4_mul_x (le_of_lt hexp)
  have htheta_nonneg : 0 ≤ θ (exp t) := theta_nonneg _
  have hexp_neg_pos : 0 < exp (-t) := Real.exp_pos _
  have cancel : exp t * exp (-t) = 1 := by rw [← Real.exp_add]; simp
  rw [abs_le]
  constructor
  ·
    have : 0 ≤ θ (exp t) * exp (-t) := mul_nonneg htheta_nonneg (le_of_lt hexp_neg_pos)
    linarith [Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)]
  ·
    have h1 : θ (exp t) * exp (-t) ≤ log 4 * exp t * exp (-t) :=
      mul_le_mul_of_nonneg_right htheta_bound (le_of_lt hexp_neg_pos)
    have h2 : log 4 * exp t * exp (-t) = log 4 := by rw [mul_assoc, cancel, mul_one]
    linarith

theorem laplace_H_identity (s : ℂ) (hs : 0 < s.re) :
    laplace_transform H s = Phi (s + 1) / (s + 1) - 1 / s := by

  unfold laplace_transform H


  have integrand_eq : ∀ t : ℝ,
      Complex.exp (-s * ↑t) * (↑(θ (exp t) * exp (-t) - 1) : ℂ) =
      Complex.exp (-(s + 1) * ↑t) * (↑(θ (exp t)) : ℂ) - Complex.exp (-s * ↑t) := by
    intro t
    have key : Complex.exp (-(s + 1) * ↑t) = Complex.exp (-s * ↑t) * Complex.exp (-(1 : ℂ) * ↑t) := by
      rw [← Complex.exp_add]; ring_nf
    rw [key]
    have key2 : Complex.exp (-(1 : ℂ) * ↑t) = (↑(exp (-t)) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [key2]; push_cast; ring
  simp_rw [integrand_eq]

  have h_theta_int : IntegrableOn
      (fun t : ℝ => Complex.exp (-(s + 1) * ↑t) * (↑(θ (exp t)) : ℂ)) (Set.Ioi 0) := by


    have hf : IntegrableOn
        (fun t : ℝ => Complex.exp (-s * ↑t) * (↑(θ (exp t) * exp (-t) - 1) : ℂ))
        (Set.Ioi 0) := by
      apply Integrable.mono' (g := fun t => (log 4 + 1) * exp (-s.re * t))
      · exact (integrableOn_exp_mul_Ioi (by linarith : -s.re < 0) 0).const_mul _
      · refine AEStronglyMeasurable.restrict ?_
        exact ((Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).measurable.aestronglyMeasurable).mul
          (Complex.measurable_ofReal.comp
            (((Chebyshev.theta_mono.measurable.comp Real.measurable_exp).mul
              (Real.measurable_exp.comp measurable_neg)).sub measurable_const)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
        rw [Complex.norm_mul, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
                   Complex.ofReal_im, mul_zero, sub_zero]
        rw [mul_comm (log 4 + 1) _, Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        rw [abs_le]
        exact ⟨by linarith [mul_nonneg (theta_nonneg (exp t)) (Real.exp_nonneg (-t)),
                    Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)],
               by have := theta_le_log4_mul_x (le_of_lt (Real.exp_pos t))
                  have hc : exp t * exp (-t) = 1 := by rw [← Real.exp_add]; simp
                  linarith [mul_le_mul_of_nonneg_right this (Real.exp_nonneg (-t)),
                    show log 4 * exp t * exp (-t) = log 4 from
                      by rw [mul_assoc, hc, mul_one]]⟩
    have hh : IntegrableOn (fun t : ℝ => Complex.exp (-s * ↑t)) (Set.Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (by simp [Complex.neg_re]; linarith) 0
    have heq : ∀ t, Complex.exp (-(s + 1) * ↑t) * (↑(θ (exp t)) : ℂ) =
        Complex.exp (-s * ↑t) * (↑(θ (exp t) * exp (-t) - 1) : ℂ) +
        Complex.exp (-s * ↑t) := by
      intro t; rw [integrand_eq]; ring
    simp_rw [heq]; exact hf.add hh
  have h_exp_int : IntegrableOn (fun t : ℝ => Complex.exp (-s * ↑t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simp [Complex.neg_re]; linarith) 0

  rw [integral_sub h_theta_int h_exp_int]

  have hs1 : 1 < (s + 1).re := by simp [Complex.add_re]; linarith
  rw [show (∫ t in Set.Ioi (0:ℝ), Complex.exp (-(s + 1) * ↑t) * (↑(θ (exp t)) : ℂ)) =
      laplace_transform (fun t => θ (exp t)) (s + 1) from rfl]
  rw [lem_16_10_laplace_theta (s + 1) hs1]

  rw [integral_exp_mul_complex_Ioi (by simp [Complex.neg_re]; linarith) 0]
  simp [Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem cor_16_12_Phi_shift_meromorphic :
    ∃ g : ℂ → ℂ, MeromorphicOn g {s : ℂ | -(1:ℝ)/2 < s.re} ∧
    ∀ s : ℂ, 0 < s.re → g s = Phi (s + 1) - 1 / s := by
  obtain ⟨g₁, hg₁_mero, hg₁_eq⟩ := lem_16_11_Phi_meromorphic
  refine ⟨fun s => g₁ (s + 1), ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    have hx' : (1:ℝ)/2 < (x + 1).re := by
      simp [Complex.add_re]; linarith
    have hg_an : AnalyticAt ℂ (fun s : ℂ => s + 1) x := analyticAt_id.add analyticAt_const
    have hg_deriv : deriv (fun s : ℂ => s + 1) x ≠ 0 := by simp
    exact (meromorphicAt_comp_iff_of_deriv_ne_zero hg_an hg_deriv).mpr (hg₁_mero (x + 1) hx')
  · intro s hs
    have hs1 : 1 < (s + 1).re := by simp [Complex.add_re]; linarith
    have := hg₁_eq (s + 1) hs1
    have h_simp : (s + 1 : ℂ) - 1 = s := by ring
    rw [h_simp] at this
    exact this

theorem cor_16_12_laplace_H_holomorphic :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s : ℂ | 0 ≤ s.re} ∧
    ∀ s : ℂ, 0 < s.re → g s = Phi (s + 1) / (s + 1) - 1 / s := by
  obtain ⟨g₁, hg₁_diff, hg₁_eq⟩ := lem_16_11_Phi_holomorphic
  refine ⟨fun s => (g₁ (s + 1) - 1) / (s + 1), ?_, ?_⟩
  ·
    apply DifferentiableOn.div
    · apply DifferentiableOn.sub
      · exact DifferentiableOn.comp hg₁_diff
          (differentiableOn_id.add (differentiableOn_const 1))
          (fun s hs => by
            simp only [Set.mem_setOf_eq] at hs ⊢
            simp [Complex.add_re]; linarith)
      · exact differentiableOn_const 1
    · exact differentiableOn_id.add (differentiableOn_const 1)
    · intro s hs
      simp only [Set.mem_setOf_eq] at hs
      intro h
      have : (s + 1).re = 0 := by rw [show s + 1 = 0 from h]; simp
      simp [Complex.add_re] at this; linarith
  ·
    intro s hs
    simp only []
    have hs1 : 1 < (s + 1).re := by simp [Complex.add_re]; linarith
    have hg₁_val := hg₁_eq (s + 1) hs1
    have h_simp : (s + 1 : ℂ) - 1 = s := by ring
    rw [h_simp] at hg₁_val
    rw [hg₁_val]
    have hs_ne : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
    have hs1_ne : s + 1 ≠ 0 := by
      intro h; have : (s + 1).re = 0 := by rw [h]; simp
      simp [Complex.add_re] at this; linarith
    field_simp
    ring

theorem H_integral_change_of_variables (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in Set.Ioc 0 T, H t =
    ∫ x in Set.Ioc 1 (exp T), (θ x - x) / x ^ 2 := by

  have himage : Set.Ioc 1 (exp T) = exp '' Set.Ioc 0 T := by
    ext y; simp only [Set.mem_image, Set.mem_Ioc]; constructor
    · rintro ⟨h1, h2⟩
      have hy : 0 < y := by linarith
      exact ⟨Real.log y, ⟨by rw [← Real.log_one]; exact Real.log_lt_log one_pos h1,
        by rwa [← Real.exp_le_exp, Real.exp_log hy]⟩, Real.exp_log hy⟩
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr h1,
             Real.exp_le_exp.mpr h2⟩

  rw [himage]
  rw [integral_image_eq_integral_abs_deriv_smul (s := Set.Ioc 0 T) (f := exp) (f' := exp)
    measurableSet_Ioc
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    ((Real.exp_strictMono.strictMonoOn _).injOn)]

  congr 1; ext t
  simp only [abs_of_pos (Real.exp_pos t), smul_eq_mul, H]
  rw [Real.exp_neg]
  field_simp




end Chapter16
