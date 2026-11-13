/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option autoImplicit false

open Finset Filter Topology BigOperators Set Polynomial Complex

set_option maxHeartbeats 800000

theorem summation_by_parts_convergence
    (a v : ℕ → ℂ)
    (hA : ∃ M : ℝ, ∀ n, ‖∑ k ∈ range (n + 1), a k‖ ≤ M)
    (hv : Tendsto v atTop (nhds 0))
    (hvs : Summable (fun n => ‖v n - v (n + 1)‖)) :
    ∃ l, Tendsto (fun N => ∑ i ∈ range N, a i * v i) atTop (nhds l) := by
  set A : ℕ → ℂ := fun n => ∑ k ∈ range (n + 1), a k with hA_def
  obtain ⟨M, hM⟩ := hA
  have hsumm : Summable (fun i => (v i - v (i + 1)) * A i) := by
    apply Summable.of_norm_bounded (g := fun i => M * ‖v i - v (i + 1)‖) (hvs.mul_left M)
    intro i
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _)
  have htend : Tendsto (fun n => v n * A n) atTop (nhds 0) := by
    have hbdd : IsBoundedUnder (· ≤ ·) atTop (norm ∘ A) :=
      ⟨M, eventually_map.mpr (Eventually.of_forall fun n => hM n)⟩
    have := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hv hbdd
    simp only [smul_eq_mul] at this
    exact this
  have habp : ∀ n, ∑ i ∈ range (n + 1), a i * v i =
      v n * A n + ∑ i ∈ range n, (v i - v (i + 1)) * A i := by
    intro n
    have := Finset.sum_range_by_parts v a (n + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at this
    simp_rw [mul_comm (a _) (v _)]
    rw [this, sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    congr 1; ext x; ring
  have hsum_tend : Tendsto (fun n => ∑ i ∈ range n, (v i - v (i + 1)) * A i)
      atTop (nhds (∑' i, (v i - v (i + 1)) * A i)) :=
    hsumm.hasSum.tendsto_sum_nat
  have hcomb : Tendsto (fun n => ∑ i ∈ range (n + 1), a i * v i) atTop
      (nhds (∑' i, (v i - v (i + 1)) * A i)) := by
    simp_rw [habp]
    rw [show (∑' i, (v i - v (i + 1)) * A i) = 0 + ∑' i, (v i - v (i + 1)) * A i
      from (zero_add _).symm]
    exact htend.add hsum_tend
  exact ⟨∑' i, (v i - v (i + 1)) * A i, (tendsto_add_atTop_iff_nat 1).mp hcomb⟩

namespace MittagLeffler

noncomputable def singularPart (P : Polynomial ℂ) (b : ℂ) (z : ℂ) : ℂ :=
  Polynomial.eval (1 / (z - b)) P

def HasNoConstantTerm (P : Polynomial ℂ) : Prop :=
  Polynomial.eval (0 : ℂ) P = 0

def HasSingularPartAt (f : ℂ → ℂ) (P : Polynomial ℂ) (b : ℂ) : Prop :=
  AnalyticAt ℂ (fun z => f z - singularPart P b z) b


lemma singularPart_analyticAt (P : Polynomial ℂ) (b z₀ : ℂ) (hz : z₀ ≠ b) :
    AnalyticAt ℂ (singularPart P b) z₀ := by
  unfold singularPart
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact hp.add hq
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    apply AnalyticAt.mul analyticAt_const
    apply AnalyticAt.pow
    exact AnalyticAt.div analyticAt_const (analyticAt_id.sub analyticAt_const)
      (by simp [sub_ne_zero]; exact hz)

lemma partialSum_eq_polynomial_eval (ps : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) (z : ℂ) :
    ps.partialSum N z = Polynomial.eval z
      (∑ k ∈ Finset.range N, Polynomial.C (ps.coeff k) * Polynomial.X ^ k) := by
  simp only [FormalMultilinearSeries.partialSum, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  congr 1; ext k
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp [smul_eq_mul, mul_comm]

lemma exists_correcting_poly_single (P : Polynomial ℂ) (b : ℂ) (hb : b ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (p : Polynomial ℂ), ∀ (z : ℂ), ‖z‖ ≤ ‖b‖ / 4 →
      ‖singularPart P b z - Polynomial.eval z p‖ ≤ ε := by
  set R : NNReal := ⟨‖b‖ / 2, by positivity⟩
  have hR_pos : (0 : NNReal) < R := by exact_mod_cast div_pos (norm_pos_iff.mpr hb) two_pos
  have hR_val : (R : ℝ) = ‖b‖ / 2 := rfl
  have hfps : HasFPowerSeriesOnBall (singularPart P b)
      (cauchyPowerSeries (singularPart P b) 0 R) 0 R := by
    apply DifferentiableOn.hasFPowerSeriesOnBall _ hR_pos
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact (singularPart_analyticAt P b z (by
      intro heq; rw [heq] at hz; linarith [norm_pos_iff.mpr hb])).differentiableAt.differentiableWithinAt
  set ps := cauchyPowerSeries (singularPart P b) 0 R
  set r' : NNReal := ⟨‖b‖ / 3, by positivity⟩
  have hb_pos := norm_pos_iff.mpr hb
  have hr'_lt : (r' : ENNReal) < R := by
    rw [ENNReal.coe_lt_coe]; exact_mod_cast show (‖b‖ / 3 : ℝ) < ‖b‖ / 2 by linarith
  obtain ⟨a, ha, C, hC, hbound⟩ := hfps.uniform_geometric_approx hr'_lt
  have htend : Tendsto (fun n => C * a ^ n) atTop (nhds 0) := by
    have : Tendsto (fun n => C * a ^ n) atTop (nhds (C * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one ha.1.le ha.2).const_mul C
    rwa [mul_zero] at this
  obtain ⟨N, hN⟩ := (htend.eventually (eventually_le_nhds hε)).exists
  exact ⟨∑ k ∈ Finset.range N, Polynomial.C (ps.coeff k) * Polynomial.X ^ k, fun z hz => by
    have hz_ball : z ∈ Metric.ball (0 : ℂ) r' := by
      rw [Metric.mem_ball, dist_zero_right]; linarith [show (r' : ℝ) = ‖b‖ / 3 from rfl]
    have h1 := hbound z hz_ball N; simp only [zero_add] at h1
    rw [← partialSum_eq_polynomial_eval]; linarith⟩

theorem exists_correcting_polynomials
    (b : ℕ → ℂ) (P : ℕ → Polynomial ℂ)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop)
    (hP : ∀ n, HasNoConstantTerm (P n)) :
    ∃ (p : ℕ → Polynomial ℂ),
      ∀ (ν : ℕ) (z : ℂ), ‖z‖ ≤ ‖b ν‖ / 4 →
        ‖singularPart (P ν) (b ν) z - Polynomial.eval z (p ν)‖ ≤ (2⁻¹ : ℝ) ^ ν := by
  have hchoice : ∀ ν, ∃ (p : Polynomial ℂ), ∀ (z : ℂ), ‖z‖ ≤ ‖b ν‖ / 4 →
      ‖singularPart (P ν) (b ν) z - Polynomial.eval z p‖ ≤ (2⁻¹ : ℝ) ^ ν := by
    intro ν
    by_cases hbν : b ν = 0
    · exact ⟨0, fun z hz => by
        simp only [hbν, norm_zero, zero_div] at hz
        have hz0 : z = 0 := by rw [← norm_eq_zero]; linarith [norm_nonneg z]
        subst hz0
        simp only [singularPart, hbν, sub_zero, one_div, inv_zero, Polynomial.eval_zero, sub_zero]
        rw [hP ν, norm_zero]; positivity⟩
    · exact exists_correcting_poly_single (P ν) (b ν) hbν ((2⁻¹ : ℝ) ^ ν) (by positivity)
  exact ⟨fun ν => (hchoice ν).choose, fun ν => (hchoice ν).choose_spec⟩

lemma singularPart_meromorphicAt (P : Polynomial ℂ) (b : ℂ) :
    MeromorphicAt (singularPart P b) b := by
  unfold singularPart
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact hp.fun_add hq
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    apply MeromorphicAt.fun_mul (MeromorphicAt.const a b)
    apply MeromorphicAt.pow
    apply MeromorphicAt.fun_div (MeromorphicAt.const 1 b)
    exact (analyticAt_id.sub analyticAt_const).meromorphicAt

lemma polynomial_eval_analyticAt (p : Polynomial ℂ) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => Polynomial.eval z p) z₀ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact hp.add hq
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    exact analyticAt_const.mul (analyticAt_id.pow n)

lemma correctedTerm_analyticAt (P : Polynomial ℂ) (b : ℂ) (p : Polynomial ℂ) (z₀ : ℂ)
    (hz : z₀ ≠ b) :
    AnalyticAt ℂ (fun z => singularPart P b z - Polynomial.eval z p) z₀ :=
  (singularPart_analyticAt P b z₀ hz).sub (polynomial_eval_analyticAt p z₀)

lemma summable_correctedTerms (b : ℕ → ℂ) (P : ℕ → Polynomial ℂ) (p : ℕ → Polynomial ℂ)
    (hbound : ∀ (ν : ℕ) (z : ℂ), ‖z‖ ≤ ‖b ν‖ / 4 →
      ‖singularPart (P ν) (b ν) z - Polynomial.eval z (p ν)‖ ≤ (2⁻¹ : ℝ) ^ ν)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (z : ℂ) :
    Summable (fun ν => singularPart (P ν) (b ν) z - Polynomial.eval z (p ν)) := by
  rw [Filter.tendsto_atTop_atTop] at hb
  obtain ⟨N, hN⟩ := hb (4 * ‖z‖ + 1)
  apply Summable.of_norm_bounded_eventually (g := fun ν => (2⁻¹ : ℝ) ^ ν)
  · exact summable_geometric_of_lt_one (by positivity) (by norm_num)
  · rw [Nat.cofinite_eq_atTop]
    exact Filter.eventually_atTop.mpr ⟨N, fun ν hν => hbound ν z (by linarith [hN ν hν])⟩

lemma h_analyticAt_away (b : ℕ → ℂ) (P : ℕ → Polynomial ℂ) (p : ℕ → Polynomial ℂ)
    (hbound : ∀ (ν : ℕ) (z : ℂ), ‖z‖ ≤ ‖b ν‖ / 4 →
      ‖singularPart (P ν) (b ν) z - Polynomial.eval z (p ν)‖ ≤ (2⁻¹ : ℝ) ^ ν)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop)
    (z₀ : ℂ) (hz₀ : ∀ n, z₀ ≠ b n) :
    AnalyticAt ℂ (fun z => ∑' ν, (singularPart (P ν) (b ν) z -
      Polynomial.eval z (p ν))) z₀ := by
  set R := ‖z₀‖ + 1
  have hR_pos : (0 : ℝ) < R := by positivity
  set f : ℕ → ℂ → ℂ := fun ν z =>
    singularPart (P ν) (b ν) z - Polynomial.eval z (p ν)
  have hsumm : ∀ z, Summable (f · z) :=
    fun z => summable_correctedTerms b P p hbound hb z
  obtain ⟨N, hN⟩ : ∃ N, ∀ ν ≥ N, 4 * R + 1 ≤ ‖b ν‖ := by
    rw [Filter.tendsto_atTop_atTop] at hb; exact hb (4 * R + 1)
  have heq : (fun z => ∑' ν, f ν z) =
      fun z => (∑ ν ∈ Finset.range N, f ν z) + (∑' n, f (n + N) z) := by
    ext z; exact ((hsumm z).sum_add_tsum_nat_add N).symm
  rw [heq]
  apply AnalyticAt.add
  · have : (fun z => ∑ ν ∈ Finset.range N, f ν z) = ∑ ν ∈ Finset.range N, f ν := by
      ext z; simp [Finset.sum_apply]
    rw [this]
    exact Finset.analyticAt_sum _ fun ν _ =>
      correctedTerm_analyticAt (P ν) (b ν) (p ν) z₀ (hz₀ ν)
  · apply DifferentiableOn.analyticAt
    · apply Complex.differentiableOn_tsum_of_summable_norm
        (U := Metric.ball (0 : ℂ) R) (u := fun n => (2⁻¹ : ℝ) ^ (n + N))
      · exact (summable_geometric_of_lt_one (by positivity) (by norm_num)).comp_injective
          (fun a b h => by omega)
      · intro n z hz
        apply DifferentiableAt.differentiableWithinAt
        apply AnalyticAt.differentiableAt
        apply correctedTerm_analyticAt
        intro heq'
        rw [Metric.mem_ball, dist_zero_right] at hz
        have := hN (n + N) (Nat.le_add_left N n)
        rw [heq'] at hz; linarith [hR_pos]
      · exact Metric.isOpen_ball
      · intro n w hw
        rw [Metric.mem_ball, dist_zero_right] at hw
        exact hbound (n + N) w (by linarith [hN (n + N) (Nat.le_add_left N n)])
    · exact Metric.isOpen_ball.mem_nhds
        (by rw [Metric.mem_ball, dist_zero_right]; linarith)

lemma remaining_tsum_analyticAt
    (b : ℕ → ℂ) (P : ℕ → Polynomial ℂ) (p : ℕ → Polynomial ℂ)
    (hbound : ∀ (ν : ℕ) (z : ℂ), ‖z‖ ≤ ‖b ν‖ / 4 →
      ‖singularPart (P ν) (b ν) z - Polynomial.eval z (p ν)‖ ≤ (2⁻¹ : ℝ) ^ ν)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop)
    (hinj : Function.Injective b)
    (n : ℕ) :
    AnalyticAt ℂ (fun z => ∑' ν, (if ν = n then (0 : ℂ) else
      (singularPart (P ν) (b ν) z - Polynomial.eval z (p ν)))) (b n) := by
  set f : ℕ → ℂ → ℂ := fun ν z =>
    singularPart (P ν) (b ν) z - Polynomial.eval z (p ν)
  set g : ℕ → ℂ → ℂ := fun ν z => if ν = n then 0 else f ν z
  have hg_summ : ∀ z, Summable (g · z) := by
    intro z
    apply Summable.of_norm_bounded_eventually (g := fun ν => (2⁻¹ : ℝ) ^ ν)
    · exact summable_geometric_of_lt_one (by positivity) (by norm_num)
    · rw [Filter.tendsto_atTop_atTop] at hb
      obtain ⟨N, hN⟩ := hb (4 * ‖z‖ + 1)
      rw [Nat.cofinite_eq_atTop]
      exact Filter.eventually_atTop.mpr ⟨N, fun ν hν => by
        simp only [g]
        split_ifs with h
        · simp
        · exact hbound ν z (by linarith [hN ν hν])⟩
  set R := ‖b n‖ + 1
  have hR_pos : (0 : ℝ) < R := by positivity
  obtain ⟨N, hN⟩ : ∃ N, ∀ ν ≥ N, 4 * R + 1 ≤ ‖b ν‖ := by
    rw [Filter.tendsto_atTop_atTop] at hb; exact hb (4 * R + 1)
  have heq : (fun z => ∑' ν, g ν z) =
      fun z => (∑ ν ∈ Finset.range N, g ν z) + (∑' m, g (m + N) z) := by
    ext z; exact ((hg_summ z).sum_add_tsum_nat_add N).symm
  rw [heq]
  apply AnalyticAt.add
  · have : (fun z => ∑ ν ∈ Finset.range N, g ν z) = ∑ ν ∈ Finset.range N, g ν := by
      ext z; simp [Finset.sum_apply]
    rw [this]
    apply Finset.analyticAt_sum
    intro ν _
    simp only [g]
    split_ifs with h
    · exact analyticAt_const
    · exact correctedTerm_analyticAt (P ν) (b ν) (p ν) (b n) (fun heq => h (hinj heq.symm))
  · apply DifferentiableOn.analyticAt
    · apply Complex.differentiableOn_tsum_of_summable_norm
          (U := Metric.ball (0 : ℂ) R) (u := fun m => (2⁻¹ : ℝ) ^ (m + N))
      · exact (summable_geometric_of_lt_one (by positivity) (by norm_num)).comp_injective
            (fun a b h => by omega)
      · intro m z hz
        rw [Metric.mem_ball, dist_zero_right] at hz
        simp only [g]
        split_ifs with h
        · exact differentiableWithinAt_const 0
        · apply DifferentiableAt.differentiableWithinAt
          apply AnalyticAt.differentiableAt
          apply correctedTerm_analyticAt
          intro heq'
          have h1 := hN (m + N) (Nat.le_add_left N m)
          rw [heq'] at hz; linarith [hR_pos]
      · exact Metric.isOpen_ball
      · intro m w hw
        rw [Metric.mem_ball, dist_zero_right] at hw
        simp only [g]
        split_ifs with h
        · simp
        · exact hbound (m + N) w (by linarith [hN (m + N) (Nat.le_add_left N m)])
    · exact Metric.isOpen_ball.mem_nhds
        (by rw [Metric.mem_ball, dist_zero_right]; linarith)

noncomputable def hFunc (b : ℕ → ℂ) (P : ℕ → Polynomial ℂ) (p : ℕ → Polynomial ℂ) (z : ℂ) : ℂ :=
  ∑' ν, (singularPart (P ν) (b ν) z - Polynomial.eval z (p ν))

theorem mittag_leffler
    (b : ℕ → ℂ) (P : ℕ → Polynomial ℂ)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop)
    (hP : ∀ n, HasNoConstantTerm (P n))
    (hinj : Function.Injective b) :
    ∃ h : ℂ → ℂ,
      Meromorphic h ∧
      (∀ n, HasSingularPartAt h (P n) (b n)) ∧
      (∀ f : ℂ → ℂ, (∀ n, HasSingularPartAt f (P n) (b n)) →
        (∀ z, z ∉ Set.range b → AnalyticAt ℂ f z) →
        ∀ z, AnalyticAt ℂ (fun w => f w - h w) z) := by
  obtain ⟨p, hbound⟩ := exists_correcting_polynomials b P hb hP
  refine ⟨hFunc b P p, ?_, ?_, ?_⟩
  ·
    intro z₀
    by_cases hz : ∀ n, z₀ ≠ b n
    ·
      exact (h_analyticAt_away b P p hbound hb z₀ hz).meromorphicAt
    ·
      push Not at hz
      obtain ⟨n, hn⟩ := hz
      subst hn

      have hsumm : ∀ z, Summable (fun ν => singularPart (P ν) (b ν) z -
          Polynomial.eval z (p ν)) :=
        summable_correctedTerms b P p hbound hb

      have h_nth_mero : MeromorphicAt (fun z => singularPart (P n) (b n) z -
          Polynomial.eval z (p n)) (b n) :=
        (singularPart_meromorphicAt (P n) (b n)).fun_sub
          (polynomial_eval_analyticAt (p n) (b n)).meromorphicAt

      have h_rest_anal : AnalyticAt ℂ (fun z => ∑' ν, (if ν = n then (0 : ℂ) else
          (singularPart (P ν) (b ν) z - Polynomial.eval z (p ν)))) (b n) :=
        remaining_tsum_analyticAt b P p hbound hb hinj n

      have h_split : ∀ z, hFunc b P p z =
          (singularPart (P n) (b n) z - Polynomial.eval z (p n)) +
          ∑' ν, (if ν = n then (0 : ℂ) else
            (singularPart (P ν) (b ν) z - Polynomial.eval z (p ν))) := by
        intro z
        unfold hFunc
        classical
        exact (hsumm z).tsum_eq_add_tsum_ite n

      have : MeromorphicAt (fun z =>
          (singularPart (P n) (b n) z - Polynomial.eval z (p n)) +
          ∑' ν, (if ν = n then (0 : ℂ) else
            (singularPart (P ν) (b ν) z - Polynomial.eval z (p ν)))) (b n) :=
        h_nth_mero.fun_add h_rest_anal.meromorphicAt
      exact this.congr (Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Set.univ, Filter.univ_mem' (fun _ => Set.mem_univ _),
          fun z _ => (h_split z).symm⟩)
  ·
    intro n
    unfold HasSingularPartAt

    have hsumm : ∀ z, Summable (fun ν => singularPart (P ν) (b ν) z -
        Polynomial.eval z (p ν)) :=
      summable_correctedTerms b P p hbound hb
    have h_rewrite : ∀ z, hFunc b P p z - singularPart (P n) (b n) z =
        -Polynomial.eval z (p n) +
        ∑' ν, (if ν = n then (0 : ℂ) else
          (singularPart (P ν) (b ν) z - Polynomial.eval z (p ν))) := by
      intro z
      unfold hFunc
      classical
      rw [(hsumm z).tsum_eq_add_tsum_ite n]
      ring
    have heq : (fun z => hFunc b P p z - singularPart (P n) (b n) z) =
        fun z => -Polynomial.eval z (p n) +
        ∑' ν, (if ν = n then (0 : ℂ) else
          (singularPart (P ν) (b ν) z - Polynomial.eval z (p ν))) := by
      ext z; exact h_rewrite z
    rw [heq]
    exact ((polynomial_eval_analyticAt (p n) (b n)).neg).add
      (remaining_tsum_analyticAt b P p hbound hb hinj n)
  ·

    intro f hf_sing hf_anal z₀
    by_cases hz : z₀ ∈ Set.range b
    ·
      obtain ⟨n, hn⟩ := hz
      subst hn

      have h_eq : (fun w => f w - hFunc b P p w) =
          fun w => (f w - singularPart (P n) (b n) w) -
                   (hFunc b P p w - singularPart (P n) (b n) w) := by
        ext w; ring
      rw [h_eq]
      exact (hf_sing n).sub
        (show AnalyticAt ℂ (fun w => hFunc b P p w - singularPart (P n) (b n) w) (b n) from by
          have hsumm : ∀ z, Summable (fun ν => singularPart (P ν) (b ν) z -
              Polynomial.eval z (p ν)) :=
            summable_correctedTerms b P p hbound hb
          have h_rewrite : (fun z => hFunc b P p z - singularPart (P n) (b n) z) =
              fun z => -Polynomial.eval z (p n) +
              ∑' ν, (if ν = n then (0 : ℂ) else
                (singularPart (P ν) (b ν) z - Polynomial.eval z (p ν))) := by
            ext z; unfold hFunc; classical
            rw [(hsumm z).tsum_eq_add_tsum_ite n]; ring
          rw [h_rewrite]
          exact ((polynomial_eval_analyticAt (p n) (b n)).neg).add
            (remaining_tsum_analyticAt b P p hbound hb hinj n))
    ·
      have h_anal : AnalyticAt ℂ (hFunc b P p) z₀ := by
        apply h_analyticAt_away b P p hbound hb z₀
        intro n hn
        exact hz ⟨n, hn.symm⟩
      exact (hf_anal z₀ hz).sub h_anal

end MittagLeffler
