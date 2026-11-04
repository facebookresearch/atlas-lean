/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Independence.Integration
import Atlas.TheoryOfProbability.code.CenteredConvergence
set_option maxHeartbeats 8000000

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace KolmogorovThreeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

set_option maxHeartbeats 6400000 in
/-- The truncation `Yₙ = Xₙ · 1_{|Xₙ| ≤ A}` of the random variable `Xₙ` at threshold `A`,
i.e. `Yₙ(ω) = Xₙ(ω)` when `|Xₙ(ω)| ≤ A` and `0` otherwise. This is the key construction
in the Kolmogorov three-series theorem. -/
def truncatedRV (X : ℕ → Ω → ℝ) (A : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => X n ω * Set.indicator {ω | |X n ω| ≤ A} 1 ω

set_option linter.unusedSectionVars false in
/-- If the truncated variables have summable variances, then almost surely the partial sums
of the centered truncations converge: `∑ (Yᵢ - E[Yᵢ])` converges a.s. -/
theorem ae_tendsto_centered_of_indep_summableVar [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X μ) {A : ℝ} (hA : A > 0)
    (h3 : Summable fun n =>
      variance (fun ω => (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω) μ) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n =>
      ∑ i ∈ Finset.range n, (truncatedRV X A i ω -
        ∫ ω', (X i ω') * Set.indicator {ω' | |X i ω'| ≤ A} 1 ω' ∂μ)) atTop (nhds c) := by
  open Finset ENNReal in

  have hmeas_trunc : Measurable (fun x : ℝ => x * Set.indicator {x : ℝ | |x| ≤ A} 1 x) :=
    measurable_id.mul (Measurable.indicator measurable_one
      (measurableSet_le measurable_norm measurable_const))

  set m : ℕ → ℝ := fun n => ∫ ω', truncatedRV X A n ω' ∂μ
  set Z : ℕ → Ω → ℝ := fun n ω => truncatedRV X A n ω - m n

  have htrunc_norm : ∀ n ω, ‖truncatedRV X A n ω‖ ≤ A := by
    intro n ω; rw [Real.norm_eq_abs]; unfold truncatedRV
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs with h
    · simp only [mul_one]; exact h
    · simp only [mul_zero, abs_zero]; exact hA.le

  have hZ_sm : ∀ n, StronglyMeasurable (Z n) := fun n =>
    (((hX_meas n).mul (measurable_one.indicator
      (measurableSet_le (hX_meas n).norm measurable_const))).sub measurable_const).stronglyMeasurable

  have hZ_bdd : ∀ n ω, ‖Z n ω‖ ≤ 2 * A := by
    intro n ω
    have h1 : ‖truncatedRV X A n ω‖ ≤ A := htrunc_norm n ω
    have h2 : ‖m n‖ ≤ A :=
      calc ‖m n‖ = ‖∫ ω', truncatedRV X A n ω' ∂μ‖ := rfl
        _ ≤ ∫ ω', ‖truncatedRV X A n ω'‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ _, A ∂μ := integral_mono_of_nonneg (ae_of_all μ (fun _ => norm_nonneg _))
            (integrable_const A) (ae_of_all μ (fun ω' => htrunc_norm n ω'))
        _ = A := by simp
    calc ‖Z n ω‖ = ‖truncatedRV X A n ω - m n‖ := rfl
      _ ≤ ‖truncatedRV X A n ω‖ + ‖m n‖ := norm_sub_le _ _
      _ ≤ A + A := add_le_add h1 h2
      _ = 2 * A := by ring

  have hZ_int : ∀ n, Integrable (Z n) μ := fun n =>
    (memLp_top_of_bound (hZ_sm n).aestronglyMeasurable (2 * A)
      (ae_of_all μ (hZ_bdd n))).integrable le_top

  have hZ_mean : ∀ n, ∫ ω, Z n ω ∂μ = 0 := by
    intro n
    have hint : Integrable (truncatedRV X A n) μ :=
      (memLp_top_of_bound ((hX_meas n).mul (measurable_one.indicator
        (measurableSet_le (hX_meas n).norm measurable_const))).aestronglyMeasurable A
        (ae_of_all μ (htrunc_norm n))).integrable le_top
    simp only [Z, Pi.sub_apply]
    rw [integral_sub hint (integrable_const _)]
    simp [m]

  have hZ_indep : iIndepFun (m := fun _ => inferInstance) Z μ := by
    have heq : Z = fun n => (fun x => x * Set.indicator {y : ℝ | |y| ≤ A} 1 x - m n) ∘ (X n) := by
      ext n ω
      simp only [Z, truncatedRV, Function.comp, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [heq]
    exact hX_indep.comp _ (fun n => hmeas_trunc.sub measurable_const)

  have hZ_memLp : ∀ n, MemLp (Z n) 2 μ := fun n =>
    (memLp_top_of_bound (hZ_sm n).aestronglyMeasurable (2 * A)
      (ae_of_all μ (hZ_bdd n))).mono_exponent le_top

  have hVar_eq : ∀ n, variance (Z n) μ =
      variance (fun ω => (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω) μ := by
    intro n
    have hasm : AEStronglyMeasurable (truncatedRV X A n) μ :=
      ((hX_meas n).mul (measurable_one.indicator
        (measurableSet_le (hX_meas n).norm measurable_const))).aestronglyMeasurable
    show variance (fun ω => truncatedRV X A n ω - m n) μ = _
    have heq : (fun ω => truncatedRV X A n ω - m n) = (fun ω => truncatedRV X A n ω + (-(m n))) := by
      ext; ring
    rw [heq, variance_add_const hasm]

    rfl

  set C := ∑' n, variance (fun ω => (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω) μ
  have hC_nn : 0 ≤ C := tsum_nonneg (fun n => variance_nonneg _ _)
  have hR_bound : ∀ n, eLpNorm (fun ω => ∑ k ∈ range (n + 1), Z k ω) 1 μ ≤
      ENNReal.ofReal (Real.sqrt C) := by
    intro n

    have hS_sm : StronglyMeasurable (fun ω => ∑ k ∈ range (n + 1), Z k ω) := by
      have h := stronglyMeasurable_sum (range (n + 1)) (fun k _ => hZ_sm k)
      convert h using 1; ext ω; simp [Finset.sum_apply]
    have hS_memLp : MemLp (fun ω => ∑ k ∈ range (n + 1), Z k ω) 2 μ := by
      have hbdd : ∀ ω, ‖∑ k ∈ range (n + 1), Z k ω‖ ≤ (n + 1) * (2 * A) := by
        intro ω
        calc ‖∑ k ∈ range (n + 1), Z k ω‖ ≤ ∑ k ∈ range (n + 1), ‖Z k ω‖ := norm_sum_le _ _
          _ ≤ ∑ _ ∈ range (n + 1), (2 * A) := Finset.sum_le_sum (fun k _ => hZ_bdd k ω)
          _ = (n + 1) * (2 * A) := by simp [mul_comm]
      exact (memLp_top_of_bound hS_sm.aestronglyMeasurable
        ((n + 1) * (2 * A)) (ae_of_all μ hbdd)).mono_exponent le_top

    have h_int_bound : ∫ x, ‖(fun ω => ∑ k ∈ range (n + 1), Z k ω) x‖ ^ (2 : ℝ) ∂μ ≤ C := by

      have hconv : (fun x => ‖(fun ω => ∑ k ∈ range (n + 1), Z k ω) x‖ ^ (2 : ℝ)) =
          fun x => ((∑ k ∈ range (n + 1), Z k x)) ^ 2 := by
        ext x
        rw [show (2 : ℝ) = ↑(2 : ℕ) from by norm_num, Real.rpow_natCast, sq, sq,
            Real.norm_eq_abs, abs_mul_abs_self]
      rw [hconv]

      have hmean_sum : ∫ ω, (∑ k ∈ range (n + 1), Z k ω) ∂μ = 0 := by
        rw [integral_finset_sum _ (fun k _ => hZ_int k)]
        exact Finset.sum_eq_zero (fun k _ => hZ_mean k)
      have haem : AEMeasurable (fun ω => ∑ k ∈ range (n + 1), Z k ω) μ :=
        hS_sm.aestronglyMeasurable.aemeasurable
      rw [← variance_of_integral_eq_zero haem hmean_sum]

      have hpw : Set.Pairwise (↑(range (n + 1))) (fun i j => (Z i) ⟂ᵢ[μ] (Z j)) :=
        fun i _ j _ hij => hZ_indep.indepFun hij
      rw [show (fun ω => ∑ k ∈ range (n + 1), Z k ω) = ∑ k ∈ range (n + 1), Z k from by
        ext ω; simp [Finset.sum_apply]]
      rw [IndepFun.variance_sum (fun k _ => hZ_memLp k) hpw]

      calc ∑ k ∈ range (n + 1), variance (Z k) μ
          = ∑ k ∈ range (n + 1), variance (fun ω => (X k ω) * Set.indicator {ω | |X k ω| ≤ A} 1 ω) μ :=
            Finset.sum_congr rfl (fun k _ => hVar_eq k)
        _ ≤ C := h3.sum_le_tsum _ (fun k _ => variance_nonneg _ _)
    exact eLpNorm_one_le_sqrt_integral_sq hS_memLp h_int_bound

  have hR_nn : (0 : ℝ) ≤ Real.sqrt C := Real.sqrt_nonneg _
  set R : NNReal := ⟨Real.sqrt C, hR_nn⟩
  have hR_eq : (R : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt C) := by
    simp [R, ENNReal.ofReal_eq_coe_nnreal hR_nn]
  have hR_bdd : ∀ n, eLpNorm (fun ω => ∑ k ∈ range (n + 1), Z k ω) 1 μ ≤ ↑R := by
    intro n; rw [hR_eq]; exact hR_bound n

  have h := ae_tendsto_sum_of_indep_centered_L1bdd hZ_sm hZ_indep hZ_mean hZ_int hR_bdd

  filter_upwards [h] with ω ⟨c, hc⟩
  exact ⟨c, (Filter.tendsto_add_atTop_iff_nat 1).mp hc⟩


/-- If `∑ₙ P{|Xₙ| > A} < ∞`, then by the first Borel–Cantelli lemma, almost surely the
truncation eventually coincides with `Xₙ`. -/
theorem ae_eventually_truncation_eq [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {A : ℝ}
    (h1 : (∑' n, μ {ω | A < |X n ω|}) < ⊤) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, X n ω = truncatedRV X A n ω := by
  have h1' : (∑' n, μ {ω | A < |X n ω|}) ≠ ⊤ := h1.ne
  have hbc := ae_eventually_notMem h1'
  filter_upwards [hbc] with ω hω
  exact hω.mono fun n hn => by
    simp only [truncatedRV, Set.indicator_apply, Set.mem_setOf_eq]
    have hle : |X n ω| ≤ A := not_lt.mp hn
    simp [hle, mul_one]

/-- If two sequences `f, g` of random variables agree eventually (almost surely) and the
partial sums of `f` converge almost surely, then the partial sums of `g` also converge
almost surely (to a possibly different limit). -/
theorem ae_tendsto_of_ae_eventually_eq_and_ae_tendsto
    {f g : ℕ → Ω → ℝ}
    (hfg : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, f n ω = g n ω)
    (hf : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => f i ω)) atTop (nhds (S ω))) :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => g i ω)) atTop (nhds (S ω)) := by
  obtain ⟨Sf, hSf⟩ := hf

  have key : ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun n =>
      ∑ i ∈ Finset.range n, g i ω) atTop (nhds L) := by
    filter_upwards [hfg, hSf] with ω hev htend
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    set C := (∑ i ∈ Finset.range N, g i ω) - (∑ i ∈ Finset.range N, f i ω)
    refine ⟨C + Sf ω, ?_⟩

    have heq : ∀ n, N ≤ n →
        (∑ i ∈ Finset.range n, g i ω) = C + (∑ i ∈ Finset.range n, f i ω) := by
      intro n hn
      have : ∑ i ∈ Finset.Ico N n, g i ω = ∑ i ∈ Finset.Ico N n, f i ω := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hN i (Finset.mem_Ico.mp hi).1).symm
      rw [← Finset.sum_range_add_sum_Ico hn (f := fun i => g i ω),
          ← Finset.sum_range_add_sum_Ico hn (f := fun i => f i ω)]
      linarith
    exact (tendsto_const_nhds.add htend).congr'
      (eventually_atTop.mpr ⟨N, fun n hn => (heq n hn).symm⟩)

  classical
  exact ⟨fun ω => if h : ∃ L, Tendsto (fun n => ∑ i ∈ Finset.range n, g i ω)
      atTop (nhds L) then h.choose else 0,
    key.mono fun ω hω => by simp only; rw [dif_pos hω]; exact hω.choose_spec⟩

/-- If the means and variances of the truncations are summable then the partial sums of
the truncations `∑ Yᵢ` converge almost surely. This combines the centered convergence
result with the (deterministic) convergence of the mean series. -/
theorem ae_tendsto_truncated_of_conditions [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X μ) {A : ℝ} (hA : A > 0)
    (h2 : Summable fun n => ∫ ω, (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω ∂μ)
    (h3 : Summable fun n =>
      variance (fun ω => (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω) μ) :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => truncatedRV X A i ω)) atTop (nhds (S ω)) := by
  set m : ℕ → ℝ := fun n => ∫ ω, (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω ∂μ
  have h_mean_conv : Tendsto (fun n => ∑ i ∈ Finset.range n, m i) atTop
      (nhds (∑' i, m i)) := h2.hasSum.tendsto_sum_nat


  have h_centered : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n =>
      ∑ i ∈ Finset.range n, (truncatedRV X A i ω - m i)) atTop (nhds c) :=
    ae_tendsto_centered_of_indep_summableVar hX_meas hX_indep hA h3

  have key : ∀ᵐ ω ∂μ, ∃ L, Tendsto (fun n =>
      ∑ i ∈ Finset.range n, truncatedRV X A i ω) atTop (nhds L) := by
    filter_upwards [h_centered] with ω ⟨c, hc⟩
    refine ⟨c + ∑' i, m i, ?_⟩
    have heq : ∀ n, ∑ i ∈ Finset.range n, truncatedRV X A i ω =
        (∑ i ∈ Finset.range n, (truncatedRV X A i ω - m i)) +
        (∑ i ∈ Finset.range n, m i) := by
      intro n
      simp only [Finset.sum_sub_distrib]
      ring
    exact (hc.add h_mean_conv).congr (fun n => (heq n).symm)
  classical
  exact ⟨fun ω => if h : ∃ L, Tendsto (fun n => ∑ i ∈ Finset.range n,
      truncatedRV X A i ω) atTop (nhds L) then h.choose else 0,
    key.mono fun ω hω => by simp only; rw [dif_pos hω]; exact hω.choose_spec⟩

/-- `truncatedRV` factors as the composition of `Xₙ` with the deterministic truncation
function `x ↦ x · 1_{|x| ≤ A}`. -/
lemma truncatedRV_eq_comp (X : ℕ → Ω → ℝ) (A : ℝ) (n : ℕ) :
    truncatedRV X A n = (fun x => x * Set.indicator {x : ℝ | |x| ≤ A} 1 x) ∘ (X n) := by
  ext ω
  simp only [truncatedRV, Function.comp, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]

set_option linter.unusedSectionVars false in
/-- The deterministic truncation function `x ↦ x · 1_{|x| ≤ A}` is measurable. -/
lemma measurable_truncation_fun (A : ℝ) :
    Measurable (fun x : ℝ => x * Set.indicator {x : ℝ | |x| ≤ A} 1 x) :=
  measurable_id.mul (Measurable.indicator measurable_one
    (measurableSet_le measurable_norm measurable_const))

/-- If `(Xₙ)` is an independent family then so is `(truncatedRV X A n)`, since truncation
is a measurable function applied componentwise. -/
lemma iIndepFun_truncatedRV {X : ℕ → Ω → ℝ} (hX_indep : iIndepFun X μ) (A : ℝ) :
    iIndepFun (fun n => truncatedRV X A n) μ := by
  have heq : (fun n => truncatedRV X A n) = fun n =>
      (fun x => x * Set.indicator {x : ℝ | |x| ≤ A} 1 x) ∘ X n := by
    funext n; exact truncatedRV_eq_comp X A n
  rw [heq]
  exact hX_indep.comp _ (fun _ => measurable_truncation_fun A)

/-- The truncated random variable is bounded by `A` in absolute value. -/
lemma abs_truncatedRV_le {X : ℕ → Ω → ℝ} {A : ℝ} (hA : A ≥ 0) (n : ℕ) (ω : Ω) :
    |truncatedRV X A n ω| ≤ A := by
  unfold truncatedRV
  simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
  split_ifs with h
  · simp only [mul_one]; exact h
  · simp only [mul_zero, abs_zero]; exact hA

set_option linter.unusedSectionVars false in
/-- If `|Yₙ| ≤ A` everywhere, then truncation at level `A` is the identity, i.e.
`Yₙ · 1_{|Yₙ| ≤ A} = Yₙ`. -/
lemma truncated_indicator_eq_of_bdd
    {Y : ℕ → Ω → ℝ} {A : ℝ} (hY_bdd : ∀ n ω, |Y n ω| ≤ A) (n : ℕ) :
    (fun ω => (Y n ω) * Set.indicator {ω | |Y n ω| ≤ A} 1 ω) = Y n := by
  ext ω
  have h : ω ∈ {ω' : Ω | |Y n ω'| ≤ A} := hY_bdd n ω
  simp [Set.indicator_of_mem h]

set_option linter.unusedSectionVars false in
/-- If `|Yₙ| ≤ A` everywhere, then `truncatedRV Y A n = Yₙ`. -/
lemma truncatedRV_eq_of_bdd
    {Y : ℕ → Ω → ℝ} {A : ℝ} (hY_bdd : ∀ n ω, |Y n ω| ≤ A) (n : ℕ) :
    truncatedRV Y A n = Y n := by
  ext ω
  simp only [truncatedRV]
  have h : ω ∈ {ω' : Ω | |Y n ω'| ≤ A} := hY_bdd n ω
  simp [Set.indicator_of_mem h]

set_option maxHeartbeats 800000 in
/-- If `(Yₙ)` is uniformly bounded by `A` and its partial sums converge a.s., then so do the
partial sums of `truncatedRV Y A n` (in fact to the same limit). -/
lemma ae_tendsto_truncatedRV_of_bdd
    {Y : ℕ → Ω → ℝ} {A : ℝ} (hY_bdd : ∀ n ω, |Y n ω| ≤ A)
    (hY_tend : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => Y i ω)) atTop (nhds (S ω))) :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => truncatedRV Y A i ω)) atTop (nhds (S ω)) := by
  obtain ⟨S, hS⟩ := hY_tend
  refine ⟨S, hS.mono fun ω hω => ?_⟩
  have heq : (fun n => (Finset.range n).sum (fun i => truncatedRV Y A i ω)) =
      (fun n => (Finset.range n).sum (fun i => Y i ω)) := by
    ext n
    exact Finset.sum_congr rfl (fun i _ => congr_fun (truncatedRV_eq_of_bdd hY_bdd i) ω)
  rw [heq]
  exact hω




/-- If the partial sums of an independent sequence `Xₙ` converge almost surely, then for
every `A > 0` the tail probabilities `∑ₙ P(|Xₙ| > A)` are finite. Uses the second
Borel–Cantelli lemma together with the fact that almost-sure convergence forces `Xₙ → 0`. -/
theorem summable_tail_prob_of_ae_tendsto [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X μ) {A : ℝ} (hA : A > 0)
    (hX_tend : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => X i ω)) atTop (nhds (S ω))) :
    (∑' n, μ {ω | A < |X n ω|}) < ⊤ := by

  by_contra h_not_fin
  push Not at h_not_fin
  have h_infty : (∑' n, μ {ω | A < |X n ω|}) = ⊤ := top_le_iff.mp h_not_fin

  have h_meas : ∀ n, MeasurableSet {ω | A < |X n ω|} := fun n =>
    measurableSet_lt measurable_const (hX_meas n).norm

  have h_indep : iIndepSet (fun n => {ω | A < |X n ω|}) μ := by
    rw [iIndepSet_iff_meas_biInter h_meas]
    intro S
    have h_eq : ∀ n, {ω : Ω | A < |X n ω|} = X n ⁻¹' {x : ℝ | A < |x|} := by
      intro n; ext ω; simp
    simp_rw [h_eq]
    exact hX_indep.measure_inter_preimage_eq_mul S
      (fun _ _ => measurableSet_lt measurable_const measurable_norm)

  have h_limsup : μ (limsup (fun n => {ω | A < |X n ω|}) atTop) = 1 :=
    measure_limsup_eq_one h_meas h_indep h_infty

  obtain ⟨S, hS⟩ := hX_tend
  have h_term_zero : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (nhds 0) := by
    filter_upwards [hS] with ω hω
    have h1 : Tendsto (fun n => (∑ i ∈ Finset.range (n + 1), X i ω) -
        ∑ i ∈ Finset.range n, X i ω) atTop (nhds (S ω - S ω)) :=
      (hω.comp (tendsto_add_atTop_nat 1)).sub hω
    simp only [Finset.sum_range_succ_sub_sum, sub_self] at h1
    exact h1
  have h_ev_not_mem : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ {ω' | A < |X n ω'|} := by
    filter_upwards [h_term_zero] with ω hω
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hω) A hA
    exact eventually_atTop.mpr ⟨N, fun n hn => by
      simp only [not_lt]
      have hd := hN n hn
      rw [Real.dist_eq, sub_zero] at hd
      exact le_of_lt hd⟩
  have h_ae_not_limsup : ∀ᵐ ω ∂μ, ω ∉ limsup (fun n => {ω | A < |X n ω|}) atTop := by
    filter_upwards [h_ev_not_mem] with ω hω
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.mem_iInter, Set.mem_iUnion,
      not_forall, not_exists]
    obtain ⟨N, hN⟩ := eventually_atTop.mp hω
    exact ⟨N, fun n hn => hN n (by omega)⟩
  have h_freq_zero : μ (limsup (fun n => {ω | A < |X n ω|}) atTop) = 0 := by
    rw [ae_iff] at h_ae_not_limsup
    simp only [not_not] at h_ae_not_limsup
    exact h_ae_not_limsup

  rw [h_freq_zero] at h_limsup
  exact absurd h_limsup (by norm_num)

end KolmogorovThreeSeries

open KolmogorovThreeSeries

