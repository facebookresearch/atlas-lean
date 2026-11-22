/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_3
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open MeasureTheory Real ProbabilityTheory ENNReal Finset Set

noncomputable section

/-- Rewrite a set defined by an existential as a union: `{ω | ∃ i, P i ω}` equals
`⋃ i, {ω | P i ω}`. -/
lemma setOf_exists_eq_iUnion {α ι : Type*} {P : ι → α → Prop} :
    {ω | ∃ i, P i ω} = ⋃ i, {ω | P i ω} := by
  ext ω; simp [Set.mem_iUnion]

/-- The pointwise `sup'` over a finite nonempty index set of integrable functions
is integrable. -/
lemma integrable_sup' {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → Ω' → ℝ} (hf : ∀ i ∈ s, Integrable (f i) μ') :
    Integrable (fun ω => s.sup' hs (fun i => f i ω)) μ' := by
  induction s using Finset.cons_induction with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | cons a s has ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · simp [Finset.sup'_singleton]
      exact hf a (Finset.mem_cons_self a ∅)
    · have hsup_eq : (fun ω => (Finset.cons a s has).sup' hs (fun i => f i ω)) =
          (fun ω => f a ω ⊔ s.sup' hs' (fun i => f i ω)) :=
        funext (fun ω => Finset.sup'_cons hs' (fun i => f i ω))
      rw [hsup_eq]
      exact Integrable.sup (hf a (Finset.mem_cons_self a s))
        (ih hs' (fun i hi => hf i (Finset.mem_cons_of_mem hi)))

/-- If `X` is sub-Gaussian with parameter `σ²`, then so is `-X`. -/
lemma IsSubGaussian.neg {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} {σsq : ℝ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h : IsSubGaussian X σsq μ) :
    IsSubGaussian (fun ω => -X ω) σsq μ := by
  refine ⟨h.integrable.neg, ?_, ?_, ?_⟩
  · simp [integral_neg, h.mean_zero]
  · intro s
    have : (fun ω => exp (s * -X ω)) = (fun ω => exp ((-s) * X ω)) := by
      ext ω; ring_nf
    rw [this]; exact h.exp_integrable (-s)
  · intro s
    have : (fun ω => exp (s * -X ω)) = (fun ω => exp ((-s) * X ω)) := by
      ext ω; ring_nf
    rw [this]
    have hmgf := h.mgf_bound (-s)
    simp only [neg_sq] at hmgf
    exact hmgf

/-- Elementary inequality `e^{s|a|} ≤ e^{sa} + e^{-sa}`, used to handle the
absolute value in expectations involving the MGF. -/
lemma exp_abs_le_sum (s a : ℝ) :
    exp (s * |a|) ≤ exp (s * a) + exp (s * (-a)) := by
  rw [abs_eq_max_neg]
  rcases le_total a (-a) with h | h
  · rw [max_eq_right h]; linarith [exp_pos (s * a)]
  · rw [max_eq_left h]; linarith [exp_pos (s * (-a))]

/-- Theorem 1.14 (upper tail of the max): for `N` sub-Gaussian variables with
parameter `σ²`, `P(max_i X_i > t) ≤ N · exp(-t²/(2σ²))`. -/
theorem subGaussian_max_upper_tail_prob {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : ℕ} {X : Fin N → Ω → ℝ} {σsq : ℝ}
    (hX : ∀ i, IsSubGaussian (X i) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ i, X i ω > t} ≤ ENNReal.ofReal (↑N * exp (-(t ^ 2 / (2 * σsq)))) := by
  rw [setOf_exists_eq_iUnion]
  calc μ (⋃ i, {ω | X i ω > t})
      ≤ ∑' i, μ {ω | X i ω > t} := measure_iUnion_le _
    _ ≤ ∑' i : Fin N, ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) :=
        ENNReal.tsum_le_tsum (fun i => lemma_1_3_upper_tail (hX i) t ht)
    _ = N • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
        rw [tsum_eq_sum (fun i hi => (hi (Finset.mem_univ i)).elim)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    _ = ENNReal.ofReal (↑N * exp (-(t ^ 2 / (2 * σsq)))) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]


/-- Alias of `subGaussian_max_upper_tail_prob` with the textbook name. -/
alias theorem_1_14_upper_tail_prob := subGaussian_max_upper_tail_prob
/-- Alias of `subGaussian_max_upper_tail_prob` emphasising the maximal-inequality
flavour. -/
alias theorem_1_14_maximal_prob := subGaussian_max_upper_tail_prob

/-- Two-sided version of Theorem 1.14: `P(max_i |X_i| > t) ≤ 2N · exp(-t²/(2σ²))`. -/
theorem subGaussian_max_abs_tail_prob {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : ℕ} {X : Fin N → Ω → ℝ} {σsq : ℝ}
    (hX : ∀ i, IsSubGaussian (X i) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ i, |X i ω| > t} ≤ ENNReal.ofReal (2 * ↑N * exp (-(t ^ 2 / (2 * σsq)))) := by

  have h_subset : {ω | ∃ i, |X i ω| > t} ⊆
      {ω | ∃ i, X i ω > t} ∪ {ω | ∃ i, X i ω < -t} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    obtain ⟨i, hi⟩ := hω
    rcases le_or_gt (X i ω) 0 with h | h
    · right; exact ⟨i, by linarith [abs_of_nonpos h ▸ hi]⟩
    · left; exact ⟨i, by linarith [abs_of_pos h ▸ hi]⟩

  have h_upper : μ {ω | ∃ i, X i ω > t} ≤
      ENNReal.ofReal (↑N * exp (-(t ^ 2 / (2 * σsq)))) :=
    subGaussian_max_upper_tail_prob hX t ht

  have h_lower : μ {ω | ∃ i, X i ω < -t} ≤
      ENNReal.ofReal (↑N * exp (-(t ^ 2 / (2 * σsq)))) := by
    rw [setOf_exists_eq_iUnion]
    calc μ (⋃ i, {ω | X i ω < -t})
        ≤ ∑' i, μ {ω | X i ω < -t} := measure_iUnion_le _
      _ ≤ ∑' i : Fin N, ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) :=
          ENNReal.tsum_le_tsum (fun i => lemma_1_3_lower_tail (hX i) t ht)
      _ = N • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
          rw [tsum_eq_sum (fun i hi => (hi (Finset.mem_univ i)).elim)]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = ENNReal.ofReal (↑N * exp (-(t ^ 2 / (2 * σsq)))) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]

  calc μ {ω | ∃ i, |X i ω| > t}
      ≤ μ ({ω | ∃ i, X i ω > t} ∪ {ω | ∃ i, X i ω < -t}) := measure_mono h_subset
    _ ≤ μ {ω | ∃ i, X i ω > t} + μ {ω | ∃ i, X i ω < -t} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (↑N * exp (-(t ^ 2 / (2 * σsq)))) +
        ENNReal.ofReal (↑N * exp (-(t ^ 2 / (2 * σsq)))) := add_le_add h_upper h_lower
    _ = ENNReal.ofReal (2 * ↑N * exp (-(t ^ 2 / (2 * σsq)))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- Alias of `subGaussian_max_abs_tail_prob` with the textbook name. -/
alias theorem_1_14_abs_tail_prob := subGaussian_max_abs_tail_prob

/-- Parametric form of Theorem 1.14's expectation bound for the max: for any
`s > 0`, `E[max_i X_i] ≤ log N / s + σ² s / 2`. -/
theorem subGaussian_max_expectation_parametric {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N) {X : Fin N → Ω → ℝ} {σsq : ℝ} (hσ : 0 ≤ σsq)
    (hX : ∀ i, IsSubGaussian (X i) σsq μ)
    (s : ℝ) (hs : 0 < s) :
    have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    ∫ ω, (Finset.univ.sup' (Finset.univ_nonempty) (fun i => X i ω)) ∂μ ≤
      Real.log N / s + σsq * s / 2 := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set Z : Ω → ℝ := fun ω => Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) with hZ_def

  have hint_Z : Integrable Z μ :=
    integrable_sup' Finset.univ_nonempty (fun i _ => (hX i).integrable)

  have hint_exp : Integrable (fun ω => Real.exp (s * Z ω)) μ := by
    apply Integrable.mono' (integrable_finset_sum _ (fun i _ => (hX i).exp_integrable s))
      ((continuous_const.mul continuous_id').rexp.comp_aestronglyMeasurable
        hint_Z.aestronglyMeasurable)
    filter_upwards with ω
    rw [Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
    obtain ⟨j, _, hj_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => X i ω)
    show Real.exp (s * Finset.univ.sup' _ (fun i => X i ω)) ≤ _
    rw [hj_eq]
    exact Finset.single_le_sum (fun i _ => le_of_lt (Real.exp_pos (s * X i ω)))
      (Finset.mem_univ j)

  have hconv : ConvexOn ℝ Set.univ (fun x => Real.exp (s * x)) := by
    have h := convexOn_exp.comp_linearMap (s • LinearMap.id)
    simp only [Set.preimage_univ] at h
    exact h
  have hcont : ContinuousOn (fun x => Real.exp (s * x)) Set.univ :=
    (continuous_const.mul continuous_id').rexp.continuousOn
  have jensen : Real.exp (s * ∫ ω, Z ω ∂μ) ≤ ∫ ω, Real.exp (s * Z ω) ∂μ :=
    hconv.map_integral_le hcont isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hint_Z hint_exp

  have exp_bound : ∫ ω, Real.exp (s * Z ω) ∂μ ≤ ↑N * Real.exp (σsq * s ^ 2 / 2) := by
    calc ∫ ω, Real.exp (s * Z ω) ∂μ
        ≤ ∫ ω, ∑ i : Fin N, Real.exp (s * X i ω) ∂μ := by
          apply integral_mono hint_exp
            (integrable_finset_sum _ (fun i _ => (hX i).exp_integrable s))
          intro ω
          show Real.exp (s * Finset.univ.sup' _ (fun i => X i ω)) ≤ _
          obtain ⟨j, _, hj_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => X i ω)
          rw [hj_eq]
          exact Finset.single_le_sum (fun i _ => le_of_lt (Real.exp_pos (s * X i ω)))
            (Finset.mem_univ j)
      _ = ∑ i : Fin N, ∫ ω, Real.exp (s * X i ω) ∂μ :=
          integral_finset_sum _ (fun i _ => (hX i).exp_integrable s)
      _ ≤ ∑ _i : Fin N, Real.exp (σsq * s ^ 2 / 2) :=
          Finset.sum_le_sum (fun i _ => (hX i).mgf_bound s)
      _ = ↑N * Real.exp (σsq * s ^ 2 / 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

  have combined : Real.exp (s * ∫ ω, Z ω ∂μ) ≤ ↑N * Real.exp (σsq * s ^ 2 / 2) :=
    le_trans jensen exp_bound

  have hN' : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have log_bound : s * ∫ ω, Z ω ∂μ ≤ Real.log N + σsq * s ^ 2 / 2 := by
    have h1 := (Real.log_exp (s * ∫ ω, Z ω ∂μ)).symm
    have h2 := Real.log_le_log (Real.exp_pos _) combined
    have h3 : Real.log (↑N * Real.exp (σsq * s ^ 2 / 2)) =
        Real.log N + σsq * s ^ 2 / 2 := by
      rw [Real.log_mul (ne_of_gt hN') (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    linarith

  have h1 : ∫ ω, Z ω ∂μ ≤ (Real.log ↑N + σsq * s ^ 2 / 2) / s := by
    rw [le_div_iff₀ hs]; linarith [mul_comm (∫ ω, Z ω ∂μ) s]
  calc ∫ ω, Z ω ∂μ ≤ (Real.log ↑N + σsq * s ^ 2 / 2) / s := h1
    _ = Real.log ↑N / s + σsq * s / 2 := by field_simp

/-- Alias of `subGaussian_max_expectation_parametric` with the textbook name. -/
alias theorem_1_14_expectation_max_parametric := subGaussian_max_expectation_parametric

/-- Theorem 1.14 (expectation of the max): for `N ≥ 2` sub-Gaussian variables with
parameter `σ²`, `E[max_i X_i] ≤ σ √(2 log N)`. Obtained from the parametric form
by optimizing `s`. -/
theorem subGaussian_max_expectation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 2 ≤ N) {X : Fin N → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hX : ∀ i, IsSubGaussian (X i) (σ ^ 2) μ) :
    have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    ∫ ω, (Finset.univ.sup' (Finset.univ_nonempty) (fun i => X i ω)) ∂μ ≤
      σ * Real.sqrt (2 * Real.log N) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hN_pos : 0 < N := by omega
  have hN_real : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN_real
  have h2logN : 0 < 2 * Real.log (N : ℝ) := by linarith

  set s := Real.sqrt (2 * Real.log N) / σ
  have hs : 0 < s := div_pos (Real.sqrt_pos.mpr h2logN) hσ

  have param := subGaussian_max_expectation_parametric hN_pos (sq_nonneg σ) hX s hs

  suffices h : Real.log ↑N / s + σ ^ 2 * s / 2 = σ * Real.sqrt (2 * Real.log ↑N) by
    linarith

  have hsqrt_ne : Real.sqrt (2 * Real.log ↑N) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h2logN)
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hs_eq : s = Real.sqrt (2 * Real.log ↑N) / σ := rfl
  rw [hs_eq]
  field_simp
  have hsq : Real.sqrt (Real.log ↑N * 2) ^ 2 = Real.log ↑N * 2 :=
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ Real.log ↑N * 2)
  nlinarith [hsq]

/-- Parametric expectation bound for the max of absolute values:
`E[max_i |X_i|] ≤ log(2N) / s + σ² s / 2`. -/
theorem subGaussian_max_abs_expectation_parametric {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N) {X : Fin N → Ω → ℝ} {σsq : ℝ} (hσ : 0 ≤ σsq)
    (hX : ∀ i, IsSubGaussian (X i) σsq μ)
    (s : ℝ) (hs : 0 < s) :
    have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    ∫ ω, (Finset.univ.sup' (Finset.univ_nonempty) (fun i => |X i ω|)) ∂μ ≤
      Real.log (2 * N) / s + σsq * s / 2 := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set Z : Ω → ℝ := fun ω => Finset.univ.sup' Finset.univ_nonempty (fun i => |X i ω|) with hZ_def

  have hint_abs : ∀ i : Fin N, Integrable (fun ω => |X i ω|) μ :=
    fun i => (hX i).integrable.abs

  have hint_Z : Integrable Z μ :=
    integrable_sup' Finset.univ_nonempty (fun i _ => hint_abs i)

  have hint_exp_abs : ∀ i : Fin N, Integrable (fun ω => exp (s * |X i ω|)) μ := by
    intro i
    apply Integrable.mono'
      ((hX i).exp_integrable s |>.add ((hX i).neg.exp_integrable s))
      ((continuous_const.mul continuous_abs).rexp.comp_aestronglyMeasurable
        (hX i).integrable.aestronglyMeasurable)
    filter_upwards with ω
    simp only [Pi.add_apply, Pi.mul_apply,
               Real.norm_of_nonneg (le_of_lt (exp_pos _))]
    exact exp_abs_le_sum s (X i ω)

  have hint_exp : Integrable (fun ω => exp (s * Z ω)) μ := by
    apply Integrable.mono' (integrable_finset_sum _ (fun i _ => hint_exp_abs i))
      ((continuous_const.mul continuous_id').rexp.comp_aestronglyMeasurable
        hint_Z.aestronglyMeasurable)
    filter_upwards with ω
    rw [Real.norm_of_nonneg (le_of_lt (exp_pos _))]
    obtain ⟨j, _, hj_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => |X i ω|)
    show exp (s * Finset.univ.sup' _ (fun i => |X i ω|)) ≤ _
    rw [hj_eq]
    exact Finset.single_le_sum (fun i _ => le_of_lt (exp_pos (s * |X i ω|)))
      (Finset.mem_univ j)

  have hconv : ConvexOn ℝ Set.univ (fun x => exp (s * x)) := by
    have h := convexOn_exp.comp_linearMap (s • LinearMap.id)
    simp only [Set.preimage_univ] at h
    exact h
  have hcont : ContinuousOn (fun x => exp (s * x)) Set.univ :=
    (continuous_const.mul continuous_id').rexp.continuousOn
  have jensen : exp (s * ∫ ω, Z ω ∂μ) ≤ ∫ ω, exp (s * Z ω) ∂μ :=
    hconv.map_integral_le hcont isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hint_Z hint_exp

  have exp_bound : ∫ ω, exp (s * Z ω) ∂μ ≤ 2 * ↑N * exp (σsq * s ^ 2 / 2) := by
    calc ∫ ω, exp (s * Z ω) ∂μ
        ≤ ∫ ω, ∑ i : Fin N, exp (s * |X i ω|) ∂μ := by
          apply integral_mono hint_exp
            (integrable_finset_sum _ (fun i _ => hint_exp_abs i))
          intro ω
          show exp (s * Finset.univ.sup' _ (fun i => |X i ω|)) ≤ _
          obtain ⟨j, _, hj_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => |X i ω|)
          rw [hj_eq]
          exact Finset.single_le_sum (fun i _ => le_of_lt (exp_pos (s * |X i ω|)))
            (Finset.mem_univ j)
      _ ≤ ∫ ω, ∑ i : Fin N, (exp (s * X i ω) + exp (s * (-X i ω))) ∂μ := by
          apply integral_mono (integrable_finset_sum _ (fun i _ => hint_exp_abs i))
            (integrable_finset_sum _ (fun i _ =>
              ((hX i).exp_integrable s).add ((hX i).neg.exp_integrable s)))
          intro ω
          apply Finset.sum_le_sum
          intro i _
          exact exp_abs_le_sum s (X i ω)
      _ = ∑ i : Fin N, (∫ ω, exp (s * X i ω) ∂μ + ∫ ω, exp (s * (-X i ω)) ∂μ) := by
          simp_rw [← integral_add ((hX _).exp_integrable s) ((hX _).neg.exp_integrable s)]
          exact integral_finset_sum _ (fun i _ =>
            ((hX i).exp_integrable s).add ((hX i).neg.exp_integrable s))
      _ ≤ ∑ _i : Fin N, (exp (σsq * s ^ 2 / 2) + exp (σsq * s ^ 2 / 2)) := by
          apply Finset.sum_le_sum
          intro i _
          exact add_le_add ((hX i).mgf_bound s) ((hX i).neg.mgf_bound s)
      _ = 2 * ↑N * exp (σsq * s ^ 2 / 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

  have combined : exp (s * ∫ ω, Z ω ∂μ) ≤ 2 * ↑N * exp (σsq * s ^ 2 / 2) :=
    le_trans jensen exp_bound

  have h2N_pos : (0 : ℝ) < 2 * ↑N := by positivity
  have log_bound : s * ∫ ω, Z ω ∂μ ≤ Real.log (2 * N) + σsq * s ^ 2 / 2 := by
    have h1 := (Real.log_exp (s * ∫ ω, Z ω ∂μ)).symm
    have h2 := Real.log_le_log (exp_pos _) combined
    have h3 : Real.log (2 * ↑N * exp (σsq * s ^ 2 / 2)) =
        Real.log (2 * N) + σsq * s ^ 2 / 2 := by
      rw [Real.log_mul (ne_of_gt h2N_pos) (ne_of_gt (exp_pos _)), Real.log_exp]
    linarith

  have h1 : ∫ ω, Z ω ∂μ ≤ (Real.log (2 * ↑N) + σsq * s ^ 2 / 2) / s := by
    rw [le_div_iff₀ hs]; linarith [mul_comm (∫ ω, Z ω ∂μ) s]
  calc ∫ ω, Z ω ∂μ ≤ (Real.log (2 * ↑N) + σsq * s ^ 2 / 2) / s := h1
    _ = Real.log (2 * ↑N) / s + σsq * s / 2 := by field_simp

/-- Alias of `subGaussian_max_abs_expectation_parametric` with the textbook name. -/
alias theorem_1_14_expectation_abs_max_parametric := subGaussian_max_abs_expectation_parametric

/-- Expectation bound for the max of absolute values:
`E[max_i |X_i|] ≤ σ √(2 log(2N))`. -/
theorem subGaussian_max_abs_expectation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N) {X : Fin N → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hX : ∀ i, IsSubGaussian (X i) (σ ^ 2) μ) :
    have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    ∫ ω, (Finset.univ.sup' (Finset.univ_nonempty) (fun i => |X i ω|)) ∂μ ≤
      σ * Real.sqrt (2 * Real.log (2 * N)) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h2N_pos : (0 : ℝ) < 2 * ↑N := by positivity
  have h2N_gt1 : (1 : ℝ) < 2 * (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    linarith
  have hlog2N : 0 < Real.log (2 * (N : ℝ)) := Real.log_pos h2N_gt1
  have h2log2N : 0 < 2 * Real.log (2 * (N : ℝ)) := by linarith

  set s := Real.sqrt (2 * Real.log (2 * N)) / σ
  have hs : 0 < s := div_pos (Real.sqrt_pos.mpr h2log2N) hσ

  have param := subGaussian_max_abs_expectation_parametric hN (sq_nonneg σ) hX s hs

  suffices h : Real.log (2 * ↑N) / s + σ ^ 2 * s / 2 = σ * Real.sqrt (2 * Real.log (2 * ↑N)) by
    linarith

  have hsqrt_ne : Real.sqrt (2 * Real.log (2 * ↑N)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr h2log2N)
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hs_eq : s = Real.sqrt (2 * Real.log (2 * ↑N)) / σ := rfl
  rw [hs_eq]
  field_simp
  have hsq1 : Real.sqrt (Real.log (2 * ↑N) * 2) ^ 2 = Real.log (2 * ↑N) * 2 :=
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ Real.log (2 * ↑N) * 2)
  have hsq2 : Real.sqrt (2 * Real.log (2 * ↑N)) ^ 2 = 2 * Real.log (2 * ↑N) :=
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * Real.log (2 * ↑N))
  nlinarith [hsq1, hsq2]

/-- Theorem 1.14 in combined form: the four maximal inequalities for a family of
`N` sub-Gaussian variables — expectation and tail bounds for both the signed max
and the max of absolute values. -/
theorem subGaussian_maximal_inequality {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 2 ≤ N) {X : Fin N → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hX : ∀ i, IsSubGaussian (X i) (σ ^ 2) μ) :
    have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩

    (∫ ω, (Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)) ∂μ ≤
      σ * Real.sqrt (2 * Real.log N)) ∧

    (∀ t : ℝ, 0 < t →
      μ {ω | ∃ i, X i ω > t} ≤
        ENNReal.ofReal (↑N * exp (-(t ^ 2 / (2 * σ ^ 2))))) ∧

    (∫ ω, (Finset.univ.sup' Finset.univ_nonempty (fun i => |X i ω|)) ∂μ ≤
      σ * Real.sqrt (2 * Real.log (2 * N))) ∧

    (∀ t : ℝ, 0 < t →
      μ {ω | ∃ i, |X i ω| > t} ≤
        ENNReal.ofReal (2 * ↑N * exp (-(t ^ 2 / (2 * σ ^ 2))))) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hN_pos : 0 < N := by omega
  exact ⟨
    subGaussian_max_expectation hN hσ hX,
    fun t ht => subGaussian_max_upper_tail_prob hX t ht,
    subGaussian_max_abs_expectation hN_pos hσ hX,
    fun t ht => subGaussian_max_abs_tail_prob hX t ht⟩

end
