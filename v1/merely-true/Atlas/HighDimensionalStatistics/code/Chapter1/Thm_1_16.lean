/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_15
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_14

open MeasureTheory Real ProbabilityTheory ENNReal Finset Set

noncomputable section

namespace SubGaussianPolytope

/-- The event that some point of the convex hull of `S` exceeds `t` is contained in
the event that some vertex of `S` exceeds `t`. -/
lemma polytope_sup_subset_vertex_sup
    {Ω E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) (t : ℝ) :
    {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ⊆
    {ω | ∃ v ∈ S, g ω v > t} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  obtain ⟨θ, hθ_mem, hθ_gt⟩ := hω
  obtain ⟨v, hv_mem, hv_le⟩ := lemma_1_15_exists_vertex (g ω) S θ hθ_mem
  exact ⟨v, hv_mem, lt_of_lt_of_le hθ_gt hv_le⟩

/-- Rewrite a set defined by a bounded existential over a finset as a biUnion. -/
lemma setOf_bexists_eq_biUnion {Ω E : Type*} (S : Finset E) (P : E → Ω → Prop) :
    {ω | ∃ v ∈ S, P v ω} = ⋃ v ∈ (S : Set E), {ω | P v ω} := by
  ext ω; simp [Set.mem_iUnion]

/-- The `sup'` of a function over a finset equals the `sup'` over `Fin S.card`
obtained by reindexing via `S.equivFin`. -/
lemma sup'_equivFin_eq {E : Type*} (S : Finset E) (hS : S.Nonempty) (f : E → ℝ) :
    have : Nonempty (Fin S.card) := ⟨⟨0, Finset.card_pos.mpr hS⟩⟩
    S.sup' hS f = Finset.univ.sup' Finset.univ_nonempty
      (fun i => f (S.equivFin.symm i)) := by
  haveI : Nonempty (Fin S.card) := ⟨⟨0, Finset.card_pos.mpr hS⟩⟩
  apply le_antisymm
  · apply Finset.sup'_le
    intro v hv
    have hmem : S.equivFin ⟨v, hv⟩ ∈ Finset.univ := Finset.mem_univ _
    have h := Finset.le_sup' (fun i => f (↑(S.equivFin.symm i))) hmem
    simp only [Equiv.symm_apply_apply] at h
    exact h
  · apply Finset.sup'_le
    intro i _
    exact Finset.le_sup' f (S.equivFin.symm i).prop

/-- Tail bound for the sup over a polytope (vertex-indexed form, `nsmul`):
if each `ω ↦ g ω v` for `v ∈ S` is `σ²`-sub-Gaussian, then
`P(∃ θ ∈ conv(S), g ω θ > t) ≤ |S| · exp(-t²/(2σ²))`. -/
theorem tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) {σsq : ℝ}
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ≤
    S.card • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
  have h_subset := polytope_sup_subset_vertex_sup g S t
  calc μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t}
      ≤ μ {ω | ∃ v ∈ S, g ω v > t} := measure_mono h_subset
    _ = μ (⋃ v ∈ (S : Set E), {ω | g ω v > t}) := by
        congr 1; exact setOf_bexists_eq_biUnion S (fun v ω => g ω v > t)
    _ ≤ ∑' (v : ↥(S : Set E)), μ {ω | g ω (v : E) > t} :=
        measure_biUnion_le μ S.countable_toSet _
    _ ≤ ∑' (_ : ↥(S : Set E)), ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
        apply ENNReal.tsum_le_tsum
        intro ⟨v, hv⟩
        exact lemma_1_3_upper_tail (hsg v hv) t ht
    _ = S.card • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
        rw [tsum_eq_sum (s := Finset.univ) (fun i hi => (hi (Finset.mem_univ i)).elim)]
        simp [Finset.sum_const]

/-- Restatement of `tail_bound` with the right-hand side packaged as a single
`ENNReal.ofReal`. -/
theorem tail_bound'
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) {σsq : ℝ}
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ≤
    ENNReal.ofReal (S.card * exp (-(t ^ 2 / (2 * σsq)))) := by
  calc μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t}
      ≤ S.card • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) :=
        tail_bound g S hsg t ht
    _ = ENNReal.ofReal (S.card * exp (-(t ^ 2 / (2 * σsq)))) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]

/-- Parametric expectation bound for `sup_{v ∈ S} g(ω) v`: for any `s > 0`,
`E[max_v g ω v] ≤ log |S| / s + σ² s / 2`. -/
lemma expectation_sup_parametric
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) (hS : S.Nonempty) {σsq : ℝ} (hσ : 0 ≤ σsq)
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
    (s : ℝ) (hs : 0 < s) :
    ∫ ω, (S.sup' hS (fun v => g ω v)) ∂μ ≤
      Real.log S.card / s + σsq * s / 2 := by
  let e := S.equivFin
  let X : Fin S.card → Ω → ℝ := fun i ω => g ω (e.symm i)
  have hN : 0 < S.card := Finset.card_pos.mpr hS
  haveI : Nonempty (Fin S.card) := ⟨⟨0, hN⟩⟩
  have hX : ∀ i, IsSubGaussian (X i) σsq μ := by
    intro i; exact hsg (e.symm i) (by simp)
  have h14 := theorem_1_14_expectation_max_parametric hN hσ hX s hs
  suffices hsup : ∀ ω, S.sup' hS (fun v => g ω v) =
      Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) by
    simp_rw [hsup]; exact h14
  intro ω
  exact sup'_equivFin_eq S hS (fun v => g ω v)

/-- Expectation bound for the sup over the vertices of a polytope:
`E[max_{v ∈ S} g ω v] ≤ √σ² · √(2 log |S|)`. -/
theorem expectation_max_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) (hS : S.Nonempty) {σsq : ℝ} (hσ : 0 ≤ σsq)
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ) :
    ∫ ω, (S.sup' hS (fun v => g ω v)) ∂μ ≤
      Real.sqrt σsq * Real.sqrt (2 * Real.log S.card) := by
  by_cases hlog : Real.log (↑S.card : ℝ) ≤ 0
  · have hrhs : Real.sqrt (2 * Real.log ↑S.card) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [hrhs, mul_zero]
    have hcard_pos : 0 < S.card := Finset.card_pos.mpr hS
    have hge : (1 : ℝ) ≤ ↑S.card := by exact_mod_cast hcard_pos
    have hlog_nn : 0 ≤ Real.log (↑S.card : ℝ) := Real.log_nonneg hge
    have hlog_eq : Real.log (↑S.card : ℝ) = 0 := le_antisymm hlog hlog_nn
    have hcard_le : S.card ≤ 1 := by
      by_contra h
      push Not at h
      have : (1 : ℝ) < ↑S.card := by exact_mod_cast h
      linarith [Real.log_pos this]
    have hcard : S.card = 1 := le_antisymm hcard_le hcard_pos
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
    subst hv
    simp only [Finset.sup'_singleton]
    linarith [(hsg v (Finset.mem_singleton_self v)).mean_zero]
  · push Not at hlog
    by_cases hσ0 : σsq = 0
    · rw [hσ0, Real.sqrt_zero, zero_mul]
      by_contra hc
      push Not at hc
      set I := ∫ ω, S.sup' hS (fun v => g ω v) ∂μ
      set L := Real.log (↑S.card : ℝ)
      have hL_pos : 0 < L := hlog
      have hI_pos : 0 < I := hc
      have hL_ne : L ≠ 0 := ne_of_gt hL_pos
      have hI_ne : I ≠ 0 := ne_of_gt hI_pos
      have hs_pos : 0 < 2 * L / I := div_pos (by linarith) hI_pos
      have hparam := expectation_sup_parametric g S hS hσ hsg (2 * L / I) hs_pos
      rw [hσ0] at hparam
      simp only [zero_mul, zero_div, add_zero] at hparam
      have hsimp : L / (2 * L / I) = I / 2 := by field_simp
      linarith
    · have hσpos : 0 < σsq := lt_of_le_of_ne hσ (Ne.symm hσ0)
      set L := Real.log (↑S.card : ℝ) with hL_def
      set s₀ := Real.sqrt (2 * L / σsq) with hs₀_def
      have h2Lb : 0 < 2 * L / σsq := div_pos (by linarith) hσpos
      have hs₀_pos : 0 < s₀ := Real.sqrt_pos_of_pos h2Lb
      have hparam := expectation_sup_parametric g S hS hσ hsg s₀ hs₀_pos
      suffices hopt : L / s₀ + σsq * s₀ / 2 = Real.sqrt σsq * Real.sqrt (2 * L) by
        linarith
      have hs₀_sq : s₀ ^ 2 = 2 * L / σsq := Real.sq_sqrt (le_of_lt h2Lb)
      have hL_eq : L = σsq * s₀ ^ 2 / 2 := by field_simp at hs₀_sq ⊢; linarith
      have hterm : L / s₀ = σsq * s₀ / 2 := by rw [hL_eq]; field_simp
      have hsum : L / s₀ + σsq * s₀ / 2 = σsq * s₀ := by linarith
      have h2L_eq : 2 * L = σsq * s₀ ^ 2 := by linarith
      have hrhs : Real.sqrt σsq * Real.sqrt (2 * L) = σsq * s₀ := by
        rw [show 2 * L = σsq * s₀ ^ 2 from h2L_eq]
        rw [Real.sqrt_mul hσ, Real.sqrt_sq (le_of_lt hs₀_pos)]
        rw [← mul_assoc, Real.mul_self_sqrt hσ]
      linarith

/-- Parametric expectation bound for the sup of absolute values over the vertices:
for any `s > 0`, `E[max_v |g ω v|] ≤ log(2|S|) / s + σ² s / 2`. -/
lemma expectation_abs_sup_parametric
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) (hS : S.Nonempty) {σsq : ℝ} (hσ : 0 ≤ σsq)
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
    (s : ℝ) (hs : 0 < s) :
    ∫ ω, (S.sup' hS (fun v => |g ω v|)) ∂μ ≤
      Real.log (2 * S.card) / s + σsq * s / 2 := by
  let e := S.equivFin
  let X : Fin S.card → Ω → ℝ := fun i ω => g ω (e.symm i)
  have hN : 0 < S.card := Finset.card_pos.mpr hS
  haveI : Nonempty (Fin S.card) := ⟨⟨0, hN⟩⟩
  have hX : ∀ i, IsSubGaussian (X i) σsq μ := by
    intro i; exact hsg (e.symm i) (by simp)
  have h14 := theorem_1_14_expectation_abs_max_parametric hN hσ hX s hs
  suffices hsup : ∀ ω, S.sup' hS (fun v => |g ω v|) =
      Finset.univ.sup' Finset.univ_nonempty (fun i => |X i ω|) by
    simp_rw [hsup]; exact h14
  intro ω
  exact sup'_equivFin_eq S hS (fun v => |g ω v|)

/-- Expectation bound for the sup of absolute values over the vertices:
`E[max_{v ∈ S} |g ω v|] ≤ √σ² · √(2 log(2|S|))`. -/
theorem expectation_abs_max_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) (hS : S.Nonempty) {σsq : ℝ} (hσ : 0 ≤ σsq)
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ) :
    ∫ ω, (S.sup' hS (fun v => |g ω v|)) ∂μ ≤
      Real.sqrt σsq * Real.sqrt (2 * Real.log (2 * S.card)) := by
  have hN : 0 < S.card := Finset.card_pos.mpr hS
  by_cases hσ0 : σsq = 0
  · rw [hσ0, Real.sqrt_zero, zero_mul]
    by_contra hc
    push Not at hc
    set I := ∫ ω, S.sup' hS (fun v => |g ω v|) ∂μ
    set L := Real.log (2 * (↑S.card : ℝ))
    have hL_pos : 0 < L := by
      apply Real.log_pos
      exact_mod_cast (show 1 < 2 * S.card by omega)
    have hI_pos : 0 < I := hc
    have hL_ne : L ≠ 0 := ne_of_gt hL_pos
    have hI_ne : I ≠ 0 := ne_of_gt hI_pos
    have hs_pos : 0 < 2 * L / I := div_pos (by linarith) hI_pos
    have hparam := expectation_abs_sup_parametric g S hS hσ hsg (2 * L / I) hs_pos
    rw [hσ0] at hparam
    simp only [zero_mul, zero_div, add_zero] at hparam
    have hsimp : L / (2 * L / I) = I / 2 := by field_simp
    linarith
  · have hσpos : 0 < σsq := lt_of_le_of_ne hσ (Ne.symm hσ0)
    have h2N_pos : (1 : ℝ) < 2 * ↑S.card := by
      exact_mod_cast (show 1 < 2 * S.card by omega)
    have hlog2N : 0 < Real.log (2 * (S.card : ℝ)) := Real.log_pos h2N_pos
    set L := Real.log (2 * (S.card : ℝ)) with hL_def
    set s₀ := Real.sqrt (2 * L / σsq) with hs₀_def
    have h2Lb : 0 < 2 * L / σsq := div_pos (by linarith) hσpos
    have hs₀_pos : 0 < s₀ := Real.sqrt_pos_of_pos h2Lb
    have hparam := expectation_abs_sup_parametric g S hS hσ hsg s₀ hs₀_pos
    suffices hopt : L / s₀ + σsq * s₀ / 2 = Real.sqrt σsq * Real.sqrt (2 * L) by
      linarith
    have hs₀_sq : s₀ ^ 2 = 2 * L / σsq := Real.sq_sqrt (le_of_lt h2Lb)
    have hL_eq : L = σsq * s₀ ^ 2 / 2 := by field_simp at hs₀_sq ⊢; linarith
    have hterm : L / s₀ = σsq * s₀ / 2 := by rw [hL_eq]; field_simp
    have hsum : L / s₀ + σsq * s₀ / 2 = σsq * s₀ := by linarith
    have h2L_eq : 2 * L = σsq * s₀ ^ 2 := by linarith
    have hrhs : Real.sqrt σsq * Real.sqrt (2 * L) = σsq * s₀ := by
      rw [show 2 * L = σsq * s₀ ^ 2 from h2L_eq]
      rw [Real.sqrt_mul hσ, Real.sqrt_sq (le_of_lt hs₀_pos)]
      rw [← mul_assoc, Real.mul_self_sqrt hσ]
    linarith

/-- The event `{∃ θ ∈ conv(S), |g ω θ| > t}` is contained in `{∃ v ∈ S, |g ω v| > t}`. -/
lemma polytope_abs_sup_subset_vertex_abs_sup
    {Ω E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) (t : ℝ) :
    {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), |g ω θ| > t} ⊆
    {ω | ∃ v ∈ S, |g ω v| > t} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  obtain ⟨θ, hθ_mem, hθ_gt⟩ := hω

  rw [GT.gt, lt_abs] at hθ_gt
  rcases hθ_gt with hpos | hneg
  ·
    obtain ⟨v, hv_mem, hv_le⟩ := lemma_1_15_exists_vertex (g ω) S θ hθ_mem
    refine ⟨v, hv_mem, ?_⟩
    rw [GT.gt, lt_abs]
    left; linarith
  ·
    obtain ⟨v, hv_mem, hv_le⟩ := lemma_1_15_exists_vertex (-(g ω)) S θ hθ_mem
    simp only [LinearMap.neg_apply] at hv_le

    refine ⟨v, hv_mem, ?_⟩
    rw [GT.gt, lt_abs]
    right; linarith

/-- Two-sided tail bound over a polytope:
`P(∃ θ ∈ conv(S), |g ω θ| > t) ≤ 2 |S| · exp(-t²/(2σ²))`. -/
theorem abs_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) {σsq : ℝ}
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), |g ω θ| > t} ≤
    ENNReal.ofReal (2 * ↑S.card * exp (-(t ^ 2 / (2 * σsq)))) := by
  have h_subset := polytope_abs_sup_subset_vertex_abs_sup g S t
  have h_vertex : μ {ω | ∃ v ∈ S, |g ω v| > t} ≤
      ENNReal.ofReal (2 * ↑S.card * exp (-(t ^ 2 / (2 * σsq)))) := by

    let e := S.equivFin
    let X : Fin S.card → Ω → ℝ := fun i ω => g ω (e.symm i)
    have hX : ∀ i, IsSubGaussian (X i) σsq μ := by
      intro i; exact hsg (e.symm i) (by simp)
    have h14 := subGaussian_max_abs_tail_prob hX t ht

    suffices h_eq : {ω | ∃ v ∈ S, |g ω v| > t} ⊆
        {ω | ∃ i, |X i ω| > t} by
      exact le_trans (measure_mono h_eq) h14
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    obtain ⟨v, hv, hvt⟩ := hω
    exact ⟨e ⟨v, hv⟩, by
      show |g ω ↑(e.symm (e ⟨v, hv⟩))| > t
      have : (e.symm (e ⟨v, hv⟩) : E) = v :=
        congr_arg Subtype.val (Equiv.symm_apply_apply e ⟨v, hv⟩)
      rw [this]
      exact hvt⟩
  exact le_trans (measure_mono h_subset) h_vertex

/-- Theorem 1.16 (combined): for a polytope with vertex set `S` whose vertex
processes are `σ²`-sub-Gaussian, both the sup and the absolute-value sup of `g ω ·`
over `conv(S)` satisfy logarithmic expectation bounds and Gaussian tail bounds. -/
theorem theorem_1_16
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) (hS : S.Nonempty) {σsq : ℝ} (hσ : 0 ≤ σsq)
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    (∫ ω, (S.sup' hS (fun v => g ω v)) ∂μ ≤
      Real.sqrt σsq * Real.sqrt (2 * Real.log S.card)) ∧
    (∫ ω, (S.sup' hS (fun v => |g ω v|)) ∂μ ≤
      Real.sqrt σsq * Real.sqrt (2 * Real.log (2 * S.card))) ∧
    (μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ≤
      S.card • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq))))) ∧
    (μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), |g ω θ| > t} ≤
      ENNReal.ofReal (2 * ↑S.card * exp (-(t ^ 2 / (2 * σsq))))) :=
  ⟨expectation_max_bound g S hS hσ hsg,
   expectation_abs_max_bound g S hS hσ hsg,
   tail_bound g S hsg t ht,
   abs_tail_bound g S hsg t ht⟩

end SubGaussianPolytope

/-- Top-level export of the polytope tail bound (`nsmul` form). -/
theorem theorem_1_16_polytope_subgaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) {σsq : ℝ}
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ≤
    S.card • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) :=
  SubGaussianPolytope.tail_bound g S hsg t ht

/-- Top-level export of the polytope tail bound in `ENNReal.ofReal` form. -/
theorem theorem_1_16_polytope_subgaussian'
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) {σsq : ℝ}
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ≤
    ENNReal.ofReal (S.card * exp (-(t ^ 2 / (2 * σsq)))) :=
  SubGaussianPolytope.tail_bound' g S hsg t ht

/-- Top-level export of the expectation bound for the sup over polytope vertices. -/
theorem theorem_1_16_expectation_max
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) (hS : S.Nonempty) {σsq : ℝ} (hσ : 0 ≤ σsq)
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ) :
    ∫ ω, (S.sup' hS (fun v => g ω v)) ∂μ ≤
      Real.sqrt σsq * Real.sqrt (2 * Real.log S.card) :=
  SubGaussianPolytope.expectation_max_bound g S hS hσ hsg

/-- Top-level export of the expectation bound for the sup of absolute values
over polytope vertices. -/
theorem theorem_1_16_expectation_abs_max
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → (E →ₗ[ℝ] ℝ)) (S : Finset E) (hS : S.Nonempty) {σsq : ℝ} (hσ : 0 ≤ σsq)
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ) :
    ∫ ω, (S.sup' hS (fun v => |g ω v|)) ∂μ ≤
      Real.sqrt σsq * Real.sqrt (2 * Real.log (2 * S.card)) :=
  SubGaussianPolytope.expectation_abs_max_bound g S hS hσ hsg

end
