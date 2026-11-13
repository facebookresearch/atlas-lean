/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_2
import Atlas.HighDimensionalStatistics.code.Chapter2.Lemma_2_7
import Atlas.HighDimensionalStatistics.code.Chapter2.EpsilonNetBridge
import Mathlib

open Matrix Finset BigOperators

/-- Expansion of the squared dot product of a difference:
$\langle a - b, a - b \rangle = \langle a, a \rangle - 2 \langle a, b \rangle + \langle b, b \rangle$. -/
lemma dotProduct_sub_self {m : Type*} [Fintype m] (a b : m → ℝ) :
    dotProduct (a - b) (a - b) = dotProduct a a - 2 * dotProduct a b + dotProduct b b := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm b a]
  ring

/-- Mean-squared-error rescaling step in the proof of Corollary 2.8 / Theorem 2.6.
If the prediction error is bounded by `4·8·σ² · L`, then dividing by `n` yields the
MSE bound `32·σ²/n · L`, where `L = 2k·log(e·d/(2k)) + 2k·log 6 + log(1/δ)`. -/
theorem cor_2_8_mse_bound
    (n d k : ℕ) (hn : 0 < (n : ℝ)) (_hk : 1 ≤ k) (_hkd : 2 * k ≤ d)
    (σsq δ : ℝ) (_hσ : 0 < σsq) (_hδ : 0 < δ)
    (sq_pred_err : ℝ)

    (hbound : sq_pred_err ≤
      4 * (8 * σsq * (2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k))
        + 2 * ↑k * Real.log 6 + Real.log (1 / δ)))) :
    sq_pred_err / ↑n ≤
      32 * σsq / ↑n * (2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k))
        + 2 * ↑k * Real.log 6 + Real.log (1 / δ)) := by

  set L := 2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k)) +
        2 * ↑k * Real.log 6 + Real.log (1 / δ)

  have h1 : 4 * (8 * σsq * L) = 32 * σsq * L := by ring
  rw [h1] at hbound

  have h2 : 32 * σsq / ↑n * L = 32 * σsq * L / ↑n := by ring
  rw [h2]

  exact div_le_div_of_nonneg_right hbound hn.le

/-- If `L ≥ log(M/δ)`, then `M · exp(-L) ≤ δ`. Used to bound tail probabilities
after applying a Chernoff-type inequality. -/
lemma mul_exp_neg_le_of_ge_log {M δ L : ℝ} (hM : 0 < M) (hδ : 0 < δ)
    (hL : L ≥ Real.log (M / δ)) : M * Real.exp (-L) ≤ δ := by
  have hMd : M / δ > 0 := div_pos hM hδ
  have h1 : Real.exp L ≥ M / δ :=
    calc Real.exp L ≥ Real.exp (Real.log (M / δ)) := Real.exp_le_exp_of_le hL
      _ = M / δ := Real.exp_log hMd
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos L)]
  calc M = (M / δ) * δ := by field_simp
    _ ≤ Real.exp L * δ := mul_le_mul_of_nonneg_right h1 hδ.le
    _ = δ * Real.exp L := mul_comm _ _

/-- The union-bound tail estimate `C(d, 2k) · 6^(2k) · exp(-L) ≤ δ`, where
`L = 2k·log(e·d/(2k)) + 2k·log 6 + log(1/δ)`. This collects the deterministic
upper bound on `log C(d, 2k)` from Lemma 2.7 with the explicit constants. -/
lemma tail_rhs_le_delta (d k : ℕ) (δ : ℝ)
    (hk : 1 ≤ k) (hkd : 2 * k ≤ d) (hδ_pos : 0 < δ) :
    (d.choose (2 * k) : ℝ) * (6 : ℝ) ^ (2 * k) *
      Real.exp (-(2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k)) +
                   2 * ↑k * Real.log 6 + Real.log (1 / δ))) ≤ δ := by
  have hC_pos : (0 : ℝ) < (d.choose (2 * k) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have h6_pos : (0 : ℝ) < (6 : ℝ) ^ (2 * k) := by positivity
  have hM_pos : (0 : ℝ) < (d.choose (2 * k) : ℝ) * (6 : ℝ) ^ (2 * k) :=
    mul_pos hC_pos h6_pos
  apply mul_exp_neg_le_of_ge_log hM_pos hδ_pos


  have hlog_decomp : Real.log ((d.choose (2 * k) : ℝ) * (6 : ℝ) ^ (2 * k) / δ) =
      Real.log (d.choose (2 * k) : ℝ) + Real.log ((6 : ℝ) ^ (2 * k)) + Real.log (1 / δ) := by
    rw [show (d.choose (2 * k) : ℝ) * (6 : ℝ) ^ (2 * k) / δ =
        ((d.choose (2 * k) : ℝ) * (6 : ℝ) ^ (2 * k)) * (1 / δ) from by field_simp]
    rw [Real.log_mul (ne_of_gt hM_pos)
        (ne_of_gt (show (0 : ℝ) < 1 / δ from by positivity))]
    rw [Real.log_mul (ne_of_gt hC_pos) (ne_of_gt h6_pos)]
  rw [hlog_decomp]

  rw [Real.log_pow]

  have h_log_C : Real.log (d.choose (2 * k) : ℝ) ≤
      ↑(2 * k) * Real.log (Real.exp 1 * ↑d / (2 * ↑k)) := by
    have h2k : 1 ≤ 2 * k := by omega
    have hbound := lemma_2_7_binom_bound d (2 * k) h2k hkd
    calc Real.log ↑(d.choose (2 * k))
        ≤ Real.log ((Real.exp 1 * ↑d / ↑(2 * k)) ^ (2 * k)) :=
          Real.log_le_log hC_pos hbound
      _ = ↑(2 * k) * Real.log (Real.exp 1 * ↑d / ↑(2 * k)) := Real.log_pow _ _
      _ = ↑(2 * k) * Real.log (Real.exp 1 * ↑d / (2 * ↑k)) := by
          congr 1; congr 1; push_cast; ring

  push_cast at h_log_C ⊢
  linarith

/-- The complexity term `L = 2k·log(e·d/(2k)) + 2k·log 6 + log(1/δ)` is strictly
positive under `1 ≤ k`, `2k ≤ d`, and `0 < δ ≤ 1`. -/
lemma L_pos (k d : ℕ) (δ : ℝ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    0 < 2 * (↑k : ℝ) * Real.log (Real.exp 1 * ↑d / (2 * ↑k)) +
        2 * ↑k * Real.log 6 + Real.log (1 / δ) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have h2k_pos : (0 : ℝ) < 2 * ↑k := by positivity
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num : (1 : ℝ) < 6)
  have h_term2 : 0 < 2 * (↑k : ℝ) * Real.log 6 := mul_pos h2k_pos hlog6
  have h_term3 : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hδ_pos]; linarith
  have h_ed_bound : (1 : ℝ) ≤ Real.exp 1 * ↑d / (2 * ↑k) := by
    rw [le_div_iff₀ h2k_pos]
    have hd_ge : (2 * ↑k : ℝ) ≤ ↑d := by exact_mod_cast hkd
    calc 1 * (2 * (↑k : ℝ)) = 2 * ↑k := one_mul _
      _ ≤ (↑d : ℝ) := hd_ge
      _ ≤ Real.exp 1 * ↑d := le_mul_of_one_le_left (by positivity)
          (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1))
  have h_term1 : 0 ≤ 2 * (↑k : ℝ) * Real.log (Real.exp 1 * ↑d / (2 * ↑k)) :=
    mul_nonneg h2k_pos.le (Real.log_nonneg h_ed_bound)
  linarith

/-- Convert a tail bound `μ{f > b} ≤ δ` into a high-probability lower bound
`μ{f ≤ b} ≥ 1 - δ` for a probability measure `μ`. -/
lemma prob_good_of_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {f : Ω → ℝ} {b δ : ℝ} (hδ_pos : 0 < δ)
    (htail : μ {ω | f ω > b} ≤ ENNReal.ofReal δ) :
    μ {ω | f ω ≤ b} ≥ ENNReal.ofReal (1 - δ) := by
  have hcompl : {ω | f ω ≤ b} = {ω | f ω > b}ᶜ := by
    ext ω; simp [not_lt]
  rw [hcompl]
  have h_compl_ge : μ ({ω | f ω > b}ᶜ) ≥ 1 - μ {ω | f ω > b} := by
    have h1 : 1 ≤ μ {ω | f ω > b} + μ {ω | f ω > b}ᶜ := by
      calc (1 : ENNReal) = μ Set.univ := (MeasureTheory.measure_univ).symm
        _ = μ ({ω | f ω > b} ∪ {ω | f ω > b}ᶜ) := by rw [Set.union_compl_self]
        _ ≤ μ {ω | f ω > b} + μ {ω | f ω > b}ᶜ := MeasureTheory.measure_union_le _ _
    exact tsub_le_iff_right.mpr (by rwa [add_comm])
  calc μ ({ω | f ω > b}ᶜ) ≥ 1 - μ {ω | f ω > b} := h_compl_ge
    _ ≥ 1 - ENNReal.ofReal δ := tsub_le_tsub_left htail 1
    _ = ENNReal.ofReal (1 - δ) := by
        rw [ENNReal.ofReal_sub 1 hδ_pos.le]; simp

/-- Extract integrability of `exp(s · ⟨ε, v⟩)` from the sub-Gaussian MGF
assumption on the noise vector `ε`. -/
theorem exp_dotProduct_integrable_of_subG
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {n : ℕ} {ε : Ω → Fin n → ℝ} {σ : ℝ} (_hσ : 0 < σ)
    (hsubG : ∀ (v : Fin n → ℝ),
      dotProduct v v ≤ 1 →
      ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ ∧
        ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
        Real.exp (s ^ 2 * σ ^ 2 / 2))
    (v : Fin n → ℝ) (hv : dotProduct v v ≤ 1) (s : ℝ) :
    MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ :=
  (hsubG v hv s).1

/-- One-sided Chernoff tail bound for a sub-Gaussian linear functional of `ε`:
$\mu\{\omega : \langle \varepsilon(\omega), v\rangle > t'\} \le \exp(-t'^2 / (2\sigma^2))$
for any unit direction `v` with $\langle v, v\rangle \le 1$. -/
theorem chernoff_tail_from_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {n : ℕ} {ε : Ω → Fin n → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hsubG : ∀ (v : Fin n → ℝ),
      dotProduct v v ≤ 1 →
      ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ ∧
        ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
        Real.exp (s ^ 2 * σ ^ 2 / 2))
    (v : Fin n → ℝ) (hv : dotProduct v v ≤ 1)
    (t' : ℝ) (ht' : 0 < t') :
    μ {ω | dotProduct (ε ω) v > t'} ≤
      ENNReal.ofReal (Real.exp (-(t' ^ 2 / (2 * σ ^ 2)))) := by

  set X : Ω → ℝ := fun ω => dotProduct (ε ω) v with hX_def

  have hmgf : ∀ s : ℝ, ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * σ ^ 2 / 2) :=
    fun s => (hsubG v hv s).2

  set s₀ := t' / σ ^ 2 with hs₀_def
  have hs₀_pos : 0 < s₀ := div_pos ht' (sq_pos_of_pos hσ)

  have h_int : MeasureTheory.Integrable (fun ω => Real.exp (s₀ * X ω)) μ :=
    exp_dotProduct_integrable_of_subG hσ hsubG v hv s₀


  have hchernoff := ProbabilityTheory.measure_ge_le_exp_mul_mgf t' hs₀_pos.le h_int

  have h_mgf_bound : ProbabilityTheory.mgf X μ s₀ ≤ Real.exp (s₀ ^ 2 * σ ^ 2 / 2) := hmgf s₀

  have h_bound : μ.real {ω | t' ≤ X ω} ≤ Real.exp (-(t' ^ 2 / (2 * σ ^ 2))) := by
    calc μ.real {ω | t' ≤ X ω}
        ≤ Real.exp (-s₀ * t') * ProbabilityTheory.mgf X μ s₀ := hchernoff
      _ ≤ Real.exp (-s₀ * t') * Real.exp (s₀ ^ 2 * σ ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h_mgf_bound (Real.exp_pos _).le
      _ = Real.exp (-s₀ * t' + s₀ ^ 2 * σ ^ 2 / 2) := (Real.exp_add _ _).symm
      _ = Real.exp (-(t' ^ 2 / (2 * σ ^ 2))) := by
          congr 1; rw [hs₀_def]
          have hσ2_ne : σ ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hσ)
          field_simp; ring

  have h_subset : {ω | X ω > t'} ⊆ {ω | t' ≤ X ω} := by
    intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; linarith
  calc μ {ω | dotProduct (ε ω) v > t'}
      = μ {ω | X ω > t'} := by rfl
    _ ≤ μ {ω | t' ≤ X ω} := MeasureTheory.measure_mono h_subset
    _ = ENNReal.ofReal (μ.real {ω | t' ≤ X ω}) := by
        symm; exact MeasureTheory.ofReal_measureReal (by finiteness)
    _ ≤ ENNReal.ofReal (Real.exp (-(t' ^ 2 / (2 * σ ^ 2)))) :=
        ENNReal.ofReal_le_ofReal h_bound

/-- Existence of a `1/4`-net (in dot-product norm) of cardinality at most `6^|B|`
for the unit ball of the subspace spanned by `B ⊆ Fin n → ℝ`. The net `N` lies in
the span of `B` and every unit vector in span(B) is within `1/4` (in squared
distance) of some element of `N`. -/
theorem epsilon_net_covering_number {n : ℕ}
    (B : Finset (Fin n → ℝ)) :
    ∃ (N : Finset (Fin n → ℝ)),
      N.card ≤ 6 ^ B.card ∧
      (∀ z ∈ N, dotProduct z z ≤ 1) ∧
      (∀ z ∈ N, z ∈ Submodule.span ℝ (B : Set (Fin n → ℝ))) ∧
      (∀ v, dotProduct v v ≤ 1 → v ∈ Submodule.span ℝ (B : Set (Fin n → ℝ)) →
        ∃ z ∈ N, dotProduct (v - z) (v - z) ≤ 1/4) := by
  by_cases hB : B.card = 0
  · refine ⟨{0}, ?_, ?_, ?_, ?_⟩
    · simp [hB]
    · intro z hz; simp at hz; subst hz; simp [dotProduct]
    · intro z hz; simp at hz; subst hz; exact Submodule.zero_mem _
    · intro v _ hv_span
      have hB_empty : B = ∅ := Finset.card_eq_zero.mp hB
      have hspan_bot : Submodule.span ℝ (B : Set (Fin n → ℝ)) = ⊥ := by
        rw [hB_empty]; simp
      rw [hspan_bot] at hv_span
      rw [Submodule.mem_bot] at hv_span
      subst hv_span
      exact ⟨0, Finset.mem_singleton_self 0, by simp [dotProduct]⟩
  · have hBcard_pos : 0 < B.card := Nat.pos_of_ne_zero hB
    set eN := WithLp.linearEquiv 2 ℝ (Fin n → ℝ) with heN_def
    let B_E : Finset (EuclideanSpace ℝ (Fin n)) := B.image eN.symm
    set V := Submodule.span ℝ (B_E : Set (EuclideanSpace ℝ (Fin n))) with hV_def
    haveI : FiniteDimensional ℝ V :=
      FiniteDimensional.span_of_finite ℝ B_E.finite_toSet
    set d' := Module.finrank ℝ V with hd'_def
    have hd'_le : d' ≤ B.card := by
      calc d' ≤ (B_E : Set (EuclideanSpace ℝ (Fin n))).toFinset.card :=
            finrank_span_le_card _
        _ = B_E.card := by simp
        _ ≤ B.card := Finset.card_image_le
    set ob := stdOrthonormalBasis ℝ V with hob_def
    set eD := WithLp.linearEquiv 2 ℝ (Fin d' → ℝ) with heD_def
    let φ : (Fin d' → ℝ) → (Fin n → ℝ) := fun a =>
      eN (V.subtypeₗᵢ (ob.repr.symm (eD.symm a)))

    have hφ_dot : ∀ a : Fin d' → ℝ, dotProduct (φ a) (φ a) = dotProduct a a := by
      intro a
      rw [dotProduct_eq_euclideanNorm_sq, dotProduct_eq_euclideanNorm_sq]
      show ‖eN.symm (eN (V.subtypeₗᵢ (ob.repr.symm (eD.symm a))))‖ ^ 2 =
           ‖eD.symm a‖ ^ 2
      rw [eN.symm_apply_apply]
      rw [LinearIsometry.norm_map, LinearIsometryEquiv.norm_map]

    have hφ_sub : ∀ a b : Fin d' → ℝ, φ a - φ b = φ (a - b) := by
      intro a b; ext i
      simp only [Pi.sub_apply, φ]
      show eN (V.subtypeₗᵢ (ob.repr.symm (eD.symm a))) i -
           eN (V.subtypeₗᵢ (ob.repr.symm (eD.symm b))) i =
           eN (V.subtypeₗᵢ (ob.repr.symm (eD.symm (a - b)))) i
      have h1 : V.subtypeₗᵢ (ob.repr.symm (eD.symm (a - b)))
        = V.subtypeₗᵢ (ob.repr.symm (eD.symm a)) - V.subtypeₗᵢ (ob.repr.symm (eD.symm b)) := by
        rw [map_sub eD.symm, map_sub ob.repr.symm, map_sub V.subtypeₗᵢ]
      rw [h1, map_sub eN, Pi.sub_apply]

    have hφ_span : ∀ a : Fin d' → ℝ, φ a ∈ Submodule.span ℝ (B : Set (Fin n → ℝ)) := by
      intro a
      have h1 : (ob.repr.symm (eD.symm a) : EuclideanSpace ℝ (Fin n)) ∈ V :=
        (ob.repr.symm (eD.symm a)).2
      rw [show Submodule.span ℝ (B : Set (Fin n → ℝ)) =
        (Submodule.span ℝ (B_E : Set (EuclideanSpace ℝ (Fin n)))).map eN.toLinearMap from by
          rw [Submodule.map_span]
          congr 1
          simp only [B_E]
          ext x; simp [LinearEquiv.apply_symm_apply]]
      exact Submodule.mem_map_of_mem h1

    have hV_eq : V = (Submodule.span ℝ (B : Set (Fin n → ℝ))).map eN.symm.toLinearMap := by
      rw [hV_def, Submodule.map_span]
      congr 1
      show ↑B_E = eN.symm.toLinearMap '' ↑B
      simp only [B_E, Finset.coe_image]
      rfl

    have hφ_surj : ∀ v, dotProduct v v ≤ 1 → v ∈ Submodule.span ℝ (B : Set (Fin n → ℝ)) →
        ∃ a : Fin d' → ℝ, dotProduct a a ≤ 1 ∧ φ a = v := by
      intro v hv_unit hv_span
      have hv_E : eN.symm v ∈ V := by
        rw [hV_eq]; exact Submodule.mem_map_of_mem hv_span
      set v_V : V := ⟨eN.symm v, hv_E⟩ with hv_V_def
      set a := eD (ob.repr v_V) with ha_def
      refine ⟨a, ?_, ?_⟩
      · rw [dotProduct_eq_euclideanNorm_sq]
        show ‖eD.symm (eD (ob.repr v_V))‖ ^ 2 ≤ 1
        rw [eD.symm_apply_apply, LinearIsometryEquiv.norm_map]
        have hv_V_norm : ‖v_V‖ = ‖eN.symm v‖ := rfl
        rw [hv_V_norm]
        have : dotProduct v v = ‖eN.symm v‖ ^ 2 := dotProduct_eq_euclideanNorm_sq v
        nlinarith [norm_nonneg (eN.symm v)]
      · show eN (V.subtypeₗᵢ (ob.repr.symm (eD.symm (eD (ob.repr v_V))))) = v
        rw [eD.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]
        show eN ↑v_V = v
        simp [hv_V_def, eN.apply_symm_apply]

    by_cases hd' : d' = 0
    · refine ⟨{0}, ?_, ?_, ?_, ?_⟩
      · simp; exact Nat.one_le_pow _ _ (by norm_num)
      · intro z hz; simp at hz; subst hz; simp [dotProduct]
      · intro z hz; simp at hz; subst hz; exact Submodule.zero_mem _
      · intro v hv_unit hv_span
        obtain ⟨a, _, hφa⟩ := hφ_surj v hv_unit hv_span
        have ha_zero : a = 0 := by ext i; exact (Fin.elim0 (hd' ▸ i))
        have hv_zero : v = φ 0 := by rw [← hφa, ha_zero]
        rw [hv_zero]
        refine ⟨0, Finset.mem_singleton_self 0, ?_⟩
        show dotProduct (φ 0 - 0) (φ 0 - 0) ≤ 1 / 4
        simp only [sub_zero]
        have : dotProduct (φ 0) (φ 0) = dotProduct (0 : Fin d' → ℝ) 0 := hφ_dot 0
        rw [this]; simp [dotProduct]
    · have hd'_pos : 0 < d' := Nat.pos_of_ne_zero hd'
      obtain ⟨N₀, hN₀_card, hN₀_unit, hN₀_cover⟩ :=
        epsilon_net_dotProduct_of_euclidean hd'_pos
      set N := N₀.image φ with hN_def
      refine ⟨N, ?_, ?_, ?_, ?_⟩
      · calc N.card ≤ N₀.card := Finset.card_image_le
          _ ≤ 6 ^ d' := hN₀_card
          _ ≤ 6 ^ B.card := Nat.pow_le_pow_right (by norm_num) hd'_le
      · intro z hz
        rw [Finset.mem_image] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        rw [hφ_dot]; exact hN₀_unit a ha
      · intro z hz
        rw [Finset.mem_image] at hz
        obtain ⟨a, _, rfl⟩ := hz
        exact hφ_span a
      · intro v hv_unit hv_span
        obtain ⟨a, ha_unit, hφa⟩ := hφ_surj v hv_unit hv_span
        obtain ⟨z₀, hz₀_mem, hz₀_close⟩ := hN₀_cover a ha_unit
        refine ⟨φ z₀, Finset.mem_image_of_mem φ hz₀_mem, ?_⟩
        rw [← hφa, hφ_sub a z₀, hφ_dot]
        exact hz₀_close

/-- Discretisation step: if some unit vector `v` in the span of `B` satisfies
`⟨ε, v⟩ > τ`, then some net point `z ∈ N` satisfies `⟨ε, z⟩ > τ/2`. This is the
standard `1/2`-net reduction used to apply union bounds in the sub-Gaussian
supremum argument. -/
theorem epsilon_net_event_containment {n : ℕ}
    {N : Finset (Fin n → ℝ)}
    {B : Finset (Fin n → ℝ)}
    (_hN_unit : ∀ z ∈ N, dotProduct z z ≤ 1)
    (hN_span : ∀ z ∈ N, z ∈ Submodule.span ℝ (B : Set (Fin n → ℝ)))
    (hN_cover : ∀ v, dotProduct v v ≤ 1 → v ∈ Submodule.span ℝ (B : Set (Fin n → ℝ)) →
      ∃ z ∈ N, dotProduct (v - z) (v - z) ≤ 1/4)
    (V : Set (Fin n → ℝ))
    (hV_unit : ∀ v ∈ V, dotProduct v v ≤ 1)
    (hV_span : ∀ v ∈ V, v ∈ Submodule.span ℝ (B : Set (Fin n → ℝ)))
    (ε_val : Fin n → ℝ) (τ : ℝ) (_hτ : 0 < τ) :
    (∃ v ∈ V, dotProduct ε_val v > τ) →
    (∃ z ∈ N, dotProduct ε_val z > τ / 2) := by
  intro ⟨v, hv_mem, hv_big⟩
  by_contra h_neg
  push Not at h_neg


  let S : Set ℝ := {x | ∃ w, dotProduct w w ≤ 1 ∧
    w ∈ Submodule.span ℝ (B : Set (Fin n → ℝ)) ∧ dotProduct ε_val w = x}
  have hS_ne : S.Nonempty := ⟨dotProduct ε_val 0, 0, by simp [dotProduct],
    Submodule.zero_mem _, rfl⟩
  have hS_bdd : BddAbove S := by
    use ∑ i : Fin n, |ε_val i|
    intro x ⟨w, hw_unit, _, hw_eq⟩
    rw [← hw_eq]; unfold dotProduct
    calc ∑ i, ε_val i * w i ≤ ∑ i, |ε_val i * w i| :=
        Finset.sum_le_sum (fun i _ => le_abs_self _)
      _ = ∑ i, |ε_val i| * |w i| := by simp_rw [abs_mul]
      _ ≤ ∑ i, |ε_val i| * 1 := by
          apply Finset.sum_le_sum; intro i _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have h1 : w i * w i ≤ dotProduct w w := by
            unfold dotProduct
            exact Finset.single_le_sum (fun j _ => mul_self_nonneg (w j)) (Finset.mem_univ i)
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (w i + 1), sq_nonneg (w i - 1)]
      _ = ∑ i, |ε_val i| := by simp
  let M := sSup S

  have h_contract : ∀ w, dotProduct w w ≤ 1 → w ∈ Submodule.span ℝ (B : Set (Fin n → ℝ)) →
      dotProduct ε_val w ≤ τ / 2 + M / 2 := by
    intro w hw_unit hw_span
    obtain ⟨z, hz_mem, hz_close⟩ := hN_cover w hw_unit hw_span
    have h_split : dotProduct ε_val w = dotProduct ε_val z + dotProduct ε_val (w - z) := by
      simp [dotProduct, mul_sub]
    rw [h_split]
    have h_z_small : dotProduct ε_val z ≤ τ / 2 := h_neg z hz_mem
    set d := (2 : ℝ) • (w - z) with hd_def
    have h_d_unit : dotProduct d d ≤ 1 := by
      simp only [hd_def, dotProduct, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      have key : (∑ i : Fin n, (2 * (w i - z i)) * (2 * (w i - z i))) =
          4 * dotProduct (w - z) (w - z) := by
        simp only [dotProduct, Pi.sub_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      linarith
    have h_d_span : d ∈ Submodule.span ℝ (B : Set (Fin n → ℝ)) :=
      (Submodule.span ℝ (B : Set (Fin n → ℝ))).smul_mem (2 : ℝ)
        ((Submodule.span ℝ (B : Set (Fin n → ℝ))).sub_mem hw_span (hN_span z hz_mem))
    have h_d_in_S : dotProduct ε_val d ∈ S := ⟨d, h_d_unit, h_d_span, rfl⟩
    have h_d_le_M : dotProduct ε_val d ≤ M := le_csSup hS_bdd h_d_in_S
    have h_half : dotProduct ε_val (w - z) = (1/2) * dotProduct ε_val d := by
      simp only [hd_def, dotProduct, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring
    linarith

  have hM_le : M ≤ τ := by
    have hM_bound : M ≤ τ / 2 + M / 2 := by
      apply csSup_le hS_ne
      intro x ⟨w, hw_unit, hw_span, hw_eq⟩
      rw [← hw_eq]; exact h_contract w hw_unit hw_span
    linarith

  have hv_in_S : dotProduct ε_val v ∈ S :=
    ⟨v, hV_unit v hv_mem, hV_span v hv_mem, rfl⟩
  linarith [le_csSup hS_bdd hv_in_S]

/-- Tail bound on the supremum of `⟨ε, v⟩` over a unit ball `V` of an
`m`-dimensional subspace: combining the `1/2`-net reduction with the Chernoff
bound gives $\mu\{\exists v \in V, \langle\varepsilon, v\rangle > \tau\}
\le 6^m \cdot \exp(-\tau^2 / (8\sigma^2))$. -/
lemma subG_subspace_sup_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {n : ℕ}
    (ε : Ω → Fin n → ℝ) (m : ℕ)
    (σ : ℝ) (hσ : 0 < σ)
    (hsubG : ∀ (v : Fin n → ℝ),
      dotProduct v v ≤ 1 →
      ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ ∧
        ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
        Real.exp (s ^ 2 * σ ^ 2 / 2))

    (V : Set (Fin n → ℝ))
    (hV_unit : ∀ v ∈ V, dotProduct v v ≤ 1)
    (hV_dim : ∃ (B : Finset (Fin n → ℝ)),
      B.card ≤ m ∧ ∀ v ∈ V, v ∈ Submodule.span ℝ (B : Set (Fin n → ℝ)))
    (τ : ℝ) (hτ : 0 < τ) :
    μ {ω | ∃ v ∈ V, dotProduct (ε ω) v > τ} ≤
      ENNReal.ofReal ((6 : ℝ) ^ m * Real.exp (-(τ ^ 2 / (8 * σ ^ 2)))) := by

  obtain ⟨B, hB_card, hV_span⟩ := hV_dim
  obtain ⟨N, hN_card, hN_unit, hN_span, hN_cover⟩ := epsilon_net_covering_number B


  have h_contain : {ω | ∃ v ∈ V, dotProduct (ε ω) v > τ} ⊆
      ⋃ z ∈ N, {ω | dotProduct (ε ω) z > τ / 2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    have ⟨z, hz_mem, hz_big⟩ :=
      epsilon_net_event_containment hN_unit hN_span hN_cover V hV_unit hV_span (ε ω) τ hτ hω

    exact Set.mem_biUnion hz_mem hz_big


  have hτ_half : 0 < τ / 2 := by linarith
  have hexp_eq : (τ / 2) ^ 2 / (2 * σ ^ 2) = τ ^ 2 / (8 * σ ^ 2) := by
    field_simp; ring
  set bound := ENNReal.ofReal (Real.exp (-(τ ^ 2 / (8 * σ ^ 2))))
  have h_per : ∀ z ∈ N, μ {ω | dotProduct (ε ω) z > τ / 2} ≤ bound := by
    intro z hz
    have h := chernoff_tail_from_mgf hσ hsubG z (hN_unit z hz) (τ / 2) hτ_half
    rw [hexp_eq] at h
    exact h

  have h_card_le : N.card ≤ 6 ^ m :=
    le_trans hN_card (Nat.pow_le_pow_right (by norm_num) hB_card)

  calc μ {ω | ∃ v ∈ V, dotProduct (ε ω) v > τ}
      ≤ μ (⋃ z ∈ N, {ω | dotProduct (ε ω) z > τ / 2}) :=
        MeasureTheory.measure_mono h_contain
    _ ≤ ∑ z ∈ N, μ {ω | dotProduct (ε ω) z > τ / 2} :=
        MeasureTheory.measure_biUnion_finset_le N _
    _ ≤ ∑ _z ∈ N, bound := Finset.sum_le_sum h_per
    _ = N.card • bound := Finset.sum_const bound
    _ ≤ (6 ^ m) • bound := nsmul_le_nsmul_left (zero_le bound) h_card_le
    _ = ENNReal.ofReal ((6 : ℝ) ^ m * Real.exp (-(τ ^ 2 / (8 * σ ^ 2)))) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        ring

/-- Per-support tail bound: fix a support `S ⊆ Fin d` of size `2k`; then the
probability that some `S`-supported `w` with `‖Xw‖ ≤ 1` has `⟨ε, Xw⟩ > √t` is
at most `6^(2k) · exp(-t / (8σ²))`. -/
theorem per_support_concentration_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (ε : Ω → Fin n → ℝ) (k : ℕ) (_hk : 1 ≤ k) (_hkd : 2 * k ≤ d)
    (σ : ℝ) (hσ : 0 < σ)
    (hsubG : ∀ (v : Fin n → ℝ),
      dotProduct v v ≤ 1 →
      ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ ∧
        ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
        Real.exp (s ^ 2 * σ ^ 2 / 2))
    (S : Finset (Fin d)) (hS : S.card = 2 * k)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ (w : Fin d → ℝ), (∀ j, j ∉ S → w j = 0) ∧
      dotProduct (X.mulVec w) (X.mulVec w) ≤ 1 ∧
      dotProduct (ε ω) (X.mulVec w) > Real.sqrt t} ≤
    ENNReal.ofReal ((6 : ℝ) ^ (2 * k) * Real.exp (-t / (8 * σ ^ 2))) := by

  set V : Set (Fin n → ℝ) := {v | ∃ (w : Fin d → ℝ),
    (∀ j, j ∉ S → w j = 0) ∧ X.mulVec w = v ∧ dotProduct v v ≤ 1}

  have h_event : {ω | ∃ (w : Fin d → ℝ), (∀ j, j ∉ S → w j = 0) ∧
      dotProduct (X.mulVec w) (X.mulVec w) ≤ 1 ∧
      dotProduct (ε ω) (X.mulVec w) > Real.sqrt t} ⊆
    {ω | ∃ v ∈ V, dotProduct (ε ω) v > Real.sqrt t} := by
    intro ω ⟨w, hw_supp, hw_norm, hw_big⟩
    exact ⟨X.mulVec w, ⟨w, hw_supp, rfl, hw_norm⟩, hw_big⟩

  have hV_unit : ∀ v ∈ V, dotProduct v v ≤ 1 := by
    intro v ⟨_, _, _, hv_norm⟩
    exact hv_norm


  have hV_dim : ∃ (B : Finset (Fin n → ℝ)),
      B.card ≤ 2 * k ∧ ∀ v ∈ V, v ∈ Submodule.span ℝ (B : Set (Fin n → ℝ)) := by

    refine ⟨S.image (fun j => fun i => X i j), ?_, ?_⟩
    · calc (S.image (fun j => fun i => X i j)).card
          ≤ S.card := Finset.card_image_le
        _ = 2 * k := hS
    · intro v ⟨w, hw_supp, hv_eq, _⟩
      rw [← hv_eq]

      have hXw : X.mulVec w = ∑ j : Fin d, w j • (fun i => X i j) := by
        ext i
        simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
        congr 1; ext j; exact mul_comm _ _
      rw [hXw, show (∑ j : Fin d, w j • (fun i => X i j)) =
          ∑ j ∈ S, w j • (fun i => X i j) from
        (Finset.sum_subset (Finset.subset_univ S)
          (fun j _ hj => by simp [hw_supp j hj])).symm]
      apply Submodule.sum_mem
      intro j hj
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_tail := subG_subspace_sup_tail_bound ε (2 * k) σ hσ hsubG V hV_unit hV_dim
    (Real.sqrt t) hsqrt_pos

  have hexp_eq : (Real.sqrt t) ^ 2 / (8 * σ ^ 2) = t / (8 * σ ^ 2) := by
    rw [Real.sq_sqrt ht.le]
  rw [hexp_eq] at h_tail
  have hneg_eq : -(t / (8 * σ ^ 2)) = -t / (8 * σ ^ 2) := by ring
  rw [hneg_eq] at h_tail

  exact le_trans (MeasureTheory.measure_mono h_event) h_tail

/-- Tail bound on the squared prediction error of the sparsity-constrained least
squares estimator. Taking a union bound over all supports of size `2k` gives
$\mu\{\|X(\hat\theta - \theta^*)\|^2 > 4t\} \le \binom{d}{2k}\,6^{2k}\,
\exp(-t / (8\sigma^2))$. -/
theorem sparse_ls_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin d → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d)
    (σ : ℝ) (hσ : 0 < σ)

    (hhat_sparse : ∀ ω, (univ.filter (fun j => θhat ω j ≠ 0)).card ≤ k)
    (hstar_sparse : (univ.filter (fun j => θstar j ≠ 0)).card ≤ k)

    (hLS : ∀ ω, ∀ θ : Fin d → ℝ,
      (univ.filter (fun j => θ j ≠ 0)).card ≤ k →
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω))
                 ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω)) ≤
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec θ)
                 ((X.mulVec θstar + ε ω) - X.mulVec θ))

    (hsubG : ∀ (v : Fin n → ℝ),
      dotProduct v v ≤ 1 →
      ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ ∧
        ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
        Real.exp (s ^ 2 * σ ^ 2 / 2))
    (t : ℝ) (ht : 0 < t) :
    μ {ω | dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) > 4 * t} ≤
      ENNReal.ofReal ((d.choose (2 * k) : ℝ) * (6 : ℝ) ^ (2 * k) * Real.exp (-t / (8 * σ ^ 2))) := by


  set RHS := (d.choose (2 * k) : ℝ) * (6 : ℝ) ^ (2 * k) * Real.exp (-t / (8 * σ ^ 2))
  by_cases hrhs : 1 ≤ RHS
  ·
    calc μ {ω | dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) > 4 * t}
        ≤ μ Set.univ := MeasureTheory.OuterMeasureClass.measure_mono μ (Set.subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
      _ ≤ ENNReal.ofReal RHS := by
          rw [show (1 : ENNReal) = ENNReal.ofReal 1 from by simp]
          exact ENNReal.ofReal_le_ofReal hrhs
  ·
    simp only [not_le] at hrhs

    let event_S (S : Finset (Fin d)) : Set Ω :=
      {ω | ∃ (w : Fin d → ℝ), (∀ j, j ∉ S → w j = 0) ∧
        dotProduct (X.mulVec w) (X.mulVec w) ≤ 1 ∧
        dotProduct (ε ω) (X.mulVec w) > Real.sqrt t}

    have h_contain : {ω | dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) > 4 * t} ⊆
        ⋃ S ∈ Finset.powersetCard (2 * k) (univ : Finset (Fin d)), event_S S := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω

      have h_fund : dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) ≤
          2 * dotProduct (ε ω) (X.mulVec (θhat ω - θstar)) := by
        have h1 := hLS ω θstar hstar_sparse
        have hrhs' : (X.mulVec θstar + ε ω) - X.mulVec θstar = ε ω := by
          ext i; simp [add_sub_cancel_left]
        rw [hrhs'] at h1
        set v' := X.mulVec (θhat ω - θstar) with hv'_def
        have hlhs : (X.mulVec θstar + ε ω) - X.mulVec (θhat ω) = ε ω - v' := by
          ext i; simp [hv'_def, mulVec_sub, Pi.sub_apply, Pi.add_apply]; ring
        rw [hlhs] at h1
        rw [dotProduct_sub_self] at h1
        linarith

      set v := θhat ω - θstar with hv_def
      have hv_sparse : (univ.filter (fun j => v j ≠ 0)).card ≤ 2 * k := by
        calc (univ.filter (fun j => v j ≠ 0)).card
            ≤ (univ.filter (fun j => θhat ω j ≠ 0) ∪ univ.filter (fun j => θstar j ≠ 0)).card := by
              apply Finset.card_le_card
              intro j hj
              simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hj ⊢
              by_contra h; simp only [not_or, Decidable.not_not] at h
              simp [hv_def, Pi.sub_apply, h.1, h.2] at hj
          _ ≤ (univ.filter (fun j => θhat ω j ≠ 0)).card +
              (univ.filter (fun j => θstar j ≠ 0)).card := Finset.card_union_le _ _
          _ ≤ k + k := Nat.add_le_add (hhat_sparse ω) hstar_sparse
          _ = 2 * k := by ring

      obtain ⟨S, hTS, hS_card⟩ := Finset.exists_superset_card_eq hv_sparse (by simp; exact hkd)

      have hS_mem : S ∈ Finset.powersetCard (2 * k) (univ : Finset (Fin d)) :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS_card⟩

      have hv_supp_S : ∀ j, j ∉ S → v j = 0 := by
        intro j hj
        by_contra h
        exact hj (hTS (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩))

      have h_Xv_pos : dotProduct (X.mulVec v) (X.mulVec v) > 0 := by linarith

      set c := 1 / Real.sqrt (dotProduct (X.mulVec v) (X.mulVec v)) with hc_def
      set w := c • v with hw_def

      have hw_supp : ∀ j, j ∉ S → w j = 0 := by
        intro j hj; simp [hw_def, Pi.smul_apply, hv_supp_S j hj]

      have hw_norm : dotProduct (X.mulVec w) (X.mulVec w) ≤ 1 := by
        rw [hw_def, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        have hsqrt_pos : 0 < Real.sqrt (dotProduct (X.mulVec v) (X.mulVec v)) :=
          Real.sqrt_pos.mpr h_Xv_pos
        have : c * (c * dotProduct (X.mulVec v) (X.mulVec v)) = 1 := by
          rw [hc_def]; field_simp; exact (Real.sq_sqrt h_Xv_pos.le).symm
        linarith

      have hw_big : dotProduct (ε ω) (X.mulVec w) > Real.sqrt t := by
        rw [hw_def, mulVec_smul, dotProduct_smul, smul_eq_mul]
        have h_sqrt_pos : 0 < Real.sqrt (dotProduct (X.mulVec v) (X.mulVec v)) :=
          Real.sqrt_pos.mpr h_Xv_pos

        have h1 : c * dotProduct (ε ω) (X.mulVec v) ≥
            Real.sqrt (dotProduct (X.mulVec v) (X.mulVec v)) / 2 := by
          have h_eps_lb : dotProduct (ε ω) (X.mulVec v) ≥
              dotProduct (X.mulVec v) (X.mulVec v) / 2 := by linarith
          have h_key : c * (dotProduct (X.mulVec v) (X.mulVec v) / 2) =
              Real.sqrt (dotProduct (X.mulVec v) (X.mulVec v)) / 2 := by
            rw [hc_def]; field_simp; exact (Real.sq_sqrt h_Xv_pos.le).symm
          calc c * dotProduct (ε ω) (X.mulVec v)
              ≥ c * (dotProduct (X.mulVec v) (X.mulVec v) / 2) := by
                apply mul_le_mul_of_nonneg_left h_eps_lb; rw [hc_def]; positivity
            _ = Real.sqrt (dotProduct (X.mulVec v) (X.mulVec v)) / 2 := h_key

        have h2 : Real.sqrt (dotProduct (X.mulVec v) (X.mulVec v)) / 2 > Real.sqrt t := by
          suffices h : Real.sqrt (4 * t) < Real.sqrt (dotProduct (X.mulVec v) (X.mulVec v)) by
            have : 2 * Real.sqrt t ≤ Real.sqrt (4 * t) := by
              rw [show (4 : ℝ) * t = (2 * Real.sqrt t) * (2 * Real.sqrt t) from by
                nlinarith [Real.sq_sqrt ht.le]]
              rw [Real.sqrt_mul_self (by positivity)]
            linarith
          exact Real.sqrt_lt_sqrt (by positivity) hω
        linarith

      rw [Set.mem_iUnion₂]
      exact ⟨S, hS_mem, ⟨w, hw_supp, hw_norm, hw_big⟩⟩

    set per_bound := ENNReal.ofReal ((6 : ℝ) ^ (2 * k) * Real.exp (-t / (8 * σ ^ 2)))
    have h_per : ∀ S ∈ Finset.powersetCard (2 * k) (univ : Finset (Fin d)),
        μ (event_S S) ≤ per_bound := by
      intro S hS_mem
      have hS_card : S.card = 2 * k := (Finset.mem_powersetCard.mp hS_mem).2
      exact per_support_concentration_bound X ε k hk hkd σ hσ hsubG S hS_card t ht
    calc μ {ω | dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) > 4 * t}
        ≤ μ (⋃ S ∈ Finset.powersetCard (2 * k) (univ : Finset (Fin d)), event_S S) :=
          MeasureTheory.measure_mono h_contain
      _ ≤ ∑ S ∈ Finset.powersetCard (2 * k) (univ : Finset (Fin d)), μ (event_S S) :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ ∑ S ∈ Finset.powersetCard (2 * k) (univ : Finset (Fin d)), per_bound :=
          Finset.sum_le_sum h_per
      _ = (Finset.powersetCard (2 * k) (univ : Finset (Fin d))).card • per_bound :=
          Finset.sum_const _
      _ = ENNReal.ofReal RHS := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1; ring

/-- High-probability prediction-error bound (unnormalised). With probability
$1 - \delta$, the constrained least squares estimator $\hat\theta^{LS}_{B_0(k)}$
satisfies $\|X(\hat\theta - \theta^*)\|^2 \le 32\sigma^2
\bigl(2k\log(e d / (2k)) + 2k\log 6 + \log(1/\delta)\bigr)$. -/
theorem sparse_ls_high_prob_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin d → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d)
    (σ : ℝ) (hσ : 0 < σ)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)

    (hhat_sparse : ∀ ω, (univ.filter (fun j => θhat ω j ≠ 0)).card ≤ k)
    (hstar_sparse : (univ.filter (fun j => θstar j ≠ 0)).card ≤ k)

    (hLS : ∀ ω, ∀ θ : Fin d → ℝ,
      (univ.filter (fun j => θ j ≠ 0)).card ≤ k →
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω))
                 ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω)) ≤
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec θ)
                 ((X.mulVec θstar + ε ω) - X.mulVec θ))

    (hsubG : ∀ (v : Fin n → ℝ),
      dotProduct v v ≤ 1 →
      ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ ∧
        ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
        Real.exp (s ^ 2 * σ ^ 2 / 2)) :
    μ {ω | dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) ≤
      32 * σ ^ 2 * (2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k))
        + 2 * ↑k * Real.log 6 + Real.log (1 / δ))} ≥
    ENNReal.ofReal (1 - δ) := by

  set L := 2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k)) +
           2 * ↑k * Real.log 6 + Real.log (1 / δ) with hL_def
  set t₀ := 8 * σ ^ 2 * L with ht₀_def

  have hL_pos : 0 < L := L_pos k d δ hk hkd hδ_pos hδ_le
  have ht₀_pos : 0 < t₀ := by simp only [ht₀_def]; positivity

  have htail := sparse_ls_tail_bound X θstar ε θhat k hk hkd σ hσ
    hhat_sparse hstar_sparse hLS hsubG t₀ ht₀_pos


  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hexp_simp : -t₀ / (8 * σ ^ 2) = -L := by simp only [ht₀_def]; field_simp
  rw [hexp_simp] at htail


  have htail_rhs_le : (d.choose (2 * k) : ℝ) * (6 : ℝ) ^ (2 * k) * Real.exp (-L) ≤ δ :=
    tail_rhs_le_delta d k δ hk hkd hδ_pos
  have htail_le_δ : μ {ω | dotProduct (X.mulVec (θhat ω - θstar))
      (X.mulVec (θhat ω - θstar)) > 4 * t₀} ≤ ENNReal.ofReal δ :=
    le_trans htail (ENNReal.ofReal_le_ofReal htail_rhs_le)

  have hset_eq : {ω | dotProduct (X.mulVec (θhat ω - θstar))
      (X.mulVec (θhat ω - θstar)) ≤ 32 * σ ^ 2 * L} =
    {ω | dotProduct (X.mulVec (θhat ω - θstar))
      (X.mulVec (θhat ω - θstar)) ≤ 4 * t₀} := by
    ext ω; simp only [Set.mem_setOf_eq, ht₀_def]; ring_nf
  rw [hset_eq]

  exact prob_good_of_tail_bound hδ_pos htail_le_δ

open MeasureTheory in
/-- **Theorem 2.6** (Rigollet, High-Dimensional Statistics).  Sparse least
squares MSE bound: for $k$-sparse $\theta^*$ and the least squares estimator
$\hat\theta^{LS}_{B_0(k)}$ constrained to $k$-sparse vectors, with probability
at least $1 - \delta$,
$$\frac{1}{n}\,\|X(\hat\theta - \theta^*)\|_2^2 \;\lesssim\; \frac{\sigma^2}{n}
  \log\binom{d}{2k} + \frac{\sigma^2 k}{n} + \frac{\sigma^2}{n}\log(1/\delta).$$
This Lean statement gives the explicit constant `32 σ²/n · L`. -/
theorem thm_2_6_sparse_ls_high_prob
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin d → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d)
    (σ : ℝ) (hσ : 0 < σ)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)

    (hhat_sparse : ∀ ω, (univ.filter (fun j => θhat ω j ≠ 0)).card ≤ k)
    (hstar_sparse : (univ.filter (fun j => θstar j ≠ 0)).card ≤ k)

    (hLS : ∀ ω, ∀ θ : Fin d → ℝ,
      (univ.filter (fun j => θ j ≠ 0)).card ≤ k →
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω))
                 ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω)) ≤
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec θ)
                 ((X.mulVec θstar + ε ω) - X.mulVec θ))

    (hsubG : ∀ (v : Fin n → ℝ),
      dotProduct v v ≤ 1 →
      ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ ∧
        ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
        Real.exp (s ^ 2 * σ ^ 2 / 2)) :
    μ {ω | (1 / (n : ℝ)) *
      dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) ≤
      32 * σ ^ 2 / ↑n * (2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k))
        + 2 * ↑k * Real.log 6 + Real.log (1 / δ))} ≥
    ENNReal.ofReal (1 - δ) := by

  have hHP := sparse_ls_high_prob_bound X θstar ε θhat k hk hkd σ hσ δ hδ_pos hδ_le
    hhat_sparse hstar_sparse hLS hsubG

  have hset : {ω | (1 / (n : ℝ)) *
      dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) ≤
      32 * σ ^ 2 / ↑n * (2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k))
        + 2 * ↑k * Real.log 6 + Real.log (1 / δ))} =
    {ω | dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) ≤
      32 * σ ^ 2 * (2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k))
        + 2 * ↑k * Real.log 6 + Real.log (1 / δ))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [show (1 : ℝ) / ↑n *
        dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) =
        dotProduct (X.mulVec (θhat ω - θstar)) (X.mulVec (θhat ω - θstar)) / ↑n by ring]
    rw [show 32 * σ ^ 2 / ↑n * (2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k))
        + 2 * ↑k * Real.log 6 + Real.log (1 / δ)) =
      32 * σ ^ 2 * (2 * ↑k * Real.log (Real.exp 1 * ↑d / (2 * ↑k))
        + 2 * ↑k * Real.log 6 + Real.log (1 / δ)) / ↑n by ring]
    exact div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hn)
  rw [hset]
  exact hHP
