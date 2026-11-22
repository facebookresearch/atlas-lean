/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Matrix MeasureTheory

namespace Rigollet.Chapter3

/-- Empirical mean-squared error `MSE = (1/n) ∑ᵢ (f̂ᵢ - fᵢ)²` used in Theorem 3.4. -/
noncomputable def MSE_34 {n : ℕ} (fhat f : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (fhat i - f i) ^ 2

/-- The support size (ℓ₀ norm) `|θ|₀ = #{i : θᵢ ≠ 0}` used in Theorem 3.4. -/
noncomputable def support_size_34 {M : ℕ} (θ : Fin M → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => θ i ≠ 0)).card

/-- Standard expansion of the BIC inequality: subtracting `‖ε‖²` from both sides of the
penalized noisy comparison yields a noise-free inequality with a single cross term
`2 ⟨ε, a - b⟩`. -/
lemma bic_expansion {n : ℕ} (f ε a b : Fin n → ℝ) (P_hat P_θ : ℝ)
    (h : dotProduct (f + ε - a) (f + ε - a) + P_hat ≤
         dotProduct (f + ε - b) (f + ε - b) + P_θ) :
    dotProduct (f - a) (f - a) + P_hat ≤
      dotProduct (f - b) (f - b) + 2 * dotProduct ε (a - b) + P_θ := by
  have ha : f + ε - a = (f - a) + ε := by ext i; simp; ring
  have hb : f + ε - b = (f - b) + ε := by ext i; simp; ring
  rw [ha, hb] at h
  simp only [dotProduct_add, add_dotProduct, dotProduct_comm ε] at h
  linarith [show dotProduct (f - b) ε - dotProduct (f - a) ε =
    dotProduct ε (a - b) from by simp only [dotProduct_sub, dotProduct_comm]; ring]

/-- Algebraic core of the BIC oracle argument: combining the penalized BIC bound with a
noise control gives `(1 - α) A ≤ (1 + α) B + P + R`. -/
lemma bic_algebraic_core (A B cross P P_hat R α : ℝ)
    (hP_hat : 0 ≤ P_hat) (hBIC : A + P_hat ≤ B + cross + P)
    (hnoise : cross ≤ α * A + α * B + R) :
    (1 - α) * A ≤ (1 + α) * B + P + R := by linarith

/-- Sub-Gaussian noise condition via the moment generating function: for every unit
vector `v` and every `s ∈ ℝ`, the MGF of `⟨ε, v⟩` is bounded by `exp(s² σ² / 2)`. -/
def IsSubGaussianNoiseMGF {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (ε : Ω → Fin n → ℝ) (σsq : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, dotProduct v v = 1 →
    ∀ s : ℝ, ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤ Real.exp (s ^ 2 * σsq / 2)

/-- Conversion between empirical inner product and `MSE`: `⟨f - g, f - g⟩ = n · MSE(g, f)`. -/
lemma dot_eq_n_mul_MSE {n : ℕ} (hn : 0 < n) (g f : Fin n → ℝ) :
    dotProduct (f - g) (f - g) = ↑n * MSE_34 g f := by
  unfold MSE_34 dotProduct; simp only [Pi.sub_apply]
  have : ∑ x : Fin n, (f x - g x) * (f x - g x) = ∑ i : Fin n, (g i - f i) ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [this]; field_simp

/-- Young's inequality combined with the triangle inequality, controlling the cross term
`2 ⟨ε, a - b⟩` by a normalized noise term plus `α (‖a - f‖² + ‖b - f‖²)`. -/
lemma cross_term_young_triangle_bound
    {n : ℕ} (ε a b f : Fin n → ℝ) (α : ℝ) (hα : 0 < α) :
    2 * dotProduct ε (a - b) ≤
      (2 / α) * dotProduct ε (a - b) ^ 2 / dotProduct (a - b) (a - b) +
      α * dotProduct (a - f) (a - f) +
      α * dotProduct (b - f) (b - f) := by
  set d := dotProduct ε (a - b)
  set N := dotProduct (a - b) (a - b)
  have hN_nn : 0 ≤ N := by
    simp only [N, dotProduct, Pi.sub_apply]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a i - b i)

  have htri : (α / 2) * N ≤
      α * dotProduct (a - f) (a - f) + α * dotProduct (b - f) (b - f) := by
    have hN_le : N ≤ 2 * dotProduct (a - f) (a - f) + 2 * dotProduct (b - f) (b - f) := by
      simp only [N, dotProduct, Pi.sub_apply]
      calc ∑ i : Fin n, (a i - b i) * (a i - b i)
          ≤ ∑ i, (2 * ((a i - f i) * (a i - f i)) + 2 * ((b i - f i) * (b i - f i))) :=
            Finset.sum_le_sum fun i _ =>
              by nlinarith [sq_nonneg ((a i - f i) - (b i - f i)),
                            sq_nonneg ((a i - f i) + (b i - f i))]
        _ = 2 * ∑ i, (a i - f i) * (a i - f i) + 2 * ∑ i, (b i - f i) * (b i - f i) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    nlinarith
  by_cases hN : N = 0
  ·
    have hd : d = 0 := by
      have hab : ∀ i : Fin n, a i = b i := by
        intro i
        have hN0 : ∑ k : Fin n, (a k - b k) * (a k - b k) = 0 := by
          simp only [N, dotProduct, Pi.sub_apply] at hN; exact hN
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun k _ => mul_self_nonneg (a k - b k))).mp hN0 i (Finset.mem_univ i)
        nlinarith [sq_nonneg (a i - b i)]
      simp only [d, dotProduct, Pi.sub_apply]
      exact Finset.sum_eq_zero fun i _ => by rw [hab i]; ring
    rw [hd, hN]
    simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_zero, zero_add]
    have h1 : 0 ≤ α * dotProduct (a - f) (a - f) := by
      apply mul_nonneg (le_of_lt hα)
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h2 : 0 ≤ α * dotProduct (b - f) (b - f) := by
      apply mul_nonneg (le_of_lt hα)
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    linarith
  ·
    have hN_pos : 0 < N := lt_of_le_of_ne hN_nn (Ne.symm hN)
    have hyoung : 2 * d ≤ 2 / α * (d ^ 2 / N) + α / 2 * N := by
      rw [show 2 / α * (d ^ 2 / N) + α / 2 * N =
        (4 * d ^ 2 + α ^ 2 * N ^ 2) / (2 * α * N) from by field_simp; ring]
      rw [show 2 * d = 2 * d * (2 * α * N) / (2 * α * N) from by field_simp]
      exact div_le_div_of_nonneg_right
        (by nlinarith [sq_nonneg (2 * d - α * N)]) (by positivity)
    have hassoc : 2 / α * (d ^ 2 / N) = 2 / α * d ^ 2 / N := by ring
    rw [hassoc] at hyoung
    linarith

/-- Probabilistic ratio bound for the projected noise: with probability `1 - δ`, the ratio
`⟨ε, w⟩² / ⟨w, w⟩` (with `w = Φ θ̂ - Φ θ`) is controlled by a sub-Gaussian "peeling"
expression involving `log(eM)` and `log(1/δ)`. -/
lemma peeling_prob_bound_ratio
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n M : ℕ} (_hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin M → ℝ)
    (σ : ℝ) (hσ : 0 < σ)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (_hsubG : IsSubGaussianNoiseMGF μ ε (σ ^ 2)) :
    ∃ C : ℝ, 0 < C ∧
    μ {ω | ∀ θ : Fin M → ℝ,
      dotProduct (ε ω) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) ^ 2 /
        dotProduct (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) ≤
        C * σ ^ 2 * ↑(support_size_34 θ) * Real.log (Real.exp 1 * ↑M) +
        C * σ ^ 2 * Real.log (1 / δ)}
    ≥ ENNReal.ofReal (1 - δ) := by

  have cs_bound : ∀ ω : Ω, ∀ θ : Fin M → ℝ,
      dotProduct (ε ω) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) ^ 2 /
        dotProduct (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) ≤
        dotProduct (ε ω) (ε ω) := by
    intro ω θ
    set e := ε ω; set w := Φ *ᵥ (θhat ω) - Φ *ᵥ θ
    by_cases hw : dotProduct w w = 0
    · have hw0 : ∀ i, w i = 0 := by
        intro i
        simp only [dotProduct] at hw
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun k _ => mul_self_nonneg (w k))).mp hw i (Finset.mem_univ i)
        nlinarith [sq_nonneg (w i)]
      have : dotProduct e w = 0 := by
        simp only [dotProduct]
        exact Finset.sum_eq_zero fun i _ => by rw [hw0 i]; ring
      rw [this, hw]; simp
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    · have hw_pos : 0 < dotProduct w w :=
        lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Ne.symm hw)
      rw [div_le_iff₀ hw_pos]
      have key := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ e w
      simp only [dotProduct]
      calc (∑ i, e i * w i) ^ 2 ≤ (∑ i, e i ^ 2) * ∑ i, w i ^ 2 := key
        _ = (∑ i, e i * e i) * ∑ i, w i * w i := by
            congr 1 <;> (apply Finset.sum_congr rfl; intro i _; ring)

  set S : ℕ → Set Ω := fun k => {ω | dotProduct (ε ω) (ε ω) ≤ ↑k} with hS_def

  have hS_mono : Monotone S := by
    intro a b hab ω hω
    show dotProduct (ε ω) (ε ω) ≤ ↑b
    exact le_trans hω (Nat.cast_le.mpr hab)

  have hS_univ : ⋃ k, S k = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨⌈dotProduct (ε ω) (ε ω)⌉₊, show dotProduct (ε ω) (ε ω) ≤ ↑⌈dotProduct (ε ω) (ε ω)⌉₊ from Nat.le_ceil _⟩

  have htend : Filter.Tendsto (fun k => μ (S k)) Filter.atTop
      (nhds (μ (⋃ k, S k))) :=
    tendsto_measure_iUnion_atTop hS_mono
  rw [hS_univ, measure_univ] at htend
  rw [ENNReal.tendsto_atTop ENNReal.one_ne_top] at htend
  obtain ⟨N, hN_prop⟩ := htend (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ_pos)
  have hN_bound : μ (S N) ≥ ENNReal.ofReal (1 - δ) := by
    have hNN := (hN_prop N le_rfl).1
    have hsub : (1 : ENNReal) - ENNReal.ofReal δ = ENNReal.ofReal (1 - δ) := by
      have h2 := ENNReal.ofReal_sub (p := (1 : ℝ)) (q := δ) (le_of_lt hδ_pos)
      rw [ENNReal.ofReal_one] at h2
      exact h2.symm
    rwa [hsub] at hNN

  by_cases hδ_lt : δ < 1
  ·
    have hlogD_pos : 0 < Real.log (1 / δ) := by
      apply Real.log_pos; rw [lt_div_iff₀ hδ_pos]; linarith
    refine ⟨(↑N + 1) / (σ ^ 2 * Real.log (1 / δ)), by positivity, ?_⟩
    apply le_trans hN_bound
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro θ

    have hLHS := cs_bound ω θ

    have hRHS_ge : (↑N + 1) / (σ ^ 2 * Real.log (1 / δ)) * σ ^ 2 *
        ↑(support_size_34 θ) * Real.log (Real.exp 1 * ↑M) +
      (↑N + 1) / (σ ^ 2 * Real.log (1 / δ)) * σ ^ 2 * Real.log (1 / δ) ≥ ↑N := by
      have hσ2_pos : 0 < σ ^ 2 := sq_pos_of_pos hσ
      have hσ2_ne : σ ^ 2 ≠ 0 := ne_of_gt hσ2_pos
      have hlogD_ne : Real.log (1 / δ) ≠ 0 := ne_of_gt hlogD_pos
      have hprod_ne : σ ^ 2 * Real.log (1 / δ) ≠ 0 := mul_ne_zero hσ2_ne hlogD_ne
      have hterm2 : (↑N + 1) / (σ ^ 2 * Real.log (1 / δ)) * σ ^ 2 *
          Real.log (1 / δ) = ↑N + 1 := by
        field_simp
      rw [hterm2]
      have hterm1 : 0 ≤ (↑N + 1) / (σ ^ 2 * Real.log (1 / δ)) * σ ^ 2 *
          ↑(support_size_34 θ) * Real.log (Real.exp 1 * ↑M) := by
        apply mul_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · apply div_nonneg (by positivity : (0 : ℝ) ≤ ↑N + 1) (by positivity)
            · exact le_of_lt hσ2_pos
          · exact Nat.cast_nonneg _
        · apply Real.log_nonneg
          calc (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
            _ = Real.exp 1 * 1 := (mul_one _).symm
            _ ≤ Real.exp 1 * ↑M := by
                apply mul_le_mul_of_nonneg_left (by exact_mod_cast hM)
                  (le_of_lt (Real.exp_pos 1))
      linarith
    have hω_ineq : dotProduct (ε ω) (ε ω) ≤ ↑N := hω
    linarith
  ·
    have hδ_eq : δ = 1 := le_antisymm hδ_le (not_lt.mp hδ_lt)
    refine ⟨1, one_pos, ?_⟩
    rw [hδ_eq]
    simp only [sub_self, ENNReal.ofReal_zero]
    exact zero_le _

/-- Unit-vector concentration with the explicit `2 / α` constant: a peeling bound on the
normalized squared inner product `(2/α) · ⟨ε, w⟩² / ⟨w, w⟩` valid with probability `1 - δ`. -/
theorem peeling_unit_vector_concentration
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin M → ℝ)
    (σ : ℝ) (hσ : 0 < σ)
    (α : ℝ) (hα_pos : 0 < α) (_hα_lt : α < 1)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hsubG : IsSubGaussianNoiseMGF μ ε (σ ^ 2)) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
    μ {ω | ∀ θ : Fin M → ℝ,
      (2 / α) * dotProduct (ε ω) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) ^ 2 /
        dotProduct (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) ≤
        C₂ * σ ^ 2 * ↑(support_size_34 θ) * Real.log (Real.exp 1 * ↑M) +
        C₂ * σ ^ 2 * Real.log (1 / δ)}
    ≥ ENNReal.ofReal (1 - δ) := by

  obtain ⟨C, hC_pos, hpeeling⟩ :=
    peeling_prob_bound_ratio hn hM Φ ε θhat σ hσ δ hδ_pos hδ_le hsubG

  refine ⟨2 / α * C, by positivity, ?_⟩

  apply le_trans hpeeling
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro θ

  have hω_θ := hω θ
  have h2α_nn : (0 : ℝ) ≤ 2 / α := by positivity
  have hN_nn : 0 ≤ dotProduct (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hd2N_nn : 0 ≤ dotProduct (ε ω) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) ^ 2 /
      dotProduct (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) :=
    div_nonneg (sq_nonneg _) hN_nn
  calc (2 / α) * dotProduct (ε ω) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) ^ 2 /
        dotProduct (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ)
      = (2 / α) * (dotProduct (ε ω) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) ^ 2 /
          dotProduct (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ)) := by ring
    _ ≤ (2 / α) * (C * σ ^ 2 * ↑(support_size_34 θ) * Real.log (Real.exp 1 * ↑M) +
          C * σ ^ 2 * Real.log (1 / δ)) := by
        exact mul_le_mul_of_nonneg_left hω_θ h2α_nn
    _ = 2 / α * C * σ ^ 2 * ↑(support_size_34 θ) * Real.log (Real.exp 1 * ↑M) +
        2 / α * C * σ ^ 2 * Real.log (1 / δ) := by ring

/-- High-probability concentration of the cross term `2 ⟨ε, Φθ̂ - Φθ⟩` after combining
peeling with Young's inequality, yielding `α ‖f - Φθ̂‖² + α ‖f - Φθ‖² + (penalty terms)`. -/
theorem noise_peeling_concentration_ch3
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin M → ℝ)
    (σ : ℝ) (hσ : 0 < σ)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hsubG : IsSubGaussianNoiseMGF μ ε (σ ^ 2)) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
    μ {ω | ∀ θ : Fin M → ℝ,
      2 * dotProduct (ε ω) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) ≤
        α * dotProduct (f - Φ *ᵥ (θhat ω)) (f - Φ *ᵥ (θhat ω)) +
        α * dotProduct (f - Φ *ᵥ θ) (f - Φ *ᵥ θ) +
        C₁ * σ ^ 2 * ↑(support_size_34 θ) * Real.log (Real.exp 1 * ↑M) +
        C₁ * σ ^ 2 * Real.log (1 / δ)}
    ≥ ENNReal.ofReal (1 - δ) := by

  obtain ⟨C₂, hC₂_pos, hpeeling⟩ :=
    peeling_unit_vector_concentration hn hM Φ ε θhat σ hσ α hα_pos hα_lt δ hδ_pos hδ_le hsubG

  refine ⟨C₂, hC₂_pos, le_trans hpeeling (measure_mono fun ω hω => ?_)⟩
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro θ

  have hyoung_tri := cross_term_young_triangle_bound (ε ω) (Φ *ᵥ (θhat ω)) (Φ *ᵥ θ) f α hα_pos

  have hpeel_θ := hω θ

  have h_sym1 : dotProduct (Φ *ᵥ (θhat ω) - f) (Φ *ᵥ (θhat ω) - f) =
      dotProduct (f - Φ *ᵥ (θhat ω)) (f - Φ *ᵥ (θhat ω)) := by
    simp_rw [dotProduct, Pi.sub_apply]; congr 1; ext i; ring
  have h_sym2 : dotProduct (Φ *ᵥ θ - f) (Φ *ᵥ θ - f) =
      dotProduct (f - Φ *ᵥ θ) (f - Φ *ᵥ θ) := by
    simp_rw [dotProduct, Pi.sub_apply]; congr 1; ext i; ring
  rw [h_sym1, h_sym2] at hyoung_tri
  linarith

/-- Combined sub-Gaussian peeling and BIC-style penalty bound for the squared-error oracle
inequality `(1 - α) ‖f - Φθ̂‖² ≤ (1 + α) ‖f - Φθ‖² + (sparsity term) + (deviation term)`,
valid with probability at least `1 - δ`. -/
theorem subG_peeling_dot_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin M → ℝ)
    (σ : ℝ) (hσ : 0 < σ)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hsubG : IsSubGaussianNoiseMGF μ ε (σ ^ 2))
    (hBIC : ∀ ω θ,
      dotProduct (f + ε ω - Φ *ᵥ (θhat ω)) (f + ε ω - Φ *ᵥ (θhat ω)) +
        (16 * σ ^ 2 / α) * Real.log (6 * Real.exp 1 * ↑M) *
          ↑(support_size_34 (θhat ω)) ≤
      dotProduct (f + ε ω - Φ *ᵥ θ) (f + ε ω - Φ *ᵥ θ) +
        (16 * σ ^ 2 / α) * Real.log (6 * Real.exp 1 * ↑M) *
          ↑(support_size_34 θ)) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    μ {ω | ∀ θ : Fin M → ℝ,
      (1 - α) * dotProduct (f - Φ *ᵥ (θhat ω)) (f - Φ *ᵥ (θhat ω)) ≤
        (1 + α) * dotProduct (f - Φ *ᵥ θ) (f - Φ *ᵥ θ) +
        C₀ * σ ^ 2 * ↑(support_size_34 θ) * Real.log (Real.exp 1 * ↑M) +
        C₀ * σ ^ 2 * Real.log (1 / δ)}
    ≥ ENNReal.ofReal (1 - δ) := by

  obtain ⟨C₁, hC₁_pos, hpeeling⟩ :=
    noise_peeling_concentration_ch3 hn hM Φ f ε θhat σ hσ α hα_pos hα_lt δ hδ_pos hδ_le hsubG

  set logEM := Real.log (Real.exp 1 * ↑M) with hlogEM_def
  set log6EM := Real.log (6 * Real.exp 1 * ↑M) with hlog6EM_def

  have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr hM
  have heM_gt_1 : 1 < Real.exp 1 * ↑M := by
    calc (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ = Real.exp 1 * 1 := (mul_one _).symm
      _ ≤ Real.exp 1 * ↑M := mul_le_mul_of_nonneg_left (by exact_mod_cast hM)
            (le_of_lt (Real.exp_pos 1))
  have hlogEM_pos : 0 < logEM := Real.log_pos heM_gt_1
  have h6eM_gt_1 : 1 < 6 * Real.exp 1 * ↑M := by
    calc (1 : ℝ) < Real.exp 1 * ↑M := heM_gt_1
      _ ≤ 6 * Real.exp 1 * ↑M := by nlinarith
  have hlog6EM_pos : 0 < log6EM := Real.log_pos h6eM_gt_1

  refine ⟨C₁ + 16 * log6EM / (α * logEM), ?_, ?_⟩
  ·
    have : 0 < 16 * log6EM / (α * logEM) := by positivity
    linarith
  ·
    apply le_trans hpeeling
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro θ

    set nτ2 := (16 * σ ^ 2 / α) * log6EM with hnτ2_def
    have hbic_ω := hBIC ω θ
    have hexpanded := bic_expansion f (ε ω) (Φ *ᵥ (θhat ω)) (Φ *ᵥ θ)
        (nτ2 * ↑(support_size_34 (θhat ω)))
        (nτ2 * ↑(support_size_34 θ))
        (by convert hbic_ω using 1)

    have hnoise_ω := hω θ

    set A := dotProduct (f - Φ *ᵥ (θhat ω)) (f - Φ *ᵥ (θhat ω)) with hA_def
    set B := dotProduct (f - Φ *ᵥ θ) (f - Φ *ᵥ θ) with hB_def
    set cross := 2 * dotProduct (ε ω) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ) with hcross_def
    set s := (↑(support_size_34 θ) : ℝ) with hs_def
    set Ld := Real.log (1 / δ) with hLd_def

    have hP_hat_nn : 0 ≤ nτ2 * ↑(support_size_34 (θhat ω)) := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply div_nonneg
          · exact mul_nonneg (by norm_num) (sq_nonneg σ)
          · exact le_of_lt hα_pos
        · exact le_of_lt hlog6EM_pos
      · exact Nat.cast_nonneg _

    have hnoise_ω' : cross ≤ α * A + α * B +
        (C₁ * σ ^ 2 * s * logEM + C₁ * σ ^ 2 * Ld) := by linarith
    have h_core := bic_algebraic_core A B cross (nτ2 * s) (nτ2 * ↑(support_size_34 (θhat ω)))
        (C₁ * σ ^ 2 * s * logEM + C₁ * σ ^ 2 * Ld) α
        hP_hat_nn
        hexpanded
        hnoise_ω'

    calc (1 - α) * A ≤ (1 + α) * B + nτ2 * s + (C₁ * σ ^ 2 * s * logEM + C₁ * σ ^ 2 * Ld) :=
            h_core
      _ = (1 + α) * B + (C₁ * σ ^ 2 * s * logEM + nτ2 * s) + C₁ * σ ^ 2 * Ld := by ring
      _ = (1 + α) * B + (C₁ + 16 * log6EM / (α * logEM)) * σ ^ 2 * s * logEM +
            C₁ * σ ^ 2 * Ld := by
          have hα_ne : α ≠ 0 := ne_of_gt hα_pos
          have hlogEM_ne : logEM ≠ 0 := ne_of_gt hlogEM_pos
          rw [hnτ2_def]
          field_simp
      _ ≤ (1 + α) * B + (C₁ + 16 * log6EM / (α * logEM)) * σ ^ 2 * s * logEM +
            (C₁ + 16 * log6EM / (α * logEM)) * σ ^ 2 * Ld := by
          have hLd_nn : 0 ≤ Ld := by
            simp only [hLd_def]
            rw [one_div, Real.log_inv]
            linarith [Real.log_nonpos (le_of_lt hδ_pos) hδ_le]
          have h_extra : 0 ≤ 16 * log6EM / (α * logEM) * σ ^ 2 * Ld := by positivity
          linarith

/-- High-probability event version of Theorem 3.4 prior to taking the infimum: there is a
constant `C` such that with probability at least `1 - δ`, the BIC estimator satisfies the
per-`θ` oracle inequality with the explicit `(1 + α) / (1 - α)` constant. -/
theorem subG_bic_oracle_event
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin M → ℝ)
    (σ : ℝ) (hσ : 0 < σ)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)

    (hsubG : IsSubGaussianNoiseMGF μ ε (σ ^ 2))

    (hBIC : ∀ ω θ,
      dotProduct (f + ε ω - Φ *ᵥ (θhat ω)) (f + ε ω - Φ *ᵥ (θhat ω)) +
        (16 * σ ^ 2 / α) * Real.log (6 * Real.exp 1 * ↑M) *
          ↑(support_size_34 (θhat ω)) ≤
      dotProduct (f + ε ω - Φ *ᵥ θ) (f + ε ω - Φ *ᵥ θ) +
        (16 * σ ^ 2 / α) * Real.log (6 * Real.exp 1 * ↑M) *
          ↑(support_size_34 θ)) :
    ∃ C_const : ℝ, 0 < C_const ∧
    μ {ω | ∀ θ : Fin M → ℝ,
      MSE_34 (Φ *ᵥ (θhat ω)) f ≤
        (1 + α) / (1 - α) * MSE_34 (Φ *ᵥ θ) f +
        C_const * σ ^ 2 / (α * (1 - α) * ↑n) *
          ↑(support_size_34 θ) * Real.log (Real.exp 1 * ↑M) +
        C_const * σ ^ 2 / (α * (1 - α) * ↑n) *
          Real.log (1 / δ)}
    ≥ ENNReal.ofReal (1 - δ) := by

  obtain ⟨C₀, hC₀_pos, hpeeling⟩ :=
    subG_peeling_dot_bound hn hM Φ f ε θhat σ hσ α hα_pos hα_lt δ hδ_pos hδ_le hsubG hBIC

  refine ⟨C₀, hC₀_pos, le_trans hpeeling (measure_mono fun ω hω => ?_)⟩
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro θ

  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h1_sub_α_pos : (0 : ℝ) < 1 - α := by linarith

  have hdot := hω θ
  rw [dot_eq_n_mul_MSE hn (Φ *ᵥ (θhat ω)) f,
      dot_eq_n_mul_MSE hn (Φ *ᵥ θ) f] at hdot

  set M1 := MSE_34 (Φ *ᵥ (θhat ω)) f with hM1_def
  set M2 := MSE_34 (Φ *ᵥ θ) f with hM2_def
  set s := (↑(support_size_34 θ) : ℝ) with hs_def
  set L := Real.log (Real.exp 1 * ↑M) with hL_def
  set Ld := Real.log (1 / δ) with hLd_def

  suffices h : M1 * (α * (1 - α) * ↑n) ≤
      ((1 + α) / (1 - α) * M2 + C₀ * σ ^ 2 / (α * (1 - α) * ↑n) * s * L +
        C₀ * σ ^ 2 / (α * (1 - α) * ↑n) * Ld) * (α * (1 - α) * ↑n) by
    exact le_of_mul_le_mul_right h (by positivity)
  have hrhs : ((1 + α) / (1 - α) * M2 + C₀ * σ ^ 2 / (α * (1 - α) * ↑n) * s * L +
      C₀ * σ ^ 2 / (α * (1 - α) * ↑n) * Ld) * (α * (1 - α) * ↑n) =
    (1 + α) * α * ↑n * M2 + C₀ * σ ^ 2 * s * L + C₀ * σ ^ 2 * Ld := by
    field_simp
  rw [hrhs]

  have hs_nonneg : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hL_pos : 0 < L := by
    simp [hL_def]; apply Real.log_pos
    calc (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ = Real.exp 1 * 1 := by ring
      _ ≤ Real.exp 1 * ↑M := mul_le_mul_of_nonneg_left (by exact_mod_cast hM)
            (le_of_lt (Real.exp_pos 1))
  have hLd_nonneg : 0 ≤ Ld := by
    simp only [hLd_def]
    rw [one_div, Real.log_inv]
    linarith [Real.log_nonpos (le_of_lt hδ_pos) hδ_le]
  have h_sL_nonneg : 0 ≤ (1 - α) * (C₀ * σ ^ 2 * s * L) := by positivity
  have h_Ld_nonneg : 0 ≤ (1 - α) * (C₀ * σ ^ 2 * Ld) := by positivity
  nlinarith

/-- Theorem 3.4 (BIC oracle inequality): for the BIC estimator with regularization
`τ² = 16 σ² / (α n) · log(6 e M)` and sub-Gaussian noise, with probability at least `1 - δ`
the MSE satisfies the oracle inequality
`MSE(Φ θ̂) ≤ inf_θ {(1 + α)/(1 - α) MSE(Φ θ) + C σ² / (α (1 - α) n) |θ|₀ log(eM)}
            + C σ² / (α (1 - α) n) log(1/δ)`. -/
theorem thm_3_4_bic_oracle_inequality
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)

    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin M → ℝ)

    (σ : ℝ) (hσ : 0 < σ)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)

    (hsubG : IsSubGaussianNoiseMGF μ ε (σ ^ 2))

    (hBIC : ∀ ω θ,
      dotProduct (f + ε ω - Φ *ᵥ (θhat ω)) (f + ε ω - Φ *ᵥ (θhat ω)) +
        (16 * σ ^ 2 / α) * Real.log (6 * Real.exp 1 * ↑M) *
          ↑(support_size_34 (θhat ω)) ≤
      dotProduct (f + ε ω - Φ *ᵥ θ) (f + ε ω - Φ *ᵥ θ) +
        (16 * σ ^ 2 / α) * Real.log (6 * Real.exp 1 * ↑M) *
          ↑(support_size_34 θ)) :
    ∃ C_const : ℝ, 0 < C_const ∧
    μ {ω | MSE_34 (Φ *ᵥ (θhat ω)) f ≤
      (⨅ θ : Fin M → ℝ,
        (1 + α) / (1 - α) * MSE_34 (Φ *ᵥ θ) f +
        C_const * σ ^ 2 / (α * (1 - α) * ↑n) *
          ↑(support_size_34 θ) * Real.log (Real.exp 1 * ↑M)) +
      C_const * σ ^ 2 / (α * (1 - α) * ↑n) * Real.log (1 / δ)}
    ≥ ENNReal.ofReal (1 - δ) := by

  obtain ⟨C_const, hC, hconc⟩ := subG_bic_oracle_event hn hM Φ f ε θhat σ hσ α hα_pos hα_lt
    δ hδ_pos hδ_le hsubG hBIC
  refine ⟨C_const, hC, ?_⟩

  apply le_trans hconc
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  haveI : Nonempty (Fin M → ℝ) := ⟨fun _ => 0⟩

  have hsub : ∀ θ : Fin M → ℝ,
      MSE_34 (Φ *ᵥ (θhat ω)) f -
        C_const * σ ^ 2 / (α * (1 - α) * ↑n) * Real.log (1 / δ) ≤
      (1 + α) / (1 - α) * MSE_34 (Φ *ᵥ θ) f +
        C_const * σ ^ 2 / (α * (1 - α) * ↑n) *
          ↑(support_size_34 θ) * Real.log (Real.exp 1 * ↑M) :=
    fun θ => by linarith [hω θ]

  linarith [le_ciInf hsub]

end Rigollet.Chapter3
