/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter5.Def_5_1_5_2
import Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8

open MeasureTheory Minimax

noncomputable section

/-- Each measure `gsm.P θ` in a Gaussian sequence model is a probability
measure. -/
theorem gsm_isProbabilityMeasure (gsm : GaussianSequenceModel)
    (θ : Fin gsm.d → ℝ) : IsProbabilityMeasure (gsm.P θ) :=
  gsm.hP_prob θ

/-- Any two parameter-conditional measures in a Gaussian sequence model are
mutually absolutely continuous. -/
theorem gsm_absolutelyContinuous (gsm : GaussianSequenceModel)
    (θ₀ θ₁ : Fin gsm.d → ℝ) : (gsm.P θ₀).AbsolutelyContinuous (gsm.P θ₁) :=
  gsm.hP_ac θ₀ θ₁

/-- Closed-form Gaussian KL divergence in a Gaussian sequence model:
`KL(P_{θ₁} ‖ P_{θ₀}) = n‖θ₁ - θ₀‖² / (2σ²)`. -/
theorem gsm_klDiv_toReal (gsm : GaussianSequenceModel)
    (θ₀ θ₁ : Fin gsm.d → ℝ) :
    (InformationTheory.klDiv (gsm.P θ₁) (gsm.P θ₀)).toReal =
      gsm.n * sqDist θ₁ θ₀ / (2 * gsm.σ ^ 2) :=
  gsm.hP_kl_toReal θ₀ θ₁

/-- KL divergences in a Gaussian sequence model are finite. -/
theorem gsm_klDiv_ne_top (gsm : GaussianSequenceModel)
    (θ₀ θ₁ : Fin gsm.d → ℝ) :
    InformationTheory.klDiv (gsm.P θ₁) (gsm.P θ₀) ≠ ⊤ :=
  gsm.hP_kl_ne_top θ₀ θ₁

/-- Triangle-type inequality for the squared Euclidean distance:
`‖a - b‖² ≤ 2‖c - a‖² + 2‖c - b‖²`. -/
lemma sqDist_triangle_le {d : ℕ} (a b c : Fin d → ℝ) :
    sqDist a b ≤ 2 * sqDist c a + 2 * sqDist c b := by
  unfold sqDist
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (a i - c i + c i - b i), sq_nonneg (a i - c i - (c i - b i))]

/-- Estimation-to-testing reduction: the sum of probabilities that an estimator
fails by more than `2α²σ²/n` at `θ₀` and `θ₁` is at least `1 - TV(P_{θ₀}, P_{θ₁})`
when `‖θ₀ - θ₁‖² = 8α²σ²/n`. -/
theorem estimation_to_testing_sum_bound (gsm : GaussianSequenceModel)
    (θ₀ θ₁ : Fin gsm.d → ℝ)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_lt : α < 1/2)
    (hDist : sqDist θ₀ θ₁ = 8 * α^2 * gsm.σ^2 / gsm.n)
    [IsProbabilityMeasure (gsm.P θ₀)]
    [IsProbabilityMeasure (gsm.P θ₁)]
    (θhat : Estimator gsm.d) :
    (gsm.P θ₀ {Y | sqDist (θhat Y) θ₀ ≥ 2 * α^2 * gsm.σ^2 / gsm.n}).toReal +
    (gsm.P θ₁ {Y | sqDist (θhat Y) θ₁ ≥ 2 * α^2 * gsm.σ^2 / gsm.n}).toReal ≥
      1 - Chapter5.TVNP.tvDist (gsm.P θ₀) (gsm.P θ₁) := by
  set φ := 2 * α ^ 2 * gsm.σ ^ 2 / ↑gsm.n with hφ_def

  let ψ : (Fin gsm.d → ℝ) → Bool := fun Y => decide (sqDist (θhat Y) θ₀ ≥ φ)


  have hψ_meas : Measurable ψ := by
    apply measurable_to_countable'
    intro b
    cases b
    · show MeasurableSet {ω | decide (sqDist (θhat ω) θ₀ ≥ φ) = false}
      convert (gsm.hP_measurableSet_sqDist_ge θhat θ₀ φ).compl using 1
      ext Y; simp [decide_eq_false_iff_not, not_le]
    · show MeasurableSet {ω | decide (sqDist (θhat ω) θ₀ ≥ φ) = true}
      convert (gsm.hP_measurableSet_sqDist_ge θhat θ₀ φ) using 1
      ext Y; simp [decide_eq_true_eq]
  have hNP := Chapter5.TVNP.neyman_pearson_lower (gsm.P θ₀) (gsm.P θ₁)
    inferInstance inferInstance ψ hψ_meas


  have hDist_half : sqDist θ₀ θ₁ / 2 = 4 * α ^ 2 * gsm.σ ^ 2 / ↑gsm.n := by
    rw [hDist]; ring
  have hφ_eq_half : φ = sqDist θ₀ θ₁ / 2 - φ := by
    rw [hDist_half, hφ_def]; ring


  have h_inclusion : {Y | ψ Y = false} ⊆ {Y | sqDist (θhat Y) θ₁ ≥ φ} := by
    intro Y hY
    simp only [Set.mem_setOf_eq, ψ, decide_eq_false_iff_not, not_le] at hY
    simp only [Set.mem_setOf_eq]


    have htri := sqDist_triangle_le θ₀ θ₁ (θhat Y)


    linarith

  have h_P1_mono : (gsm.P θ₁ {Y | ψ Y = false}).toReal ≤
      (gsm.P θ₁ {Y | sqDist (θhat Y) θ₁ ≥ φ}).toReal := by
    apply ENNReal.toReal_mono
    · exact ne_top_of_le_ne_top (measure_ne_top (gsm.P θ₁) Set.univ)
        (measure_mono (Set.subset_univ _))
    · exact measure_mono h_inclusion

  have h_sets_eq : {Y | ψ Y = true} = {Y | sqDist (θhat Y) θ₀ ≥ φ} := by
    ext Y; simp [ψ, decide_eq_true_eq]

  rw [h_sets_eq] at hNP
  linarith

/-- Boundedness above (`≤ 1`) of the outer parametrised supremum in the
definition of `supProbLargeError`. -/
lemma supProbLargeError_bddAbove_outer (gsm : GaussianSequenceModel)
    (θhat : Estimator gsm.d) (φ : ℝ) :
    BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ gsm.Θ),
      (gsm.P θ {Y | sqDist (θhat Y) θ ≥ φ}).toReal) := by
  refine ⟨1, fun x ⟨θ, hθ⟩ => hθ ▸ ?_⟩
  by_cases hm : θ ∈ gsm.Θ
  · simp only [hm, ciSup_pos]
    haveI := gsm.hP_prob θ
    exact Chapter5.TVNP.measure_toReal_le_one (gsm.P θ) _
  · simp [hm]

/-- Boundedness above of the inner parametrised supremum in the definition of
`supProbLargeError`: the value is constant in the membership proof. -/
lemma supProbLargeError_bddAbove_inner (gsm : GaussianSequenceModel)
    (θhat : Estimator gsm.d) (φ : ℝ) (θ₀ : Fin gsm.d → ℝ) :
    BddAbove (Set.range fun (_ : θ₀ ∈ gsm.Θ) =>
      (gsm.P θ₀ {Y | sqDist (θhat Y) θ₀ ≥ φ}).toReal) :=
  ⟨(gsm.P θ₀ {Y | sqDist (θhat Y) θ₀ ≥ φ}).toReal, fun _ ⟨_, h⟩ => h ▸ le_refl _⟩

/-- Two-point Le Cam reduction: the minimax probability of a `2α²σ²/n` error
is at least `½(1 - TV(P_{θ₀}, P_{θ₁}))`, provided the two hypotheses are at the
prescribed squared distance. -/
theorem two_point_testing_reduction (gsm : GaussianSequenceModel)
    (θ₀ θ₁ : Fin gsm.d → ℝ)
    (hΘ₀ : θ₀ ∈ gsm.Θ) (hΘ₁ : θ₁ ∈ gsm.Θ)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1/2)
    (hDist : sqDist θ₀ θ₁ = 8 * α^2 * gsm.σ^2 / gsm.n)
    [IsProbabilityMeasure (gsm.P θ₀)]
    [IsProbabilityMeasure (gsm.P θ₁)] :
    minimaxProbLargeError gsm (2 * α^2 * gsm.σ^2 / gsm.n) ≥
      (1/2) * (1 - Chapter5.TVNP.tvDist (gsm.P θ₀) (gsm.P θ₁)) := by
  set φ := 2 * α ^ 2 * gsm.σ ^ 2 / ↑gsm.n
  suffices h : ∀ θhat : Estimator gsm.d,
      1 / 2 * (1 - Chapter5.TVNP.tvDist (gsm.P θ₀) (gsm.P θ₁)) ≤
      supProbLargeError gsm θhat φ by
    unfold minimaxProbLargeError
    exact ge_iff_le.mpr (le_ciInf (fun θhat => h θhat))
  intro θhat
  have h0 : (gsm.P θ₀ {Y | sqDist (θhat Y) θ₀ ≥ φ}).toReal ≤
      supProbLargeError gsm θhat φ := by
    unfold supProbLargeError
    exact le_ciSup_of_le (supProbLargeError_bddAbove_outer gsm θhat φ) θ₀
      (le_ciSup_of_le (supProbLargeError_bddAbove_inner gsm θhat φ θ₀) hΘ₀ (le_refl _))
  have h1 : (gsm.P θ₁ {Y | sqDist (θhat Y) θ₁ ≥ φ}).toReal ≤
      supProbLargeError gsm θhat φ := by
    unfold supProbLargeError
    exact le_ciSup_of_le (supProbLargeError_bddAbove_outer gsm θhat φ) θ₁
      (le_ciSup_of_le (supProbLargeError_bddAbove_inner gsm θhat φ θ₁) hΘ₁ (le_refl _))
  have hSum := estimation_to_testing_sum_bound gsm θ₀ θ₁ α hα_pos hα_lt hDist θhat
  linarith

/-- Two-point minimax lower bound for the Gaussian sequence model: combining
the testing reduction with Pinsker yields
`inf_{θ̂} sup_{θ ∈ Θ} P_θ(‖θ̂ - θ‖² ≥ 2α²σ²/n) ≥ 1/2 - α`. -/
theorem Minimax.minimaxLowerBound_gaussianSequence (gsm : GaussianSequenceModel)
    (θ₀ θ₁ : Fin gsm.d → ℝ)
    (hΘ₀ : θ₀ ∈ gsm.Θ) (hΘ₁ : θ₁ ∈ gsm.Θ)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1/2)
    (hDist : sqDist θ₀ θ₁ = 8 * α^2 * gsm.σ^2 / gsm.n) :
    minimaxProbLargeError gsm (2 * α^2 * gsm.σ^2 / gsm.n) ≥ 1/2 - α := by
  haveI hP₀ := gsm_isProbabilityMeasure gsm θ₀
  haveI hP₁ := gsm_isProbabilityMeasure gsm θ₁
  have hac : (gsm.P θ₁).AbsolutelyContinuous (gsm.P θ₀) :=
    gsm_absolutelyContinuous gsm θ₁ θ₀
  have hKL_ne_top := gsm_klDiv_ne_top gsm θ₀ θ₁
  have h_step1 := two_point_testing_reduction gsm θ₀ θ₁ hΘ₀ hΘ₁ α hα_pos hα_lt hDist
  have h_pinsker := Chapter5.TVNP.pinsker_inequality
    (gsm.P θ₁) (gsm.P θ₀) hac hKL_ne_top
  have hKL_val := gsm_klDiv_toReal gsm θ₀ θ₁
  have hsqDist_sym : sqDist θ₁ θ₀ = sqDist θ₀ θ₁ := by
    unfold sqDist; congr 1; ext i; ring
  have hKL_eq : (InformationTheory.klDiv (gsm.P θ₁) (gsm.P θ₀)).toReal =
      4 * α ^ 2 := by
    rw [hKL_val, hsqDist_sym, hDist]
    have hσ_ne : gsm.σ ≠ 0 := ne_of_gt gsm.hσ
    have hn_ne : (gsm.n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp gsm.hn)
    field_simp
    ring
  have hSqrt_KL : Real.sqrt (Chapter5.TVNP.klDiv_real (gsm.P θ₁) (gsm.P θ₀)) =
      2 * α := by
    unfold Chapter5.TVNP.klDiv_real
    rw [hKL_eq, show (4 : ℝ) * α ^ 2 = (2 * α) ^ 2 from by ring]
    exact Real.sqrt_sq (by linarith)
  have hTV10_le : Chapter5.TVNP.tvDist (gsm.P θ₁) (gsm.P θ₀) ≤ 2 * α := by
    calc Chapter5.TVNP.tvDist (gsm.P θ₁) (gsm.P θ₀)
        ≤ Real.sqrt (Chapter5.TVNP.klDiv_real (gsm.P θ₁) (gsm.P θ₀)) := h_pinsker
      _ = 2 * α := hSqrt_KL
  have hTV_sym : Chapter5.TVNP.tvDist (gsm.P θ₀) (gsm.P θ₁) =
      Chapter5.TVNP.tvDist (gsm.P θ₁) (gsm.P θ₀) := by
    unfold Chapter5.TVNP.tvDist
    congr 1; ext x; constructor
    · rintro ⟨S, hS, hx⟩; exact ⟨S, hS, by rw [hx, abs_sub_comm]⟩
    · rintro ⟨S, hS, hx⟩; exact ⟨S, hS, by rw [hx, abs_sub_comm]⟩
  have hTV_le : Chapter5.TVNP.tvDist (gsm.P θ₀) (gsm.P θ₁) ≤ 2 * α := by
    rw [hTV_sym]; exact hTV10_le
  linarith

/-- Theorem 5.9 (two-point method): if `Θ` contains `θ₀, θ₁` with
`‖θ₀ - θ₁‖² = 8α²σ²/n`, then
`inf_{θ̂} sup_{θ ∈ Θ} P_θ(‖θ̂ - θ‖² ≥ 2α²σ²/n) ≥ 1/2 - α`. -/
theorem Minimax.theorem_5_9 (gsm : GaussianSequenceModel)
    (θ₀ θ₁ : Fin gsm.d → ℝ)
    (hΘ₀ : θ₀ ∈ gsm.Θ) (hΘ₁ : θ₁ ∈ gsm.Θ)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1/2)
    (hDist : sqDist θ₀ θ₁ = 8 * α^2 * gsm.σ^2 / gsm.n) :
    minimaxProbLargeError gsm (2 * α^2 * gsm.σ^2 / gsm.n) ≥ 1/2 - α :=
  Minimax.minimaxLowerBound_gaussianSequence gsm θ₀ θ₁ hΘ₀ hΘ₁ α hα_pos hα_lt hDist
