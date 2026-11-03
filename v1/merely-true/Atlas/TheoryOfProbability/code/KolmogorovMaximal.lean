/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory ProbabilityTheory Finset Set

noncomputable section

/-- The partial sum `Sₖ(ω) = ∑_{i ≤ k} Xᵢ(ω)` of a finite family of random variables. -/
def partialSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (k : Fin n) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Iic k, X i ω

/-- The "first crossing at time `k`" event: the set of `ω` for which `|Sₖ(ω)| ≥ ε` but
`|Sⱼ(ω)| < ε` for every `j < k`. These events partition `{∃ k, |Sₖ| ≥ ε}` into disjoint
pieces and are the standard tool in the proof of Kolmogorov's maximal inequality. -/
def stoppingEvent {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ε : ℝ) (k : Fin n) : Set Ω :=
  {ω | |partialSum X k ω| ≥ ε ∧ ∀ j : Fin n, j < k → |partialSum X j ω| < ε}

/-- The full sum `Sₙ(ω) = ∑_{i : Fin n} Xᵢ(ω)` of the family `X`. -/
def fullSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin n, X i ω

/-- The tail sum `∑_{i > k} Xᵢ(ω)` after index `k`. -/
def tailSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (k : Fin n) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Ioi k, X i ω

/-- Decomposition `Sₙ = Sₖ + (Sₙ - Sₖ)` of the full sum into the partial sum up to `k`
plus the tail after `k`. -/
lemma fullSum_eq_partialSum_add_tailSum {Ω : Type*} {n : ℕ}
    (X : Fin n → Ω → ℝ) (k : Fin n) (ω : Ω) :
    fullSum X ω = partialSum X k ω + tailSum X k ω := by
  unfold fullSum partialSum tailSum
  have hdisj : Disjoint (Finset.Iic k) (Finset.Ioi k) :=
    disjoint_left.mpr fun a ha hb => by
      simp [Finset.mem_Iic] at ha; simp [Finset.mem_Ioi] at hb; omega
  have hunion : Finset.Iic k ∪ Finset.Ioi k = Finset.univ := by
    ext x; constructor
    · intro; exact Finset.mem_univ _
    · intro; simp only [Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioi]; omega
  rw [← hunion, Finset.sum_union hdisj]


/-- The "first crossing at time `k`" events are pairwise disjoint over `k : Fin n`. -/
theorem stopping_events_disjoint {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ε : ℝ) :
    Pairwise (fun i j => Disjoint (stoppingEvent X ε i) (stoppingEvent X ε j)) := by
  intro i j hij
  rw [Set.disjoint_iff]
  intro ω ⟨hi, hj⟩
  simp only [stoppingEvent, mem_setOf_eq] at hi hj
  rcases hi with ⟨hi_ge, hi_lt⟩
  rcases hj with ⟨hj_ge, hj_lt⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact absurd (hj_lt i h) (not_lt.mpr hi_ge)
  · exact absurd (hi_lt j h) (not_lt.mpr hj_ge)

/-- The event `{∃ k, |Sₖ| ≥ ε}` decomposes as the disjoint union of the "first crossing"
stopping events `stoppingEvent X ε k` over `k : Fin n`. -/
theorem stopping_events_cover {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) {ε : ℝ} (_hε : 0 < ε) :
    {ω | ∃ k : Fin n, |partialSum X k ω| ≥ ε} = ⋃ k : Fin n, stoppingEvent X ε k := by
  ext ω
  simp only [mem_setOf_eq, mem_iUnion, stoppingEvent]
  constructor
  · intro ⟨k, hk⟩
    classical
    let F := Finset.univ.filter (fun j : Fin n => ε ≤ |partialSum X j ω|)
    have hF : F.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
    let k₀ := F.min' hF
    have hk₀_mem : k₀ ∈ F := Finset.min'_mem F hF
    have hk₀_ge : |partialSum X k₀ ω| ≥ ε := (Finset.mem_filter.mp hk₀_mem).2
    have hk₀_min : ∀ j : Fin n, j < k₀ → |partialSum X j ω| < ε := by
      intro j hj
      by_contra h
      push Not at h
      exact absurd (Finset.min'_le F j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩))
        (not_le.mpr hj)
    exact ⟨k₀, hk₀_ge, hk₀_min⟩
  · intro ⟨k, hk_ge, _⟩
    exact ⟨k, hk_ge⟩

/-- Each partial sum `Sₖ` is measurable whenever each `Xᵢ` is measurable. -/
lemma measurable_partialSum {Ω : Type*} {m : MeasurableSpace Ω} {n : ℕ}
    (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (k : Fin n) :
    Measurable (partialSum X k) :=
  Finset.measurable_sum _ (fun i _ => hmeas i)

/-- The stopping events `stoppingEvent X ε k` are measurable whenever each `Xᵢ` is. -/
theorem stopping_events_measurable {Ω : Type*} {m : MeasurableSpace Ω}
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (ε : ℝ) (k : Fin n) :
    MeasurableSet (stoppingEvent X ε k) := by
  have hset : stoppingEvent X ε k =
    {ω | ε ≤ |partialSum X k ω|} ∩ ⋂ j ∈ Finset.Iio k, {ω | |partialSum X j ω| < ε} := by
    ext ω
    simp only [stoppingEvent, mem_setOf_eq, mem_inter_iff, mem_iInter, Finset.mem_Iio]
  rw [hset]
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_const (measurable_partialSum X hmeas k).norm
  · exact MeasurableSet.biInter (Finset.Iio k).countable_toSet
      (fun j _ => measurableSet_lt (measurable_partialSum X hmeas j).norm measurable_const)


/-- Variant of `measurable_partialSum` with `X` implicit. -/
lemma partialSum_measurable {Ω : Type*} {m : MeasurableSpace Ω} {n : ℕ}
    {X : Fin n → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (k : Fin n) :
    Measurable (partialSum X k) :=
  Finset.measurable_sum _ (fun i _ => hmeas i)

/-- If each `Xᵢ` is square-integrable then each partial sum `Sₖ` is square-integrable. -/
lemma partialSum_sq_integrable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i))
    (hvar : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    (k : Fin n) :
    Integrable (fun ω => (partialSum X k ω) ^ 2) μ := by
  have hmlp : ∀ i, MemLp (X i) 2 μ := fun i =>
    (memLp_two_iff_integrable_sq (hmeas i).aestronglyMeasurable).mpr (hvar i)
  have hmlp_sum : MemLp (fun a => ∑ i ∈ Finset.Iic k, X i a) 2 μ :=
    memLp_finset_sum _ (fun i _ => hmlp i)
  exact (memLp_two_iff_integrable_sq hmlp_sum.aestronglyMeasurable).mp hmlp_sum

/-- If each `Xᵢ` is square-integrable then each tail sum is square-integrable. -/
lemma tailSum_sq_integrable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i))
    (hvar : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    (k : Fin n) : Integrable (fun ω => (tailSum X k ω) ^ 2) μ := by
  have hmlp : ∀ i, MemLp (X i) 2 μ := fun i =>
    (memLp_two_iff_integrable_sq (hmeas i).aestronglyMeasurable).mpr (hvar i)
  have h : MemLp (fun ω => ∑ i ∈ Finset.Ioi k, X i ω) 2 μ :=
    memLp_finset_sum _ (fun i _ => hmlp i)
  exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h

/-- Integrability of the cross term `Sₖ · (Sₙ - Sₖ)` from Cauchy–Schwarz applied to the
square-integrable partial and tail sums. -/
lemma cross_term_integrable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i))
    (hvar : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    (k : Fin n) : Integrable (fun ω => partialSum X k ω * tailSum X k ω) μ := by
  have hmlp : ∀ i, MemLp (X i) 2 μ := fun i =>
    (memLp_two_iff_integrable_sq (hmeas i).aestronglyMeasurable).mpr (hvar i)
  have hmlp_partial : MemLp (fun ω => ∑ i ∈ Finset.Iic k, X i ω) 2 μ :=
    memLp_finset_sum _ (fun i _ => hmlp i)
  have hmlp_tail : MemLp (fun ω => ∑ i ∈ Finset.Ioi k, X i ω) 2 μ :=
    memLp_finset_sum _ (fun i _ => hmlp i)
  have hmul : MemLp ((fun ω => ∑ i ∈ Finset.Iic k, X i ω) *
      fun ω => ∑ i ∈ Finset.Ioi k, X i ω) 1 μ :=
    hmlp_tail.mul (r := 1) hmlp_partial
  have : (fun ω => partialSum X k ω * tailSum X k ω) =
    ((fun ω => ∑ i ∈ Finset.Iic k, X i ω) * fun ω => ∑ i ∈ Finset.Ioi k, X i ω) := by
    ext ω; simp [partialSum, tailSum, Pi.mul_apply]
  rw [this]; exact hmul.integrable le_rfl

/-- The "abstract" partial sum: given a vector `v` indexed by `Finset.Iic k`, sum its
components at indices `≤ j`. Used to express `Sⱼ` as a function of `(Xᵢ)_{i ≤ k}` for
independence arguments. -/
def piPartialSum' {n : ℕ} (k : Fin n) (v : ↥(Finset.Iic k) → ℝ) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun (x : ↥(Finset.Iic k)) => (x : Fin n) ≤ j), v i

/-- The "abstract" version of `stoppingEvent` as a subset of `↥(Finset.Iic k) → ℝ`. -/
def piStoppingSet {n : ℕ} (ε : ℝ) (k : Fin n) : Set (↥(Finset.Iic k) → ℝ) :=
  {v | |piPartialSum' k v k| ≥ ε ∧ ∀ j : Fin n, j < k → |piPartialSum' k v j| < ε}

/-- The function `Φ` on `↥(Finset.Iic k) → ℝ` that takes value `Sₖ(v)` on the stopping set
and `0` outside it. When composed with `ω ↦ (Xᵢ(ω))_{i ≤ k}` it recovers the
indicator-weighted partial sum `1_{stoppingEvent} · Sₖ`. -/
def piPhi' {n : ℕ} (ε : ℝ) (k : Fin n) : (↥(Finset.Iic k) → ℝ) → ℝ :=
  (piStoppingSet ε k).indicator (fun v => piPartialSum' k v k)

/-- The function `Ψ` on `↥(Finset.Ioi k) → ℝ` summing all coordinates; composed with
`ω ↦ (Xᵢ(ω))_{i > k}` it gives the tail sum `Sₙ - Sₖ`. -/
def piPsi' {n : ℕ} (k : Fin n) (v : ↥(Finset.Ioi k) → ℝ) : ℝ :=
  ∑ i : ↥(Finset.Ioi k), v i

/-- Compatibility of `piPartialSum'` with `partialSum`: feeding the actual sample values
`(Xᵢ(ω))_{i ≤ k}` and evaluating at `j ≤ k` recovers `partialSum X j ω`. -/
lemma piPartialSum'_comp {Ω : Type*} {n : ℕ}
    (X : Fin n → Ω → ℝ) (k : Fin n) (ω : Ω) (j : Fin n) (hj : j ≤ k) :
    piPartialSum' k (fun i : ↥(Finset.Iic k) => X (↑i) ω) j = partialSum X j ω := by
  unfold piPartialSum' partialSum
  apply Finset.sum_nbij (fun (i : ↥(Finset.Iic k)) => (i : Fin n))
  · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact Finset.mem_Iic.mpr ha
  · intro a _ b _ hab; exact Subtype.ext hab
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_univ, true_and,
      Set.mem_setOf_eq, Set.mem_image, Finset.mem_Iic] at hb ⊢
    exact ⟨⟨b, Finset.mem_Iic.mpr (le_trans hb hj)⟩, hb, rfl⟩
  · intros; rfl

/-- Composing `piPhi'` with `ω ↦ (Xᵢ(ω))_{i ≤ k}` gives the indicator-weighted partial sum
`1_{stoppingEvent X ε k}(ω) · Sₖ(ω)`. -/
lemma piPhi'_comp {Ω : Type*} {n : ℕ}
    (X : Fin n → Ω → ℝ) (ε : ℝ) (k : Fin n) (ω : Ω) :
    piPhi' ε k (fun i : ↥(Finset.Iic k) => X (↑i) ω) =
      (stoppingEvent X ε k).indicator (partialSum X k) ω := by
  have hcond_iff : (fun i : ↥(Finset.Iic k) => X (↑i) ω) ∈ piStoppingSet ε k ↔
      ω ∈ stoppingEvent X ε k := by
    simp only [piStoppingSet, stoppingEvent, mem_setOf_eq]
    constructor
    · intro ⟨h1, h2⟩
      exact ⟨by rwa [piPartialSum'_comp X k ω k le_rfl] at h1,
             fun j hj => by have := h2 j hj; rwa [piPartialSum'_comp X k ω j (le_of_lt hj)] at this⟩
    · intro ⟨h1, h2⟩
      exact ⟨by rwa [piPartialSum'_comp X k ω k le_rfl],
             fun j hj => by have := h2 j hj; rwa [piPartialSum'_comp X k ω j (le_of_lt hj)]⟩
  unfold piPhi'
  by_cases hω : ω ∈ stoppingEvent X ε k
  · rw [indicator_of_mem (hcond_iff.mpr hω), indicator_of_mem hω,
      piPartialSum'_comp X k ω k le_rfl]
  · rw [indicator_of_notMem (by rwa [hcond_iff]), indicator_of_notMem hω]

/-- Composing `piPsi'` with `ω ↦ (Xᵢ(ω))_{i > k}` recovers the tail sum `Sₙ - Sₖ`. -/
lemma piPsi'_comp {Ω : Type*} {n : ℕ}
    (X : Fin n → Ω → ℝ) (k : Fin n) (ω : Ω) :
    piPsi' k (fun j : ↥(Finset.Ioi k) => X (↑j) ω) = tailSum X k ω := by
  simp only [piPsi', tailSum]
  exact Finset.sum_coe_sort (Finset.Ioi k) (fun i => X i ω)

/-- Rewriting `piStoppingSet` as an intersection of basic sets, convenient for proving
measurability. -/
lemma piStoppingSet_eq {n : ℕ} (ε : ℝ) (k : Fin n) :
    piStoppingSet ε k =
      {v | ε ≤ |piPartialSum' k v k|} ∩
      ⋂ j ∈ Finset.Iio k, {v | |piPartialSum' k v j| < ε} := by
  ext v
  simp only [piStoppingSet, mem_setOf_eq, mem_inter_iff, ge_iff_le, mem_iInter, Finset.mem_Iio]

/-- `piPhi'` is measurable on the product space `↥(Finset.Iic k) → ℝ`. -/
lemma measurable_piPhi' {n : ℕ} (ε : ℝ) (k : Fin n) : Measurable (piPhi' ε k) := by
  apply Measurable.indicator
  · exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  · rw [piStoppingSet_eq]
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_const
        (Measurable.norm (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)))
    · exact MeasurableSet.biInter (Finset.Iio k).countable_toSet
        (fun j _ => measurableSet_lt
          (Measurable.norm (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)))
          measurable_const)

/-- `piPsi'` is measurable on `↥(Finset.Ioi k) → ℝ`. -/
lemma measurable_piPsi' {n : ℕ} (k : Fin n) : Measurable (piPsi' k) :=
  Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

/-- The cross term integrates to zero on the stopping event: for independent mean-zero `Xᵢ`,
`∫_{stoppingEvent X ε k} Sₖ · (Sₙ - Sₖ) dμ = 0`. This uses independence between the
`σ`-algebra generated by `(Xᵢ)_{i ≤ k}` and the tail `(Xᵢ)_{i > k}`. -/
lemma cross_term_vanishes {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hind : iIndepFun (m := fun _ => inferInstance) X μ)
    (hmeas : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    {ε : ℝ} (_hε : 0 < ε) (k : Fin n) :
    ∫ ω in stoppingEvent X ε k,
      (partialSum X k ω) * (tailSum X k ω) ∂μ = 0 := by

  have hint : ∀ i, Integrable (X i) μ := fun i => by
    exact ((memLp_two_iff_integrable_sq (hmeas i).aestronglyMeasurable).mpr (hvar i)).integrable
      one_le_two

  have hdisj : Disjoint (Finset.Iic k) (Finset.Ioi k) :=
    disjoint_left.mpr fun a ha hb => by
      simp [Finset.mem_Iic] at ha; simp [Finset.mem_Ioi] at hb; omega
  have htuple_indep : IndepFun
      (fun ω (i : ↥(Finset.Iic k)) => X (↑i) ω)
      (fun ω (i : ↥(Finset.Ioi k)) => X (↑i) ω) μ :=
    hind.indepFun_finset (Finset.Iic k) (Finset.Ioi k) hdisj hmeas

  have hcomposed_indep : IndepFun
      (piPhi' ε k ∘ fun ω (i : ↥(Finset.Iic k)) => X (↑i) ω)
      (piPsi' k ∘ fun ω (i : ↥(Finset.Ioi k)) => X (↑i) ω) μ :=
    htuple_indep.comp (measurable_piPhi' ε k) (measurable_piPsi' k)

  have hphi_eq : (piPhi' ε k ∘ fun ω (i : ↥(Finset.Iic k)) => X (↑i) ω) =
      (stoppingEvent X ε k).indicator (partialSum X k) := by
    ext ω; exact piPhi'_comp X ε k ω
  have hpsi_eq : (piPsi' k ∘ fun ω (i : ↥(Finset.Ioi k)) => X (↑i) ω) = tailSum X k := by
    ext ω; exact piPsi'_comp X k ω
  rw [hphi_eq, hpsi_eq] at hcomposed_indep

  rw [← integral_indicator (stopping_events_measurable X hmeas ε k)]

  have hind_prod : ∀ ω, (stoppingEvent X ε k).indicator
      (fun ω => partialSum X k ω * tailSum X k ω) ω =
      ((stoppingEvent X ε k).indicator (partialSum X k) ω) * (tailSum X k ω) := by
    intro ω
    by_cases hω : ω ∈ stoppingEvent X ε k
    · simp [indicator_of_mem hω]
    · simp [indicator_of_notMem hω]
  simp_rw [hind_prod]

  have hf_asm : AEStronglyMeasurable
      ((stoppingEvent X ε k).indicator (partialSum X k)) μ :=
    (Measurable.indicator (Finset.measurable_sum _ (fun i _ => hmeas i))
      (stopping_events_measurable X hmeas ε k)).aestronglyMeasurable
  have hg_asm : AEStronglyMeasurable (tailSum X k) μ :=
    (Finset.measurable_sum _ (fun i _ => hmeas i)).aestronglyMeasurable
  rw [hcomposed_indep.integral_fun_mul_eq_mul_integral hf_asm hg_asm]

  have htail_zero : ∫ ω, tailSum X k ω ∂μ = 0 := by
    simp only [tailSum]
    rw [integral_finset_sum _ (fun i _ => hint i)]
    exact Finset.sum_eq_zero (fun j _ => hmean j)
  rw [htail_zero, mul_zero]

/-- On each stopping event, `∫ Sₖ² ≤ ∫ Sₙ²` (a consequence of vanishing of the cross term
and nonnegativity of `(Sₙ - Sₖ)²`). -/
theorem integral_partialSum_sq_le_fullSum_sq {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hind : iIndepFun (m := fun _ => inferInstance) X μ)
    (hmeas : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    {ε : ℝ} (hε : 0 < ε) (k : Fin n) :
    ∫ ω in stoppingEvent X ε k, (partialSum X k ω) ^ 2 ∂μ ≤
      ∫ ω in stoppingEvent X ε k, (fullSum X ω) ^ 2 ∂μ := by

  have hint_S := (partialSum_sq_integrable hmeas hvar k).integrableOn
    (s := stoppingEvent X ε k)
  have hint_F : IntegrableOn (fun ω => (fullSum X ω) ^ 2) (stoppingEvent X ε k) μ := by
    have hmlp : ∀ i, MemLp (X i) 2 μ := fun i =>
      (memLp_two_iff_integrable_sq (hmeas i).aestronglyMeasurable).mpr (hvar i)
    have hmlp_sum : MemLp (fun a => ∑ i : Fin n, X i a) 2 μ :=
      memLp_finset_sum _ (fun i _ => hmlp i)
    exact ((memLp_two_iff_integrable_sq hmlp_sum.aestronglyMeasurable).mp hmlp_sum).integrableOn

  have hint_cross := (cross_term_integrable hmeas hvar k).integrableOn
    (s := stoppingEvent X ε k)
  have hint_T := (tailSum_sq_integrable hmeas hvar k).integrableOn
    (s := stoppingEvent X ε k)

  suffices h : 0 ≤ ∫ ω in stoppingEvent X ε k,
      ((fullSum X ω) ^ 2 - (partialSum X k ω) ^ 2) ∂μ by
    linarith [integral_sub hint_F hint_S]

  have hpw : ∀ ω, (fullSum X ω) ^ 2 - (partialSum X k ω) ^ 2 =
      2 * (partialSum X k ω * tailSum X k ω) + (tailSum X k ω) ^ 2 := by
    intro ω; rw [fullSum_eq_partialSum_add_tailSum]; ring
  simp_rw [hpw]

  rw [integral_add (hint_cross.const_mul 2) hint_T]

  have h1 : ∫ ω in stoppingEvent X ε k,
      2 * (partialSum X k ω * tailSum X k ω) ∂μ = 0 := by
    rw [integral_const_mul]
    simp [cross_term_vanishes hind hmeas hmean hvar hε k]
  have h2 : 0 ≤ ∫ ω in stoppingEvent X ε k, (tailSum X k ω) ^ 2 ∂μ :=
    setIntegral_nonneg_of_ae_restrict
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
  linarith

/-- The per-stopping-event bound: `ε² · μ(stoppingEvent X ε k) ≤ ∫_{stoppingEvent X ε k} Sₙ² dμ`.
This is the key estimate that, summed over `k`, yields Kolmogorov's maximal inequality. -/
theorem per_event_bound {Ω : Type*} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hind : iIndepFun (m := fun _ => inferInstance) X μ)
    (hmeas : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    {ε : ℝ} (hε : 0 < ε) (k : Fin n) :
    ENNReal.ofReal (ε ^ 2) * μ (stoppingEvent X ε k) ≤
      ENNReal.ofReal (∫ ω in stoppingEvent X ε k, (fullSum X ω) ^ 2 ∂μ) := by
  have hε2 : (0 : ℝ) ≤ ε ^ 2 := le_of_lt (pow_pos hε 2)
  have hfin : μ (stoppingEvent X ε k) ≠ ⊤ := measure_ne_top μ _

  conv_lhs => rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hε2]
  apply ENNReal.ofReal_le_ofReal

  have hge : ∀ ω ∈ stoppingEvent X ε k, ε ^ 2 ≤ (partialSum X k ω) ^ 2 := by
    intro ω hω
    rw [← sq_abs (partialSum X k ω)]
    exact pow_le_pow_left₀ hε.le hω.1 2
  calc ε ^ 2 * (μ (stoppingEvent X ε k)).toReal
      = ∫ _ in stoppingEvent X ε k, ε ^ 2 ∂μ := by
        simp [integral_const, Measure.real, smul_eq_mul, mul_comm]
    _ ≤ ∫ ω in stoppingEvent X ε k, (partialSum X k ω) ^ 2 ∂μ := by
        apply setIntegral_mono_on
        · exact integrableOn_const
        · exact (partialSum_sq_integrable hmeas hvar k).integrableOn
        ·
          unfold stoppingEvent
          have : {ω : Ω | |partialSum X k ω| ≥ ε ∧
              ∀ j : Fin n, j < k → |partialSum X j ω| < ε} =
            {ω | ε ≤ |partialSum X k ω|} ∩
              (⋂ j ∈ Finset.Iio k, {ω | |partialSum X j ω| < ε}) := by
            ext ω
            simp only [mem_setOf_eq, mem_inter_iff, ge_iff_le, mem_iInter, Finset.mem_Iio]
          rw [this]
          apply MeasurableSet.inter
          · exact (Measurable.comp measurable_norm (partialSum_measurable hmeas k)) measurableSet_Ici
          · exact MeasurableSet.biInter (Finset.Iio k).countable_toSet
              (fun j _ => (Measurable.comp measurable_norm (partialSum_measurable hmeas j)) measurableSet_Iio)
        · exact hge
    _ ≤ ∫ ω in stoppingEvent X ε k, (fullSum X ω) ^ 2 ∂μ :=
        integral_partialSum_sq_le_fullSum_sq hind hmeas hmean hvar hε k


/-- For independent mean-zero `Xᵢ`, the variance of `Sₙ` is the sum of variances:
`E[Sₙ²] = ∑ᵢ E[Xᵢ²]`. -/
theorem variance_as_sum {Ω : Type*} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hind : iIndepFun (m := fun _ => inferInstance) X μ)
    (hmeas : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ) :
    ∫ ω, (fullSum X ω) ^ 2 ∂μ = ∑ i : Fin n, ∫ ω, (X i ω) ^ 2 ∂μ := by

  have hasm : ∀ i, AEStronglyMeasurable (X i) μ :=
    fun i => (hmeas i).aestronglyMeasurable

  have hmlp : ∀ i, MemLp (X i) 2 μ := fun i =>
    (memLp_two_iff_integrable_sq (hasm i)).mpr (hvar i)

  have sum_eq : (∑ i : Fin n, X i) = fun ω => ∑ i ∈ Finset.univ, X i ω := by
    ext ω; simp [Finset.sum_apply]

  have hmlp_sum : MemLp (∑ i : Fin n, X i) 2 μ := by
    rw [sum_eq]; exact memLp_finset_sum _ (fun i _ => hmlp i)

  have hmean_sum : ∫ ω, (∑ i : Fin n, X i) ω ∂μ = 0 := by
    simp only [sum_apply]
    rw [integral_finset_sum _ (fun i _ => (hmlp i).integrable one_le_two)]
    simp [hmean]

  have fullSum_eq : fullSum X = (∑ i : Fin n, X i) := by
    ext ω; simp [fullSum, sum_apply]
  rw [fullSum_eq]

  have key : ∫ ω, ((∑ i : Fin n, X i) ω) ^ 2 ∂μ =
      variance (∑ i : Fin n, X i) μ := by
    rw [variance_eq_sub hmlp_sum, hmean_sum]
    simp [sum_apply, Pi.pow_apply]
  rw [key]

  have hpw : Set.Pairwise (Finset.univ (α := Fin n) : Set (Fin n))
      (fun i j => IndepFun (X i) (X j) μ) :=
    fun i _ j _ hij => hind.indepFun hij
  rw [IndepFun.variance_sum (fun i _ => hmlp i) hpw]

  congr 1
  ext i
  rw [variance_eq_sub (hmlp i), hmean i]
  simp [Pi.pow_apply]

/-- The full sum `Sₙ` is square-integrable when each `Xᵢ` is square-integrable. -/
lemma fullSum_sq_integrable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i))
    (hvar : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ) :
    Integrable (fun ω => (fullSum X ω) ^ 2) μ := by
  have hmlp : ∀ i, MemLp (X i) 2 μ := fun i =>
    (memLp_two_iff_integrable_sq (hmeas i).aestronglyMeasurable).mpr (hvar i)
  have hmlp_sum : MemLp (fun a => ∑ i : Fin n, X i a) 2 μ :=
    memLp_finset_sum _ (fun i _ => hmlp i)
  exact (memLp_two_iff_integrable_sq hmlp_sum.aestronglyMeasurable).mp hmlp_sum


/-- Aggregating the per-event bound over all stopping events:
`ε² · μ{∃ k, |Sₖ| ≥ ε} ≤ E[Sₙ²]`. -/
theorem aggregate_bound {Ω : Type*} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hind : iIndepFun (m := fun _ => inferInstance) X μ)
    (hmeas : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (ε ^ 2) * μ {ω | ∃ k : Fin n, |partialSum X k ω| ≥ ε} ≤
      ENNReal.ofReal (∫ ω, (fullSum X ω) ^ 2 ∂μ) := by

  rw [stopping_events_cover X hε]

  rw [measure_iUnion (stopping_events_disjoint X ε) (stopping_events_measurable X hmeas ε)]

  rw [← ENNReal.tsum_mul_left]

  have hnn : ∀ i : Fin n, 0 ≤ ∫ ω in stoppingEvent X ε i, (fullSum X ω) ^ 2 ∂μ :=
    fun i => setIntegral_nonneg_of_ae_restrict
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
  have hsum : Summable (fun i : Fin n => ∫ ω in stoppingEvent X ε i, (fullSum X ω) ^ 2 ∂μ) :=
    summable_of_ne_finset_zero (s := Finset.univ)
      (fun _ hx => (hx (Finset.mem_univ _)).elim)
  calc ∑' (i : Fin n), ENNReal.ofReal (ε ^ 2) * μ (stoppingEvent X ε i)
      ≤ ∑' (i : Fin n), ENNReal.ofReal (∫ ω in stoppingEvent X ε i, (fullSum X ω) ^ 2 ∂μ) :=
        ENNReal.tsum_le_tsum (fun k => per_event_bound hind hmeas hmean hvar hε k)
    _ ≤ ENNReal.ofReal (∫ ω, (fullSum X ω) ^ 2 ∂μ) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
        apply ENNReal.ofReal_le_ofReal
        have hint : IntegrableOn (fun ω => (fullSum X ω) ^ 2)
            (⋃ i, stoppingEvent X ε i) μ :=
          (fullSum_sq_integrable hmeas hvar).integrableOn
        rw [← integral_iUnion (stopping_events_measurable X hmeas ε)
            (stopping_events_disjoint X ε) hint]
        exact setIntegral_le_integral (fullSum_sq_integrable hmeas hvar)
          (Filter.Eventually.of_forall (fun ω => sq_nonneg _))


/-- **Kolmogorov's maximal inequality.** Suppose `X₁, …, Xₙ` are independent mean-zero
random variables with finite variances and `Sₖ = ∑_{i ≤ k} Xᵢ`. Then for every `ε > 0`,
`P{max_{1 ≤ k ≤ n} |Sₖ| ≥ ε} ≤ ε⁻² · Var(Sₙ) = ε⁻² · ∑ᵢ E[Xᵢ²]`. -/
theorem kolmogorov_maximal_inequality
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hind : iIndepFun (m := fun _ => inferInstance) X μ)
    (hmeas : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ∃ k : Fin n, |partialSum X k ω| ≥ ε} ≤
      ENNReal.ofReal (∑ i : Fin n, ∫ ω, (X i ω) ^ 2 ∂μ) / ENNReal.ofReal (ε ^ 2) := by
  have hε2_pos : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hε2_ne : ENNReal.ofReal (ε ^ 2) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hε2_pos
  rw [ENNReal.le_div_iff_mul_le (Or.inl hε2_ne) (Or.inl ENNReal.ofReal_ne_top)]
  rw [mul_comm]
  calc ENNReal.ofReal (ε ^ 2) * μ {ω | ∃ k : Fin n, |partialSum X k ω| ≥ ε}
      ≤ ENNReal.ofReal (∫ ω, (fullSum X ω) ^ 2 ∂μ) :=
        aggregate_bound hind hmeas hmean hvar hε
    _ = ENNReal.ofReal (∑ i : Fin n, ∫ ω, (X i ω) ^ 2 ∂μ) := by
        rw [variance_as_sum hind hmeas hmean hvar]

end
