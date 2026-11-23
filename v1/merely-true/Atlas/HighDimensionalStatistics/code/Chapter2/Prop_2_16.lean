/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_9
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 800000

open Matrix Finset BigOperators MeasureTheory ProbabilityTheory Real ENNReal

/-- The Rademacher distribution on `ℝ`: a fair mixture of point masses at `+1` and `-1`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (1 : ℝ) + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (-1 : ℝ)

/-- An `n × d` random matrix `X` is *i.i.d. Rademacher* if its entries are jointly
independent, each marginal equals the Rademacher distribution under the pushforward of `μ`,
and the coordinate maps are measurable. -/
def IsIIDRademacherMatrix {Ω : Type*} [MeasurableSpace Ω]
    {n d : ℕ} (X : Ω → Matrix (Fin n) (Fin d) ℝ) (μ : Measure Ω) : Prop :=

  @iIndepFun Ω (Fin n × Fin d) _ (fun _ => ℝ) (fun _ => inferInstance)
    (fun p : Fin n × Fin d => fun ω => X ω p.1 p.2) μ ∧

  (∀ (i : Fin n) (j : Fin d), Measure.map (fun ω => X ω i j) μ = rademacherMeasure) ∧

  (∀ (i : Fin n) (j : Fin d), Measurable (fun ω => X ω i j))

/-- The incoherence assumption `INC(k)`: `|XᵀX / n − I_d|_∞ ≤ 1 / (14 k)`, i.e. the
empirical Gram matrix is close to the identity entrywise. -/
def AssumptionINC {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (k : ℕ) : Prop :=
  ∀ i j : Fin d,
    |((Xᵀ * X) i j : ℝ) / (n : ℝ) - if i = j then 1 else 0| ≤ 1 / (14 * (k : ℝ))

/-- For a `±1` matrix `X`, the diagonal entries of `XᵀX` all equal `n`. -/
lemma rademacher_diag_eq_n {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (hRad : ∀ i j, X i j = 1 ∨ X i j = -1) (j : Fin d) :
    (Xᵀ * X) j j = (n : ℝ) := by
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  have : ∀ i : Fin n, X i j * X i j = 1 := by
    intro i; rcases hRad i j with h | h <;> simp [h]
  simp [this, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Failure of `INC(k)` for a `±1` matrix reduces to violation on some off-diagonal entry:
the complement of `{INC(k)}` is contained in the union, over distinct index pairs, of the
events `|(XᵀX) i j / n| > 1/(14k)`. -/
lemma inc_compl_subset_offDiag_union {Ω : Type*} [MeasurableSpace Ω]
    {n d k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    (hRad : ∀ ω, ∀ i : Fin n, ∀ j : Fin d, X ω i j = 1 ∨ X ω i j = -1) :
    {ω | AssumptionINC (X ω) k}ᶜ ⊆
    ⋃ p ∈ (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 ≠ p.2),
      {ω | 1 / (14 * (k : ℝ)) < |((X ω)ᵀ * X ω) p.1 p.2 / (n : ℝ)|} := by
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, AssumptionINC, not_forall] at hω
  obtain ⟨i, j, hij⟩ := hω
  push Not at hij
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : i = j
  · subst h
    exfalso
    have hdiag := rademacher_diag_eq_n (X ω) (hRad ω) i
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    simp only [ite_true] at hij
    rw [hdiag, div_self (ne_of_gt hn_pos), sub_self, abs_zero] at hij
    have : (0 : ℝ) < 1 / (14 * (k : ℝ)) := by positivity
    linarith
  · exact ⟨⟨i, j⟩, h, by simp only [h, ite_false, sub_zero] at hij; exact hij⟩

/-- For an i.i.d. Rademacher matrix and distinct column indices `j₁ ≠ j₂`, the products
`X i j₁ * X i j₂` are jointly independent across rows `i`. -/
theorem rademacher_product_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    (hIID : IsIIDRademacherMatrix X μ)
    (j₁ j₂ : Fin d) (hne : j₁ ≠ j₂) :
    iIndepFun (fun i : Fin n => fun ω => X ω i j₁ * X ω i j₂) μ := by

  have hle : ∀ i : Fin n,
      MeasurableSpace.comap (fun ω => X ω i j₁ * X ω i j₂) (borel ℝ) ≤
      MeasurableSpace.comap (fun ω => X ω i j₁) (borel ℝ) ⊔
      MeasurableSpace.comap (fun ω => X ω i j₂) (borel ℝ) := fun i =>
    @Measurable.comap_le Ω ℝ
      (MeasurableSpace.comap (fun ω => X ω i j₁) (borel ℝ) ⊔
       MeasurableSpace.comap (fun ω => X ω i j₂) (borel ℝ))
      (borel ℝ) (fun ω => X ω i j₁ * X ω i j₂)
      ((Measurable.of_comap_le (m₂ := borel ℝ) le_sup_left).mul
       (Measurable.of_comap_le (m₂ := borel ℝ) le_sup_right))

  suffices h_iIndep : iIndep (fun i : Fin n =>
      MeasurableSpace.comap (fun ω => X ω i j₁) (borel ℝ) ⊔
      MeasurableSpace.comap (fun ω => X ω i j₂) (borel ℝ)) μ by
    exact iIndep_of_iIndep_of_le h_iIndep hle
  have hcomap_le : ∀ i : Fin n,
      MeasurableSpace.comap (fun ω => X ω i j₁) (borel ℝ) ⊔
      MeasurableSpace.comap (fun ω => X ω i j₂) (borel ℝ) ≤ ‹MeasurableSpace Ω› :=
    fun i => sup_le (Measurable.comap_le (hIID.2.2 i j₁)) (Measurable.comap_le (hIID.2.2 i j₂))

  set piSys : Fin n → Set (Set Ω) := fun i =>
    {S | ∃ (A B : Set ℝ), MeasurableSet A ∧ MeasurableSet B ∧
      S = (fun ω => X ω i j₁) ⁻¹' A ∩ (fun ω => X ω i j₂) ⁻¹' B}
  refine iIndepSets.iIndep hcomap_le piSys ?hpi ?hgen ?hind
  case hpi =>
    intro i S₁ hS₁ S₂ hS₂ _
    obtain ⟨A₁, B₁, hA₁, hB₁, rfl⟩ := hS₁
    obtain ⟨A₂, B₂, hA₂, hB₂, rfl⟩ := hS₂
    exact ⟨A₁ ∩ A₂, B₁ ∩ B₂, hA₁.inter hA₂, hB₁.inter hB₂, by
      simp only [Set.preimage_inter]; ext; simp [Set.mem_inter_iff]; tauto⟩
  case hgen =>
    intro i; apply le_antisymm
    · apply sup_le
      · rw [MeasurableSpace.comap_le_iff_le_map]; intro S hS; rw [MeasurableSpace.map_def]
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨S, Set.univ, hS, MeasurableSet.univ, by simp⟩
      · rw [MeasurableSpace.comap_le_iff_le_map]; intro S hS; rw [MeasurableSpace.map_def]
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨Set.univ, S, MeasurableSet.univ, hS, by simp⟩
    · apply MeasurableSpace.generateFrom_le
      rintro S ⟨A, B, hA, hB, rfl⟩
      exact @MeasurableSet.inter Ω
        (MeasurableSpace.comap (fun ω => X ω i j₁) (borel ℝ) ⊔
         MeasurableSpace.comap (fun ω => X ω i j₂) (borel ℝ)) _ _
        (@le_sup_left _ _ (MeasurableSpace.comap (fun ω => X ω i j₁) (borel ℝ))
          (MeasurableSpace.comap (fun ω => X ω i j₂) (borel ℝ)) _ ⟨A, hA, rfl⟩)
        (@le_sup_right _ _ (MeasurableSpace.comap (fun ω => X ω i j₁) (borel ℝ))
          (MeasurableSpace.comap (fun ω => X ω i j₂) (borel ℝ)) _ ⟨B, hB, rfl⟩)
  case hind =>
    rw [iIndepSets_iff]
    intro s f hf

    choose A B hA hB hfAB using fun i (hi : i ∈ s) => hf i hi

    set A' : Fin n → Set ℝ := fun i => if h : i ∈ s then A i h else Set.univ
    set B' : Fin n → Set ℝ := fun i => if h : i ∈ s then B i h else Set.univ

    set T : Fin n → Finset (Fin n × Fin d) := fun i => {(i, j₁), (i, j₂)}

    have hT_disj : (s : Set (Fin n)).PairwiseDisjoint T := by
      intro a _ b _ hab
      simp only [T, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
      rintro p (rfl | rfl) (h | h) <;> exact absurd (Prod.mk.inj h).1 hab

    have hA'_eq : ∀ i (hi : i ∈ s), A' i = A i hi := fun i hi => by simp [A', hi]
    have hB'_eq : ∀ i (hi : i ∈ s), B' i = B i hi := fun i hi => by simp [B', hi]
    have hA'_meas : ∀ i ∈ s, MeasurableSet (A' i) := by
      intro i hi; rw [hA'_eq i hi]; exact hA i hi
    have hB'_meas : ∀ i ∈ s, MeasurableSet (B' i) := by
      intro i hi; rw [hB'_eq i hi]; exact hB i hi

    have hfi : ∀ i ∈ s, f i = (fun ω => X ω i j₁) ⁻¹' (A' i) ∩
        (fun ω => X ω i j₂) ⁻¹' (B' i) := by
      intro i hi; rw [hA'_eq i hi, hB'_eq i hi]; exact hfAB i hi

    have hf_prod : ∀ i ∈ s, μ (f i) =
        μ ((fun ω => X ω i j₁) ⁻¹' (A' i)) * μ ((fun ω => X ω i j₂) ⁻¹' (B' i)) := by
      intro i hi
      rw [hfi i hi]
      exact (hIID.1.indepFun (show ((i, j₁) : Fin n × Fin d) ≠ (i, j₂) from by
        simp [Prod.ext_iff, hne])).measure_inter_preimage_eq_mul
        (A' i) (B' i) (hA'_meas i hi) (hB'_meas i hi)

    set C : Fin n × Fin d → Set ℝ := fun p =>
      if p.2 = j₁ then A' p.1 else if p.2 = j₂ then B' p.1 else Set.univ
    set S := s.biUnion T with hS_def

    have hC_meas : ∀ p, p ∈ S → MeasurableSet (C p) := by
      intro p hp
      simp only [hS_def, T, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hp
      obtain ⟨i, hi, rfl | rfl⟩ := hp
      · simp only [C, show j₁ = j₁ from rfl, ite_true]; exact hA'_meas i hi
      · simp only [C, show (j₂ = j₁) = False from propext ⟨fun h => hne h.symm, False.elim⟩,
                   ite_false, show j₂ = j₂ from rfl, ite_true]; exact hB'_meas i hi

    have h_biInter : ⋂ i ∈ s, f i = ⋂ p ∈ S, (fun ω => X ω p.1 p.2) ⁻¹' (C p) := by
      rw [hS_def, Finset.set_biInter_biUnion]
      apply Set.iInter₂_congr
      intro i hi
      symm

      ext ω
      simp only [T, Finset.mem_insert, Finset.mem_singleton, Set.mem_iInter]
      constructor
      · intro h
        have h1 := h (i, j₁) (Or.inl rfl)
        have h2 := h (i, j₂) (Or.inr rfl)
        rw [hfi i hi]
        simp only [C] at h1 h2
        simp only [show j₁ = j₁ from rfl, ite_true] at h1
        simp only [show (j₂ = j₁) = False from propext ⟨fun h => hne h.symm, False.elim⟩,
                   ite_false, show j₂ = j₂ from rfl, ite_true] at h2
        exact ⟨h1, h2⟩
      · intro h
        rw [hfi i hi] at h
        rintro ⟨a, b⟩ (hab | hab)
        · have : a = i ∧ b = j₁ := Prod.mk.inj hab
          simp only [C, this.1, this.2, show j₁ = j₁ from rfl, ite_true]
          exact h.1
        · have : a = i ∧ b = j₂ := Prod.mk.inj hab
          simp only [C, this.1, this.2,
            show (j₂ = j₁) = False from propext ⟨fun h => hne h.symm, False.elim⟩,
            ite_false, show j₂ = j₂ from rfl, ite_true]
          exact h.2

    rw [h_biInter, hIID.1.measure_inter_preimage_eq_mul S (fun p hp => hC_meas p hp)]

    rw [hS_def, Finset.prod_biUnion hT_disj]

    apply Finset.prod_congr rfl
    intro i hi
    simp only [T]
    rw [Finset.prod_pair (show ((i, j₁) : Fin n × Fin d) ≠ (i, j₂) from by
      simp [Prod.ext_iff, hne])]
    simp only [C, show j₁ = j₁ from rfl, ite_true,
      show (j₂ = j₁) = False from propext ⟨fun h => hne h.symm, False.elim⟩,
      ite_false, show j₂ = j₂ from rfl]
    exact (hf_prod i hi).symm

/-- Each entry of an i.i.d. Rademacher matrix is a measurable function of `ω`. -/
theorem rademacher_entry_measurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    (hIID : IsIIDRademacherMatrix X μ)
    (i : Fin n) (j : Fin d) :
    Measurable (fun ω => X ω i j) :=
  hIID.2.2 i j

/-- The mean of the Rademacher distribution is zero. -/
lemma rademacher_integral_zero : ∫ x, x ∂rademacherMeasure = 0 := by
  simp only [rademacherMeasure]
  have h1 : Integrable (fun x : ℝ => x) ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h2 : Integrable (fun x : ℝ => x) ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  rw [integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
  simp

/-- A measurable function whose pushforward equals the Rademacher distribution has
integral zero. -/
lemma rademacher_entry_integral_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f)
    (hmap : Measure.map f μ = rademacherMeasure) :
    ∫ ω, f ω ∂μ = 0 := by
  have h := integral_map hf.aemeasurable (f := id)
    (by rw [hmap]; exact aestronglyMeasurable_id)
  simp only [id] at h
  rw [← h, hmap]
  exact rademacher_integral_zero

/-- For an i.i.d. Rademacher matrix and `j₁ ≠ j₂`, the product `X ω i j₁ · X ω i j₂` has
mean zero. -/
theorem rademacher_product_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    (hIID : IsIIDRademacherMatrix X μ)
    (i : Fin n) (j₁ j₂ : Fin d) (hne : j₁ ≠ j₂) :
    ∫ ω, X ω i j₁ * X ω i j₂ ∂μ = 0 := by

  have hindep : IndepFun (fun ω => X ω i j₁) (fun ω => X ω i j₂) μ :=
    hIID.1.indepFun (show ((i, j₁) : Fin n × Fin d) ≠ (i, j₂) from by
      simp [Prod.ext_iff, hne])

  have hm₁ := hIID.2.2 i j₁
  have hm₂ := hIID.2.2 i j₂

  rw [hindep.integral_fun_mul_eq_mul_integral
    hm₁.aestronglyMeasurable hm₂.aestronglyMeasurable]

  rw [rademacher_entry_integral_zero hm₁ (hIID.2.1 i j₁),
      rademacher_entry_integral_zero hm₂ (hIID.2.1 i j₂)]
  ring

/-- Per-pair Hoeffding bound: for distinct columns `j₁ ≠ j₂` of an i.i.d. Rademacher
matrix, `P(|(XᵀX)_{j₁ j₂}/n| > t) ≤ 2 exp(-n t² / 2)`. -/
lemma hoeffding_per_pair_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} (hn : 0 < n)
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    (hRad : ∀ ω, ∀ i : Fin n, ∀ j : Fin d, X ω i j = 1 ∨ X ω i j = -1)
    (hIID : IsIIDRademacherMatrix X μ)
    (j₁ j₂ : Fin d) (hne : j₁ ≠ j₂) (t : ℝ) (ht : 0 < t) :
    μ {ω | t < |((X ω)ᵀ * X ω) j₁ j₂ / (n : ℝ)|} ≤
      ENNReal.ofReal (2 * exp (-(↑n * t ^ 2 / 2))) := by

  set ξ : Fin n → Ω → ℝ := fun i ω => X ω i j₁ * X ω i j₂ with hξ_def

  set a : Fin n → ℝ := fun _ => -1
  set b : Fin n → ℝ := fun _ => 1
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn

  have hentry : ∀ ω, ((X ω)ᵀ * X ω) j₁ j₂ = ∑ i : Fin n, ξ i ω := by
    intro ω; simp only [Matrix.transpose_apply, Matrix.mul_apply]; rfl

  have hab : ∀ i, a i < b i := fun _ => by norm_num
  have hξ_meas : ∀ i, Measurable (ξ i) := fun i =>
    (rademacher_entry_measurable X hIID i j₁).mul (rademacher_entry_measurable X hIID i j₂)
  have hξ_int : ∀ i, Integrable (ξ i) μ := by
    intro i
    apply Integrable.mono' (g := fun _ => (1:ℝ)) (integrable_const 1)
      (hξ_meas i).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs, ξ]
      rcases hRad ω i j₁ with h1 | h1 <;> rcases hRad ω i j₂ with h2 | h2 <;> simp [h1, h2]
  have hξ_lo : ∀ i, ∀ᵐ ω ∂μ, a i ≤ ξ i ω := fun i =>
    Filter.Eventually.of_forall fun ω => by
      simp only [a, ξ]
      rcases hRad ω i j₁ with h1 | h1 <;> rcases hRad ω i j₂ with h2 | h2 <;> simp [h1, h2]
  have hξ_hi : ∀ i, ∀ᵐ ω ∂μ, ξ i ω ≤ b i := fun i =>
    Filter.Eventually.of_forall fun ω => by
      simp only [b, ξ]
      rcases hRad ω i j₁ with h1 | h1 <;> rcases hRad ω i j₂ with h2 | h2 <;> simp [h1, h2]
  have hξ_mean : ∀ i, ∫ ω, ξ i ω ∂μ = 0 := fun i =>
    rademacher_product_mean_zero X hIID i j₁ j₂ hne
  have hξ_indep : iIndepFun ξ μ := rademacher_product_iIndepFun X hIID j₁ j₂ hne

  have hexp_eq : 2 * ((n : ℝ) * t) ^ 2 / (∑ i : Fin n, (b i - a i) ^ 2) =
      (n : ℝ) * t ^ 2 / 2 := by
    simp [a, b, Finset.sum_const]
    field_simp; ring

  have hset_sub : {ω | t < |((X ω)ᵀ * X ω) j₁ j₂ / (n : ℝ)|} ⊆
      {ω | ∑ i, ξ i ω > ↑n * t} ∪ {ω | ∑ i, ξ i ω < -(↑n * t)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rw [hentry, abs_div, abs_of_pos hn_pos] at hω
    rw [lt_div_iff₀ hn_pos] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq, gt_iff_lt]
    rw [lt_abs] at hω
    rcases hω with h | h
    · left; linarith
    · right; linarith

  have hnt_pos : (0 : ℝ) < ↑n * t := mul_pos hn_pos ht
  have hupper := hoeffding_sum_upper_tail hab hξ_meas hξ_int hξ_lo hξ_hi hξ_mean hξ_indep
    (↑n * t) hnt_pos
  have hlower := hoeffding_sum_lower_tail hab hξ_meas hξ_int hξ_lo hξ_hi hξ_mean hξ_indep
    (↑n * t) hnt_pos

  rw [hexp_eq] at hupper hlower
  calc μ {ω | t < |((X ω)ᵀ * X ω) j₁ j₂ / (n : ℝ)|}
      ≤ μ ({ω | ∑ i, ξ i ω > ↑n * t} ∪ {ω | ∑ i, ξ i ω < -(↑n * t)}) :=
        measure_mono hset_sub
    _ ≤ μ {ω | ∑ i, ξ i ω > ↑n * t} + μ {ω | ∑ i, ξ i ω < -(↑n * t)} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (exp (-(↑n * t ^ 2 / 2))) +
        ENNReal.ofReal (exp (-(↑n * t ^ 2 / 2))) := add_le_add hupper hlower
    _ = ENNReal.ofReal (2 * exp (-(↑n * t ^ 2 / 2))) := by
        rw [← ENNReal.ofReal_add (exp_nonneg _) (exp_nonneg _)]
        ring_nf

/-- `XᵀX` is symmetric: `(XᵀX) i j = (XᵀX) j i`. -/
lemma transpose_mul_self_symm {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (i j : Fin d) :
    (Xᵀ * X) i j = (Xᵀ * X) j i := by
  simp [Matrix.mul_apply, Matrix.transpose_apply]; congr 1; ext k; ring

/-- Refinement of `inc_compl_subset_offDiag_union`: by symmetry it suffices to take the
union only over the strict upper triangle of index pairs `(i, j)` with `i < j`. -/
lemma inc_compl_subset_upperTriangle_union {Ω : Type*} [MeasurableSpace Ω]
    {n d k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    (hRad : ∀ ω, ∀ i : Fin n, ∀ j : Fin d, X ω i j = 1 ∨ X ω i j = -1) :
    {ω | AssumptionINC (X ω) k}ᶜ ⊆
    ⋃ p ∈ (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 < p.2),
      {ω | 1 / (14 * (k : ℝ)) < |((X ω)ᵀ * X ω) p.1 p.2 / (n : ℝ)|} := by
  intro ω hω
  have h := inc_compl_subset_offDiag_union hn hk X hRad hω
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  obtain ⟨⟨i, j⟩, hne, hbad⟩ := h
  simp only at hne hbad

  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ⟨⟨i, j⟩, hij, hbad⟩
  · refine ⟨⟨j, i⟩, hji, ?_⟩
    simp only [Set.mem_setOf_eq] at hbad ⊢
    rw [transpose_mul_self_symm (X ω) j i]; exact hbad

/-- The strict upper triangle of `Fin d × Fin d` has cardinality at most `d² / 2`,
i.e. `2 · |{(i,j) : i < j}| ≤ d²`. -/
lemma card_upperTriangle_le (d : ℕ) :
    2 * ((Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 < p.2)).card ≤ d ^ 2 := by
  set T := (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 < p.2) with hT_def
  set L := (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.2 < p.1) with hL_def
  have hTL_disj : Disjoint T L := by
    rw [hT_def, hL_def, Finset.disjoint_filter]
    intro p _ h1 h2; exact absurd (lt_trans h1 h2) (lt_irrefl _)
  have hcard_sum : T.card + L.card ≤ d ^ 2 := by
    rw [← Finset.card_union_of_disjoint hTL_disj]
    calc (T ∪ L).card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = d * d := by simp [Fintype.card_prod, Fintype.card_fin]
      _ = d ^ 2 := by ring
  have hcard_eq : T.card = L.card := by
    apply Finset.card_equiv (Equiv.prodComm (Fin d) (Fin d))
    intro ⟨a, b⟩; simp [hT_def, hL_def, Equiv.prodComm]
  linarith

/-- Hoeffding-style union bound for i.i.d. Rademacher matrices: the probability that
`INC(k)` fails is at most `d² · exp(-n (1/(14k))² / 2)`. -/
theorem hoeffding_union_bound_for_rademacher
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d k : ℕ} (hn : 0 < n) (_hd : 2 ≤ d) (hk : 0 < k)
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    (hRad : ∀ ω, ∀ i : Fin n, ∀ j : Fin d, X ω i j = 1 ∨ X ω i j = -1)
    (hIID : IsIIDRademacherMatrix X μ)
    (_hMeas : MeasurableSet {ω | AssumptionINC (X ω) k}) :
    μ {ω | AssumptionINC (X ω) k}ᶜ ≤
      ENNReal.ofReal ((d : ℝ) ^ 2 * exp (-((n : ℝ) * (1 / (14 * (k : ℝ))) ^ 2 / 2))) := by
  set t := 1 / (14 * (k : ℝ)) with ht_def
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have ht_pos : (0 : ℝ) < t := by positivity
  have hexp_nn : (0 : ℝ) ≤ exp (-(↑n * t ^ 2 / 2)) := exp_nonneg _

  set T := (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 < p.2)

  have hsub := inc_compl_subset_upperTriangle_union hn hk X hRad

  calc μ {ω | AssumptionINC (X ω) k}ᶜ
      ≤ μ (⋃ p ∈ T, {ω | t < |((X ω)ᵀ * X ω) p.1 p.2 / (n : ℝ)|}) :=
        measure_mono hsub
    _ ≤ ∑ p ∈ T, μ {ω | t < |((X ω)ᵀ * X ω) p.1 p.2 / (n : ℝ)|} :=
        measure_biUnion_finset_le T _
    _ ≤ ∑ p ∈ T, ENNReal.ofReal (2 * exp (-(↑n * t ^ 2 / 2))) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
        exact hoeffding_per_pair_bound hn X hRad hIID p.1 p.2 (ne_of_lt hp') t ht_pos
    _ = T.card • ENNReal.ofReal (2 * exp (-(↑n * t ^ 2 / 2))) :=
        Finset.sum_const _
    _ ≤ ENNReal.ofReal ((d : ℝ) ^ 2 * exp (-(↑n * t ^ 2 / 2))) := by

        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast (n := T.card),
            ← ENNReal.ofReal_mul (Nat.cast_nonneg T.card)]
        apply ENNReal.ofReal_le_ofReal
        have h2card := card_upperTriangle_le d
        calc (T.card : ℝ) * (2 * exp (-(↑n * t ^ 2 / 2)))
            = (2 * T.card : ℕ) * exp (-(↑n * t ^ 2 / 2)) := by push_cast; ring
          _ ≤ (d ^ 2 : ℕ) * exp (-(↑n * t ^ 2 / 2)) := by
              apply mul_le_mul_of_nonneg_right _ hexp_nn
              exact Nat.cast_le.mpr h2card
          _ = (d : ℝ) ^ 2 * exp (-(↑n * t ^ 2 / 2)) := by push_cast; ring

/-- Tail bound on incoherence failure for i.i.d. Rademacher matrices, restated as a
named theorem for use in Proposition 2.16. -/
theorem rademacher_incoherence_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d k : ℕ} (hn : 0 < n) (hd : 2 ≤ d) (hk : 0 < k)
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)

    (hRad : ∀ ω, ∀ i : Fin n, ∀ j : Fin d, X ω i j = 1 ∨ X ω i j = -1)

    (hIID : IsIIDRademacherMatrix X μ)

    (hMeas : MeasurableSet {ω | AssumptionINC (X ω) k}) :
    μ {ω | AssumptionINC (X ω) k}ᶜ ≤
      ENNReal.ofReal ((d : ℝ) ^ 2 * exp (-((n : ℝ) * (1 / (14 * (k : ℝ))) ^ 2 / 2))) :=
  hoeffding_union_bound_for_rademacher hn hd hk X hRad hIID hMeas

/-- If `P(Sᶜ) ≤ δ` and `S` is measurable, then `P(S) ≥ 1 - δ`. -/
lemma prob_ge_of_compl_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S)
    {δ : ℝ} (h : μ Sᶜ ≤ ENNReal.ofReal δ)
    (hδ : 0 ≤ δ) :
    μ S ≥ ENNReal.ofReal (1 - δ) := by
  rw [ge_iff_le, ENNReal.ofReal_sub _ hδ, ENNReal.ofReal_one]
  have hfin : μ Sᶜ ≠ ⊤ := measure_ne_top μ Sᶜ
  have hsum : μ S + μ Sᶜ = 1 := by
    rw [measure_add_measure_compl hS]; exact measure_univ
  rw [← (ENNReal.eq_sub_of_add_eq hfin hsum).symm]
  exact tsub_le_tsub_left h 1

/-- Quantitative tail bound for Proposition 2.16: if
`n ≥ 392 k² (log(1/δ) + 2 log d)`, then `d² exp(-n (1/(14k))² / 2) ≤ δ`. -/
lemma prop216_tail_bound_le_delta (n d k : ℕ) (hk : 0 < k) (hd : 2 ≤ d)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hn : (n : ℝ) ≥ 392 * (k : ℝ) ^ 2 * (Real.log (1 / δ) + 2 * Real.log (d : ℝ))) :
    (d : ℝ) ^ 2 * exp (-((n : ℝ) * (1 / (14 * (k : ℝ))) ^ 2 / 2)) ≤ δ := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have h392 : (0 : ℝ) < 392 * (k : ℝ) ^ 2 := by positivity

  have hsimp : (n : ℝ) * (1 / (14 * (k : ℝ))) ^ 2 / 2 =
      (n : ℝ) / (392 * (k : ℝ) ^ 2) := by field_simp; ring
  rw [hsimp]

  have hdiv : (n : ℝ) / (392 * (k : ℝ) ^ 2) ≥
      Real.log (1 / δ) + 2 * Real.log (d : ℝ) := by
    rw [ge_iff_le, le_div_iff₀ h392]; linarith

  have hexp : exp (-((n : ℝ) / (392 * (k : ℝ) ^ 2))) ≤
      exp (-(Real.log (1 / δ) + 2 * Real.log (d : ℝ))) :=
    exp_le_exp.mpr (neg_le_neg_iff.mpr hdiv.le)

  have hval : exp (-(Real.log (1 / δ) + 2 * Real.log (d : ℝ))) =
      δ / (d : ℝ) ^ 2 := by
    rw [neg_add, exp_add]
    have h1 : exp (-Real.log (1 / δ)) = δ := by
      rw [Real.log_div (by linarith) (by linarith), Real.log_one, zero_sub,
          neg_neg, Real.exp_log hδ₀]
    have h2 : exp (-(2 * Real.log (d : ℝ))) = ((d : ℝ) ^ 2)⁻¹ := by
      rw [show 2 * Real.log (d : ℝ) = Real.log ((d : ℝ) ^ 2) by
        rw [Real.log_pow]; norm_num]
      rw [Real.exp_neg, Real.exp_log hd2_pos]
    rw [h1, h2]; ring

  calc (d : ℝ) ^ 2 * exp (-((n : ℝ) / (392 * (k : ℝ) ^ 2)))
      ≤ (d : ℝ) ^ 2 * (δ / (d : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hd2_pos.le; linarith
    _ = δ := by field_simp

/-- Proposition 2.16. A Rademacher random matrix satisfies the incoherence condition
`INC(k)` with probability at least `1 - δ` whenever
`n ≥ 392 k² log(1/δ) + 784 k² log d`. -/
theorem prop_2_16_rademacher_incoherence
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d k : ℕ} (hk : 0 < k) (hd : 2 ≤ d) (hn : 0 < n)
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)

    (hRad : ∀ ω, ∀ i : Fin n, ∀ j : Fin d, X ω i j = 1 ∨ X ω i j = -1)

    (hIID : IsIIDRademacherMatrix X μ)

    (hMeasINC : MeasurableSet {ω | AssumptionINC (X ω) k})

    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)

    (hn_large : (n : ℝ) ≥ 392 * (k : ℝ) ^ 2 *
      (Real.log (1 / δ) + 2 * Real.log (d : ℝ))) :
    μ {ω | AssumptionINC (X ω) k} ≥ ENNReal.ofReal (1 - δ) := by

  have htail : μ {ω | AssumptionINC (X ω) k}ᶜ ≤
      ENNReal.ofReal ((d : ℝ) ^ 2 * exp (-((n : ℝ) * (1 / (14 * (k : ℝ))) ^ 2 / 2))) :=
    rademacher_incoherence_tail_bound hn hd hk X hRad hIID hMeasINC

  have hanalytic : (d : ℝ) ^ 2 * exp (-((n : ℝ) * (1 / (14 * (k : ℝ))) ^ 2 / 2)) ≤ δ :=
    prop216_tail_bound_le_delta n d k hk hd δ hδ₀ hδ₁ hn_large

  apply prob_ge_of_compl_le hMeasINC _ hδ₀.le
  calc μ {ω | AssumptionINC (X ω) k}ᶜ
      ≤ ENNReal.ofReal ((d : ℝ) ^ 2 * exp (-((n : ℝ) * (1 / (14 * (k : ℝ))) ^ 2 / 2))) :=
        htail
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hanalytic

/-- The fair coin distribution on `Fin 2`, used to model a single Rademacher bit. -/
noncomputable def coinMeasure : Measure (Fin 2) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (0 : Fin 2) + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (1 : Fin 2)

/-- The fair coin distribution is a probability measure. -/
instance coinMeasure_prob : IsProbabilityMeasure coinMeasure := by
  refine ⟨?_⟩
  simp [coinMeasure, Measure.add_apply, Measure.smul_apply]
  simp only [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- Map `Fin 2 → ℝ` sending the bit `0` to `-1` and `1` to `+1`; converts a coin flip
into a Rademacher sign. -/
def coinToSign : Fin 2 → ℝ := fun b => if b = 0 then -1 else 1

/-- The coin-to-sign map is measurable (its domain is finite). -/
lemma measurable_coinToSign : Measurable coinToSign := measurable_of_finite _

/-- The pushforward of `coinMeasure` under `coinToSign` is the Rademacher distribution. -/
lemma map_coinToSign_eq_rademacher :
    Measure.map coinToSign coinMeasure = rademacherMeasure := by
  simp only [coinMeasure, rademacherMeasure]
  rw [Measure.map_add _ _ measurable_coinToSign, Measure.map_smul, Measure.map_smul,
      Measure.map_dirac, Measure.map_dirac]
  simp [coinToSign]
  exact add_comm _ _

/-- Existence of an i.i.d. Rademacher matrix space: there is a probability space carrying
an `n × d` random matrix `X` with `±1` entries that is i.i.d. Rademacher and for which the
event `{INC(k)}` is measurable for every `k`. -/
theorem exists_iid_rademacher_space (n d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : Ω → Matrix (Fin n) (Fin d) ℝ),
      (∀ ω, ∀ i : Fin n, ∀ j : Fin d, X ω i j = 1 ∨ X ω i j = -1) ∧
      IsIIDRademacherMatrix X μ ∧
      ∀ k : ℕ, MeasurableSet {ω | AssumptionINC (X ω) k} := by
  refine ⟨(Fin n × Fin d) → Fin 2, inferInstance,
    Measure.pi (fun _ : Fin n × Fin d => coinMeasure),
    inferInstance,
    fun ω => Matrix.of (fun i j => coinToSign (ω (i, j))),
    ?_, ?_, ?_⟩
  ·
    intro ω i j
    simp only [Matrix.of_apply, coinToSign]
    split
    · right; rfl
    · left; rfl
  ·
    constructor
    ·
      exact iIndepFun_pi (ι := Fin n × Fin d) (Ω := fun _ => Fin 2)
        (𝓧 := fun _ => ℝ) (X := fun _ => coinToSign) (μ := fun _ => coinMeasure)
        (fun _ => measurable_coinToSign.aemeasurable)
    · constructor
      ·
        intro i j
        exact (MeasurePreserving.comp
          (⟨measurable_coinToSign, map_coinToSign_eq_rademacher⟩ :
            MeasurePreserving coinToSign coinMeasure rademacherMeasure)
          (measurePreserving_eval (fun _ : Fin n × Fin d => coinMeasure) (i, j))).map_eq
      ·
        intro i j
        simp only [Matrix.of_apply]
        exact measurable_coinToSign.comp (measurable_pi_apply (i, j))

  ·
    intro k
    have heq : {ω : (Fin n × Fin d) → Fin 2 |
        AssumptionINC (Matrix.of (fun i j => coinToSign (ω (i, j)))) k} =
      ⋂ i : Fin d, ⋂ j : Fin d, {ω |
        |((Matrix.of (fun a b => coinToSign (ω (a, b))))ᵀ *
          (Matrix.of (fun a b => coinToSign (ω (a, b))))) i j / (n : ℝ) -
          if i = j then 1 else 0| ≤ 1 / (14 * (k : ℝ))} := by
      ext ω; simp [AssumptionINC, Set.mem_iInter]
    rw [heq]
    apply MeasurableSet.iInter; intro i
    apply MeasurableSet.iInter; intro j
    apply measurableSet_le
    · apply Measurable.abs
      apply Measurable.sub
      · apply Measurable.div_const
        simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.of_apply]
        apply Finset.measurable_sum
        intro a _
        exact (measurable_coinToSign.comp (measurable_pi_apply (a, i))).mul
          (measurable_coinToSign.comp (measurable_pi_apply (a, j)))
      · exact measurable_const
    · exact measurable_const
