/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Process.Stopping
import Atlas.TheoryOfProbability.code.StoppingTime

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
variable {S : Type*} [MeasurableSpace S]

/-- The **post-stopping-time sequence** `(X_{T+k+1})_{k ≥ 0}` obtained from a sequence
`X : ℕ → Ω → S` by shifting the index by `T(ω) + 1`. This is the sequence of observations
immediately after the stopping time `T`. -/
def postStoppingTimeSeq (X : ℕ → Ω → S) (T : Ω → ℕ) : ℕ → Ω → S :=
  fun k ω => X (T ω + k + 1) ω

/-- For an identically distributed sequence, the shifted variable `X (n + k + 1)` has the
same distribution as `X 0`. -/
lemma identDistrib_tail {X : ℕ → Ω → S}
    (hX_id : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (n k : ℕ) :
    IdentDistrib (X (n + k + 1)) (X 0) μ μ :=
  hX_id (n + k + 1) 0

/-- Key independence lemma: the event `{T = n}` (which lies in `F_n`) is independent of the
preimage `(X_{n+k+1})⁻¹(A)` (which depends on a strictly later index), since the underlying
sequence is independent. -/
lemma indep_stopping_time_tail
    (X : ℕ → Ω → S) (f : Filtration ℕ m) (T : Ω → ℕ)
    (hX_ind : iIndepFun (m := fun _ => ‹MeasurableSpace S›) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hT : IsStoppingTime f (fun ω => (T ω : ℕ∞)))
    (hfX : ∀ n, f n ≤ ⨆ i ∈ Finset.range (n + 1), MeasurableSpace.comap (X i) ‹MeasurableSpace S›)
    [IsProbabilityMeasure μ]
    (n k : ℕ) (A : Set S) (hA : MeasurableSet A) :
    μ ({ω | T ω = n} ∩ (X (n + k + 1)) ⁻¹' A) =
      μ {ω | T ω = n} * μ ((X (n + k + 1)) ⁻¹' A) := by
  set m' : ℕ → MeasurableSpace Ω := fun i => MeasurableSpace.comap (X i) ‹MeasurableSpace S›
  have hle : ∀ i, m' i ≤ m := fun i => MeasurableSpace.comap_le_iff_le_map.mpr (hX_meas i)

  have hST : Disjoint (Set.Iic n) ({n + k + 1} : Set ℕ) := by
    simp only [Set.disjoint_left, Set.mem_Iic, Set.mem_singleton_iff]
    intro x hx hxT; omega

  have hindep : Indep (⨆ i ∈ Set.Iic n, m' i) (⨆ i ∈ ({n + k + 1} : Set ℕ), m' i) μ :=
    indep_iSup_of_disjoint hle hX_ind hST

  have hTn_meas : @MeasurableSet Ω (⨆ i ∈ Set.Iic n, m' i) {ω | T ω = n} := by
    have h1 : @MeasurableSet Ω (f n) {ω : Ω | T ω = n} := by
      have : {ω : Ω | T ω = n} = {ω : Ω | (T ω : ℕ∞) = ↑n} := by ext ω; simp [Nat.cast_inj]
      rw [this]; exact hT.measurableSet_eq n
    have h3 : (⨆ i ∈ Finset.range (n + 1), m' i) ≤ (⨆ i ∈ Set.Iic n, m' i) := by
      apply biSup_mono
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Set.mem_Iic]; omega
    exact h3 _ (hfX n _ h1)

  have hA_meas : @MeasurableSet Ω (⨆ i ∈ ({n + k + 1} : Set ℕ), m' i) (X (n + k + 1) ⁻¹' A) := by
    have hle' : m' (n + k + 1) ≤ ⨆ i ∈ ({n + k + 1} : Set ℕ), m' i :=
      le_biSup (f := m') (Set.mem_singleton _)
    have hcomap : @MeasurableSet Ω (m' (n + k + 1)) (X (n + k + 1) ⁻¹' A) := by
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨A, hA, rfl⟩
    exact hle' _ hcomap

  exact (hindep.indepSet_of_measurableSet hTn_meas hA_meas).measure_inter_eq_mul

/-- The level set `{ω | T(ω) = n}` of a stopping time `T` is measurable in the ambient
σ-algebra. -/
lemma measurableSet_stoppingTime_eq {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : ℕ∞))) (n : ℕ) :
    MeasurableSet {ω | T ω = n} := by
  have h := hT.measurableSet_eq n
  have : {ω : Ω | T ω = n} = {ω : Ω | (T ω : ℕ∞) = ↑n} := by ext ω; simp [Nat.cast_inj]
  rw [this]; exact (f.le n) _ h

/-- The post-stopping-time sequence `postStoppingTimeSeq X T k` is almost-everywhere
measurable whenever each `X i` is and `T` is a stopping time. -/
lemma aemeasurable_postStoppingTimeSeq
    {X : ℕ → Ω → S} {f : Filtration ℕ m} {T : Ω → ℕ}
    (hX_aem : ∀ i, AEMeasurable (X i) μ)
    (hT : IsStoppingTime f (fun ω => (T ω : ℕ∞)))
    (k : ℕ) :
    AEMeasurable (postStoppingTimeSeq X T k) μ := by
  show AEMeasurable (fun ω => X (T ω + k + 1) ω) μ
  set X' : ℕ → Ω → S := fun i => (hX_aem i).mk (X i)
  have hX'_meas : ∀ i, Measurable (X' i) := fun i => (hX_aem i).measurable_mk
  have hT_meas : Measurable T := by
    apply measurable_to_countable; intro ω
    show MeasurableSet (T ⁻¹' {T ω})
    have : T ⁻¹' {T ω} = {ω' : Ω | T ω' = T ω} := by ext ω'; simp
    rw [this]; exact measurableSet_stoppingTime_eq hT (T ω)
  have h_meas : Measurable (fun ω => X' (T ω + k + 1) ω) := by
    intro s hs
    have decomp : (fun ω => X' (T ω + k + 1) ω) ⁻¹' s =
        ⋃ n, {ω | T ω = n} ∩ (X' (n + k + 1)) ⁻¹' s := by
      ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨T ω, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
    rw [decomp]
    exact MeasurableSet.iUnion fun n =>
      (hT_meas (MeasurableSet.singleton n)).inter (hX'_meas (n + k + 1) hs)
  refine ⟨fun ω => X' (T ω + k + 1) ω, h_meas, ?_⟩
  have hall : ∀ᵐ ω ∂μ, ∀ i : ℕ, X i ω = X' i ω := ae_all_iff.mpr fun i => (hX_aem i).ae_eq_mk
  filter_upwards [hall] with ω hω
  exact hω (T ω + k + 1)

/-- **Strong Markov property (identically-distributed part).**

For an i.i.d. sequence `X : ℕ → Ω → S` and a finite stopping time `T`, each variable
`postStoppingTimeSeq X T k = X_{T+k+1}` has the same distribution as `X 0`. -/
theorem strong_markov_iid_identDistrib
    {X : ℕ → Ω → S} {f : Filtration ℕ m} {T : Ω → ℕ}
    (hX_id : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_ind : iIndepFun (m := fun _ => ‹MeasurableSpace S›) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hT : IsStoppingTime f (fun ω => (T ω : ℕ∞)))
    (hfX : ∀ n, f n ≤ ⨆ i ∈ Finset.range (n + 1), MeasurableSpace.comap (X i) ‹MeasurableSpace S›)
    [IsProbabilityMeasure μ]
    (k : ℕ) :
    IdentDistrib (postStoppingTimeSeq X T k) (X 0) μ μ := by
  have haem := aemeasurable_postStoppingTimeSeq
    (fun i => (hX_id i 0).aemeasurable_fst) hT k
  refine ⟨haem, (hX_id 0 0).aemeasurable_fst, ?_⟩

  apply Measure.ext
  intro A hA
  rw [Measure.map_apply_of_aemeasurable haem hA,
      Measure.map_apply_of_aemeasurable (hX_id 0 0).aemeasurable_fst hA]

  show μ ((fun ω => X (T ω + k + 1) ω) ⁻¹' A) = μ ((X 0) ⁻¹' A)

  have decomp : (fun ω => X (T ω + k + 1) ω) ⁻¹' A =
      ⋃ n, {ω | T ω = n} ∩ (X (n + k + 1)) ⁻¹' A := by
    ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨T ω, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
  rw [decomp]

  have hdisj : Pairwise (Function.onFun Disjoint
      (fun n => {ω | T ω = n} ∩ (X (n + k + 1)) ⁻¹' A)) := by
    intro i j hij
    simp only [Function.onFun, Set.disjoint_left, Set.mem_inter_iff, Set.mem_setOf_eq]
    intro ω ⟨hi, _⟩ ⟨hj, _⟩; exact hij (hi.symm.trans hj)

  have hnull : ∀ n, NullMeasurableSet
      ({ω | T ω = n} ∩ (X (n + k + 1)) ⁻¹' A) μ := by
    intro n
    exact ((measurableSet_stoppingTime_eq hT n).nullMeasurableSet).inter
      ((hX_meas (n + k + 1) hA).nullMeasurableSet)

  rw [measure_iUnion₀ (fun i j hij => (hdisj hij).aedisjoint) hnull]

  have key : ∀ n, μ ({ω | T ω = n} ∩ (X (n + k + 1)) ⁻¹' A) =
      μ {ω | T ω = n} * μ ((X 0) ⁻¹' A) := by
    intro n
    have h1 := indep_stopping_time_tail X f T hX_ind hX_meas hT hfX n k A hA
    have h2 := (identDistrib_tail hX_id n k).measure_preimage_eq hA
    rw [h1, h2]
  simp_rw [key, ENNReal.tsum_mul_right]

  have hsum : ∑' n, μ {ω | T ω = n} = 1 := by
    rw [← measure_iUnion (fun i j hij => by
      simp only [Function.onFun, Set.disjoint_left, Set.mem_setOf_eq]
      intro ω hi hj; exact hij (hi.symm.trans hj))
      (fun n => measurableSet_stoppingTime_eq hT n)]
    have : ⋃ n, {ω : Ω | T ω = n} = Set.univ := by ext ω; simp [Set.mem_iUnion]
    rw [this]; exact measure_univ
  rw [hsum, one_mul]

/-- Finite-family version of `indep_stopping_time_tail`: on `{T = n}`, the intersection of
preimages `⋂_{k ∈ SF} X_{n+k+1}⁻¹(sets k)` is independent of `{T = n}` and the joint
probability splits as a product. -/
lemma indep_stopping_time_tail_finset
    (X : ℕ → Ω → S) (f : Filtration ℕ m) (T : Ω → ℕ)
    (hX_ind : iIndepFun (m := fun _ => ‹MeasurableSpace S›) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hT : IsStoppingTime f (fun ω => (T ω : ℕ∞)))
    (hfX : ∀ n, f n ≤ ⨆ i ∈ Finset.range (n + 1), MeasurableSpace.comap (X i) ‹MeasurableSpace S›)
    [IsProbabilityMeasure μ]
    (n : ℕ) (SF : Finset ℕ) (sets : ℕ → Set S) (hsets : ∀ k ∈ SF, MeasurableSet (sets k)) :
    μ ({ω | T ω = n} ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' sets k) =
      μ {ω | T ω = n} * ∏ k ∈ SF, μ ((X (n + k + 1)) ⁻¹' sets k) := by
  set m' : ℕ → MeasurableSpace Ω := fun i => MeasurableSpace.comap (X i) ‹MeasurableSpace S›
  have hle : ∀ i, m' i ≤ m := fun i => MeasurableSpace.comap_le_iff_le_map.mpr (hX_meas i)
  set g : ℕ → ℕ := fun k => n + k + 1
  have hST : Disjoint (Set.Iic n) (↑(SF.image g) : Set ℕ) := by
    simp only [Set.disjoint_left, Set.mem_Iic, Finset.coe_image, Set.mem_image, g]
    intro x hx ⟨k, _, hk⟩; omega
  have hindep : Indep (⨆ i ∈ Set.Iic n, m' i) (⨆ i ∈ (↑(SF.image g) : Set ℕ), m' i) μ :=
    indep_iSup_of_disjoint hle hX_ind hST
  have hTn_meas : @MeasurableSet Ω (⨆ i ∈ Set.Iic n, m' i) {ω | T ω = n} := by
    have h1 : @MeasurableSet Ω (f n) {ω : Ω | T ω = n} := by
      have : {ω : Ω | T ω = n} = {ω : Ω | (T ω : ℕ∞) = ↑n} := by ext ω; simp [Nat.cast_inj]
      rw [this]; exact hT.measurableSet_eq n
    have h3 : (⨆ i ∈ Finset.range (n + 1), m' i) ≤ (⨆ i ∈ Set.Iic n, m' i) := by
      apply biSup_mono; intro i hi
      simp only [Finset.mem_range] at hi; simp only [Set.mem_Iic]; omega
    exact h3 _ (hfX n _ h1)
  have hB_meas : @MeasurableSet Ω (⨆ i ∈ (↑(SF.image g) : Set ℕ), m' i)
      (⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' sets k) := by
    apply MeasurableSet.biInter (Finset.countable_toSet SF)
    intro k hk
    have hmem : g k ∈ SF.image g := Finset.mem_image_of_mem g hk
    have hle' : m' (g k) ≤ ⨆ i ∈ (↑(SF.image g) : Set ℕ), m' i :=
      le_biSup (f := m') (Finset.mem_coe.mpr hmem)
    apply hle'; rw [MeasurableSpace.measurableSet_comap]
    exact ⟨sets k, hsets k hk, rfl⟩
  rw [(hindep.indepSet_of_measurableSet hTn_meas hB_meas).measure_inter_eq_mul]
  congr 1
  have htail : iIndepFun (m := fun _ => ‹MeasurableSpace S›) (fun k => X (n + k + 1)) μ := by
    have hinj : Function.Injective g := by intro a b h; simp only [g] at h; omega
    exact hX_ind.precomp hinj
  exact htail.measure_inter_preimage_eq_mul SF (fun k hk => hsets k hk)

/-- For each measurable set `A`, `μ((postStoppingTimeSeq X T k)⁻¹(A)) = μ((X 0)⁻¹(A))`,
i.e. the law of each `X_{T+k+1}` agrees with that of `X 0`. -/
lemma postStoppingTimeSeq_preimage_eq
    {X : ℕ → Ω → S} {f : Filtration ℕ m} {T : Ω → ℕ}
    (hX_id : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_ind : iIndepFun (m := fun _ => ‹MeasurableSpace S›) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hT : IsStoppingTime f (fun ω => (T ω : ℕ∞)))
    (hfX : ∀ n, f n ≤ ⨆ i ∈ Finset.range (n + 1), MeasurableSpace.comap (X i) ‹MeasurableSpace S›)
    [IsProbabilityMeasure μ]
    (k : ℕ) (A : Set S) (hA : MeasurableSet A) :
    μ ((postStoppingTimeSeq X T k) ⁻¹' A) = μ ((X 0) ⁻¹' A) := by
  have decomp : (postStoppingTimeSeq X T k) ⁻¹' A =
      ⋃ n, {ω | T ω = n} ∩ (X (n + k + 1)) ⁻¹' A := by
    ext ω
    simp only [postStoppingTimeSeq, Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    exact ⟨fun h => ⟨T ω, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
  rw [decomp]
  rw [measure_iUnion₀ (fun i j hij => (Disjoint.aedisjoint (by
    simp only [Set.disjoint_left, Set.mem_inter_iff, Set.mem_setOf_eq]
    intro ω ⟨hi, _⟩ ⟨hj, _⟩; exact hij (hi.symm.trans hj))))
    (fun n => ((measurableSet_stoppingTime_eq hT n).nullMeasurableSet).inter
      ((hX_meas (n + k + 1) hA).nullMeasurableSet))]
  have key : ∀ n, μ ({ω | T ω = n} ∩ (X (n + k + 1)) ⁻¹' A) =
      μ {ω | T ω = n} * μ ((X 0) ⁻¹' A) := by
    intro n
    rw [indep_stopping_time_tail X f T hX_ind hX_meas hT hfX n k A hA]
    congr 1; exact (hX_id (n + k + 1) 0).measure_preimage_eq hA
  simp_rw [key, ENNReal.tsum_mul_right]
  have hsum : ∑' n, μ {ω | T ω = n} = 1 := by
    rw [← measure_iUnion (fun i j hij => by
      simp only [Function.onFun, Set.disjoint_left, Set.mem_setOf_eq]
      intro ω hi hj; exact hij (hi.symm.trans hj))
      (fun n => measurableSet_stoppingTime_eq hT n)]
    have : ⋃ n, {ω : Ω | T ω = n} = Set.univ := by ext ω; simp [Set.mem_iUnion]
    rw [this]; exact measure_univ
  rw [hsum, one_mul]

/-- **Strong Markov property (independence part).**

For an i.i.d. sequence `X` and a finite stopping time `T`, the post-stopping sequence
`(X_{T+k+1})_{k ≥ 0}` is itself an independent family. -/
theorem strong_markov_iid_iIndepFun
    {X : ℕ → Ω → S} {f : Filtration ℕ m} {T : Ω → ℕ}
    (hX_id : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_ind : iIndepFun (m := fun _ => ‹MeasurableSpace S›) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hT : IsStoppingTime f (fun ω => (T ω : ℕ∞)))
    (hfX : ∀ n, f n ≤ ⨆ i ∈ Finset.range (n + 1), MeasurableSpace.comap (X i) ‹MeasurableSpace S›)
    [IsProbabilityMeasure μ] :
    iIndepFun (m := fun _ => ‹MeasurableSpace S›) (postStoppingTimeSeq X T) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro SF sets hsets

  have decomp : ⋂ k ∈ SF, (postStoppingTimeSeq X T k) ⁻¹' sets k =
      ⋃ n, {ω | T ω = n} ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' sets k := by
    ext ω
    simp only [postStoppingTimeSeq, Set.mem_iInter, Set.mem_preimage, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h; exact ⟨T ω, rfl, fun k hk => h k hk⟩
    · rintro ⟨n, hn, h⟩ k hk; rw [hn]; exact h k hk
  rw [decomp]

  have hdisj : Pairwise (Function.onFun Disjoint
      (fun n => {ω | T ω = n} ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' sets k)) := by
    intro i j hij
    simp only [Function.onFun, Set.disjoint_left, Set.mem_inter_iff, Set.mem_setOf_eq]
    intro ω ⟨hi, _⟩ ⟨hj, _⟩; exact hij (hi.symm.trans hj)

  have hnull : ∀ n, NullMeasurableSet
      ({ω | T ω = n} ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' sets k) μ := by
    intro n
    apply NullMeasurableSet.inter
    · exact (measurableSet_stoppingTime_eq hT n).nullMeasurableSet
    · exact (MeasurableSet.biInter (Finset.countable_toSet SF)
        (fun k hk => hX_meas (n + k + 1) (hsets k hk))).nullMeasurableSet

  rw [measure_iUnion₀ (fun i j hij => (hdisj hij).aedisjoint) hnull]

  have key : ∀ n, μ ({ω | T ω = n} ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' sets k) =
      μ {ω | T ω = n} * ∏ k ∈ SF, μ ((X 0) ⁻¹' sets k) := by
    intro n
    rw [indep_stopping_time_tail_finset X f T hX_ind hX_meas hT hfX n SF sets hsets]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    exact (hX_id (n + k + 1) 0).measure_preimage_eq (hsets k hk)
  simp_rw [key, ENNReal.tsum_mul_right]

  have hsum : ∑' n, μ {ω | T ω = n} = 1 := by
    rw [← measure_iUnion (fun i j hij => by
      simp only [Function.onFun, Set.disjoint_left, Set.mem_setOf_eq]
      intro ω hi hj; exact hij (hi.symm.trans hj))
      (fun n => measurableSet_stoppingTime_eq hT n)]
    have : ⋃ n, {ω : Ω | T ω = n} = Set.univ := by ext ω; simp [Set.mem_iUnion]
    rw [this]; exact measure_univ
  rw [hsum, one_mul]

  apply Finset.prod_congr rfl
  intro k hk
  exact (postStoppingTimeSeq_preimage_eq hX_id hX_ind hX_meas hT hfX k (sets k) (hsets k hk)).symm

/-- If `A` is measurable in the stopped σ-algebra `F_T`, then `A ∩ {T = n}` is measurable
in `F_n`. -/
lemma measurableSet_FT_inter_eq
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : ℕ∞)))
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A) (n : ℕ) :
    MeasurableSet[f n] (A ∩ {ω | T ω = n}) := by
  rw [hT.measurableSet] at hA
  obtain ⟨_, hA2⟩ := hA
  have heq : A ∩ {ω | T ω = n} = (A ∩ {ω | (T ω : ℕ∞) ≤ ↑n}) ∩ {ω | (T ω : ℕ∞) = ↑n} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro ⟨ha, htn⟩; exact ⟨⟨ha, by simp [htn]⟩, by simp [htn]⟩
    · intro ⟨⟨ha, _⟩, htn⟩; exact ⟨ha, by simp [Nat.cast_inj] at htn; exact htn⟩
  rw [heq]
  exact (hA2 n).inter (hT.measurableSet_eq n)

/-- Generalization of `indep_stopping_time_tail_finset`: any set `A ∈ F_n` is independent
of the finite intersection `⋂_{k ∈ SF} X_{n+k+1}⁻¹(sets k)`. -/
lemma indep_fn_tail_finset
    (X : ℕ → Ω → S) (f : Filtration ℕ m)
    (hX_ind : iIndepFun (m := fun _ => ‹MeasurableSpace S›) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hfX : ∀ n, f n ≤ ⨆ i ∈ Finset.range (n + 1), MeasurableSpace.comap (X i) ‹MeasurableSpace S›)
    [IsProbabilityMeasure μ]
    (n : ℕ) (A : Set Ω) (hA : MeasurableSet[f n] A)
    (SF : Finset ℕ) (sets : ℕ → Set S) (hsets : ∀ k ∈ SF, MeasurableSet (sets k)) :
    μ (A ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' sets k) =
      μ A * ∏ k ∈ SF, μ ((X (n + k + 1)) ⁻¹' sets k) := by
  set m' : ℕ → MeasurableSpace Ω := fun i => MeasurableSpace.comap (X i) ‹MeasurableSpace S›
  have hle : ∀ i, m' i ≤ m := fun i => MeasurableSpace.comap_le_iff_le_map.mpr (hX_meas i)
  set g : ℕ → ℕ := fun k => n + k + 1
  have hST : Disjoint (Set.Iic n) (↑(SF.image g) : Set ℕ) := by
    simp only [Set.disjoint_left, Set.mem_Iic, Finset.coe_image, Set.mem_image, g]
    intro x hx ⟨k, _, hk⟩; omega
  have hindep : Indep (⨆ i ∈ Set.Iic n, m' i) (⨆ i ∈ (↑(SF.image g) : Set ℕ), m' i) μ :=
    indep_iSup_of_disjoint hle hX_ind hST
  have hA_meas : @MeasurableSet Ω (⨆ i ∈ Set.Iic n, m' i) A := by
    have h3 : (⨆ i ∈ Finset.range (n + 1), m' i) ≤ (⨆ i ∈ Set.Iic n, m' i) := by
      apply biSup_mono; intro i hi
      simp only [Finset.mem_range] at hi; simp only [Set.mem_Iic]; omega
    exact h3 _ (hfX n _ hA)
  have hB_meas : @MeasurableSet Ω (⨆ i ∈ (↑(SF.image g) : Set ℕ), m' i)
      (⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' sets k) := by
    apply MeasurableSet.biInter (Finset.countable_toSet SF)
    intro k hk
    have hmem : g k ∈ SF.image g := Finset.mem_image_of_mem g hk
    have hle' : m' (g k) ≤ ⨆ i ∈ (↑(SF.image g) : Set ℕ), m' i :=
      le_biSup (f := m') (Finset.mem_coe.mpr hmem)
    apply hle'; rw [MeasurableSpace.measurableSet_comap]
    exact ⟨sets k, hsets k hk, rfl⟩
  rw [(hindep.indepSet_of_measurableSet hA_meas hB_meas).measure_inter_eq_mul]
  congr 1
  have htail : iIndepFun (m := fun _ => ‹MeasurableSpace S›) (fun k => X (n + k + 1)) μ := by
    have hinj : Function.Injective g := by intro a b h; simp only [g] at h; omega
    exact hX_ind.precomp hinj
  exact htail.measure_inter_preimage_eq_mul SF (fun k hk => hsets k hk)

/-- **Strong Markov property (independence from the past).**

The stopped σ-algebra `F_T` is independent of the σ-algebra generated by the post-stopping
sequence `(X_{T+k+1})_{k ≥ 0}`. -/
theorem strong_markov_iid_indep_past
    {X : ℕ → Ω → S} {f : Filtration ℕ m} {T : Ω → ℕ}
    (hX_id : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_ind : iIndepFun (m := fun _ => ‹MeasurableSpace S›) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hT : IsStoppingTime f (fun ω => (T ω : ℕ∞)))
    (hfX : ∀ n, f n ≤ ⨆ i ∈ Finset.range (n + 1), MeasurableSpace.comap (X i) ‹MeasurableSpace S›)
    [IsProbabilityMeasure μ] :
    Indep (hT.measurableSpace)
      (⨆ k, MeasurableSpace.comap (postStoppingTimeSeq X T k) ‹MeasurableSpace S›)
      (μ := μ) := by
  set Y := postStoppingTimeSeq X T
  set m_Y : ℕ → MeasurableSpace Ω := fun k => MeasurableSpace.comap (Y k) ‹MeasurableSpace S›

  set p1 : Set (Set Ω) := {s | @MeasurableSet Ω hT.measurableSpace s}
  set p2 : Set (Set Ω) := piiUnionInter (fun k => {s | @MeasurableSet Ω (m_Y k) s}) Set.univ

  have hY_meas : ∀ k, Measurable (Y k) := by
    intro k; show Measurable (fun ω => X (T ω + k + 1) ω)
    intro s hs
    have : (fun ω => X (T ω + k + 1) ω) ⁻¹' s =
        ⋃ n, {ω | T ω = n} ∩ (X (n + k + 1)) ⁻¹' s := by
      ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨T ω, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
    rw [this]
    exact MeasurableSet.iUnion fun n =>
      (measurableSet_stoppingTime_eq hT n).inter (hX_meas (n + k + 1) hs)

  have hgen1 : hT.measurableSpace = MeasurableSpace.generateFrom p1 :=
    (@MeasurableSpace.generateFrom_measurableSet Ω hT.measurableSpace).symm

  have hgen2 : ⨆ k, m_Y k = MeasurableSpace.generateFrom p2 := by
    have := generateFrom_piiUnionInter_measurableSet m_Y Set.univ
    simp only [Set.mem_univ, iSup_true] at this
    exact this.symm

  have h1 : hT.measurableSpace ≤ m := fun s hs => (hT.measurableSet s).mp hs |>.1

  have h2 : ⨆ k, m_Y k ≤ m := by
    apply iSup_le; intro k
    exact MeasurableSpace.comap_le_iff_le_map.mpr (hY_meas k)

  have hp1 : IsPiSystem p1 := @MeasurableSpace.isPiSystem_measurableSet Ω hT.measurableSpace

  have hp2 : IsPiSystem p2 :=
    isPiSystem_piiUnionInter _ (fun k => @MeasurableSpace.isPiSystem_measurableSet Ω (m_Y k))
      Set.univ

  have hindep_sets : IndepSets p1 p2 μ := by
    simp only [IndepSets, Kernel.IndepSets, Kernel.const_apply]
    intro A B hA hB_pii

    change @MeasurableSet Ω hT.measurableSpace A at hA

    obtain ⟨SF, _, sets_fn, hsets_fn, hB_eq⟩ := hB_pii
    subst hB_eq

    have hCk : ∀ k ∈ SF, ∃ C_k : Set S, MeasurableSet C_k ∧ Y k ⁻¹' C_k = sets_fn k := by
      intro k hk
      have h := hsets_fn k hk
      rw [Set.mem_setOf_eq] at h
      rwa [MeasurableSpace.measurableSet_comap] at h

    classical
    choose! C hC_meas hC_eq using hCk

    have hB_form : ⋂ k ∈ SF, sets_fn k = ⋂ k ∈ SF, Y k ⁻¹' C k := by
      apply Set.iInter₂_congr; intro k hk; exact (hC_eq k hk).symm
    rw [hB_form]

    have decomp_AB : A ∩ ⋂ k ∈ SF, Y k ⁻¹' C k =
        ⋃ n, (A ∩ {ω | T ω = n}) ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' C k := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
        Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro ⟨ha, hb⟩; exact ⟨T ω, ⟨ha, rfl⟩, fun k hk => hb k hk⟩
      · rintro ⟨n, ⟨ha, rfl⟩, hb⟩; exact ⟨ha, fun k hk => hb k hk⟩
    have decomp_B : ⋂ k ∈ SF, Y k ⁻¹' C k =
        ⋃ n, {ω | T ω = n} ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' C k := by
      ext ω; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro hb; exact ⟨T ω, rfl, fun k hk => hb k hk⟩
      · rintro ⟨n, rfl, hb⟩ k hk; exact hb k hk

    have hdisj_AB : Pairwise (Function.onFun Disjoint
        (fun n => (A ∩ {ω | T ω = n}) ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' C k)) := by
      intro i j hij; simp only [Function.onFun, Set.disjoint_left, Set.mem_inter_iff,
        Set.mem_setOf_eq]; intro ω ⟨⟨_, hi⟩, _⟩ ⟨⟨_, hj⟩, _⟩; exact hij (hi.symm.trans hj)
    have hdisj_B : Pairwise (Function.onFun Disjoint
        (fun n => {ω | T ω = n} ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' C k)) := by
      intro i j hij; simp only [Function.onFun, Set.disjoint_left, Set.mem_inter_iff,
        Set.mem_setOf_eq]; intro ω ⟨hi, _⟩ ⟨hj, _⟩; exact hij (hi.symm.trans hj)

    have hA_m : MeasurableSet A := h1 _ hA
    have hnull_AB n : NullMeasurableSet
        ((A ∩ {ω | T ω = n}) ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' C k) μ :=
      (hA_m.inter (measurableSet_stoppingTime_eq hT n)).nullMeasurableSet |>.inter
        ((MeasurableSet.biInter (Finset.countable_toSet SF)
          (fun k hk => hX_meas (n + k + 1) (hC_meas k hk))).nullMeasurableSet)
    have hnull_B n : NullMeasurableSet
        ({ω | T ω = n} ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' C k) μ :=
      ((measurableSet_stoppingTime_eq hT n).nullMeasurableSet).inter
        ((MeasurableSet.biInter (Finset.countable_toSet SF)
          (fun k hk => hX_meas (n + k + 1) (hC_meas k hk))).nullMeasurableSet)

    rw [decomp_AB, measure_iUnion₀ (fun i j hij => (hdisj_AB hij).aedisjoint) hnull_AB]
    rw [decomp_B, measure_iUnion₀ (fun i j hij => (hdisj_B hij).aedisjoint) hnull_B]

    have key_AB : ∀ n, μ ((A ∩ {ω | T ω = n}) ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' C k) =
        μ (A ∩ {ω | T ω = n}) * ∏ k ∈ SF, μ ((X (n + k + 1)) ⁻¹' C k) := by
      intro n
      exact indep_fn_tail_finset X f hX_ind hX_meas hfX n _ (measurableSet_FT_inter_eq hT hA n)
        SF C (fun k hk => hC_meas k hk)
    have key_B : ∀ n, μ ({ω | T ω = n} ∩ ⋂ k ∈ SF, (X (n + k + 1)) ⁻¹' C k) =
        μ {ω | T ω = n} * ∏ k ∈ SF, μ ((X (n + k + 1)) ⁻¹' C k) :=
      fun n => indep_stopping_time_tail_finset X f T hX_ind hX_meas hT hfX n SF C
        (fun k hk => hC_meas k hk)

    have hprod_const : ∀ n, ∏ k ∈ SF, μ ((X (n + k + 1)) ⁻¹' C k) =
        ∏ k ∈ SF, μ ((X 0) ⁻¹' C k) := by
      intro n; apply Finset.prod_congr rfl
      intro k hk; exact (hX_id (n + k + 1) 0).measure_preimage_eq (hC_meas k hk)
    simp_rw [key_AB, key_B, hprod_const, ENNReal.tsum_mul_right]

    have hsum : ∑' n, μ {ω | T ω = n} = 1 := by
      rw [← measure_iUnion (fun i j hij => by
        simp only [Function.onFun, Set.disjoint_left, Set.mem_setOf_eq]
        intro ω hi hj; exact hij (hi.symm.trans hj))
        (fun n => measurableSet_stoppingTime_eq hT n)]
      have : ⋃ n, {ω : Ω | T ω = n} = Set.univ := by ext ω; simp [Set.mem_iUnion]
      rw [this]; exact measure_univ

    have hsum_A : ∑' n, μ (A ∩ {ω | T ω = n}) = μ A := by
      rw [← measure_iUnion₀ (fun i j hij => by
        exact (Disjoint.aedisjoint (by
          simp only [Set.disjoint_left, Set.mem_inter_iff, Set.mem_setOf_eq]
          intro ω ⟨_, hi⟩ ⟨_, hj⟩; exact hij (hi.symm.trans hj))))
        (fun n => (hA_m.inter (measurableSet_stoppingTime_eq hT n)).nullMeasurableSet)]
      congr 1; ext ω; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun ⟨_, ⟨h, _⟩⟩ => h, fun h => ⟨T ω, ⟨h, rfl⟩⟩⟩
    rw [hsum_A, hsum, one_mul]
    exact Filter.Eventually.of_forall fun _ => rfl

  exact hindep_sets.indep h1 h2 hp1 hp2 hgen1 hgen2

/-- **Strong Markov property for i.i.d. sequences.**

Let `X_1, X_2, …` be i.i.d. with values in `S`, and let `T` be a finite `ℕ`-valued stopping
time relative to a filtration that contains the filtration generated by `X`. Then,
conditional on `{T < ∞}`:

1. each `X_{T+k+1}` has the same distribution as `X_0`,
2. the sequence `(X_{T+k+1})_{k ≥ 0}` is independent, and
3. it is independent of the stopped σ-algebra `F_T`.

In other words, `(X_{T+k+1})_{k ≥ 0}` is an i.i.d. copy of the original sequence,
independent of the past `F_T`. -/
theorem strong_markov_iid
    {X : ℕ → Ω → S} {f : Filtration ℕ m} {T : Ω → ℕ}
    (hX_id : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_ind : iIndepFun (m := fun _ => ‹MeasurableSpace S›) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hT : IsStoppingTime f (fun ω => (T ω : ℕ∞)))
    (hfX : ∀ n, f n ≤ ⨆ i ∈ Finset.range (n + 1), MeasurableSpace.comap (X i) ‹MeasurableSpace S›)
    [IsProbabilityMeasure μ] :
    (∀ k, IdentDistrib (postStoppingTimeSeq X T k) (X 0) μ μ) ∧
    iIndepFun (m := fun _ => ‹MeasurableSpace S›) (postStoppingTimeSeq X T) μ ∧
    Indep (hT.measurableSpace)
      (⨆ k, MeasurableSpace.comap (postStoppingTimeSeq X T k) ‹MeasurableSpace S›)
      (μ := μ) :=
  ⟨fun k => strong_markov_iid_identDistrib hX_id hX_ind hX_meas hT hfX k,
   strong_markov_iid_iIndepFun hX_id hX_ind hX_meas hT hfX,
   strong_markov_iid_indep_past hX_id hX_ind hX_meas hT hfX⟩

end
