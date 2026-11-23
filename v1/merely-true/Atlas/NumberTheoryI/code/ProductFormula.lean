/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Complex
import Mathlib.Analysis.Normed.Field.ProperSpace

noncomputable section

open MeasureTheory Measure TopologicalSpace Pointwise Filter Topology

structure IsRadonMeasure {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X]
    (μ : MeasureTheory.Measure X) : Prop where
  isFiniteMeasureOnCompacts : MeasureTheory.IsFiniteMeasureOnCompacts μ
  regular : MeasureTheory.Measure.Regular μ
  innerRegular : MeasureTheory.Measure.InnerRegular μ

theorem compact_group_finite_measure (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] : IsFiniteMeasure μ :=
  CompactSpace.isFiniteMeasure

theorem weil_uniqueness (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ν = c • μ := by
  obtain ⟨K0⟩ := PositiveCompacts.nonempty' (α := G)
  set c := ν ↑K0 / μ ↑K0 with hc_def
  have hμ_pos : μ ↑K0 ≠ 0 :=
    (measure_pos_of_nonempty_interior μ K0.interior_nonempty).ne'
  have hμ_fin : μ ↑K0 ≠ ⊤ := (IsCompact.measure_lt_top K0.isCompact).ne
  have hν_pos : ν ↑K0 ≠ 0 :=
    (measure_pos_of_nonempty_interior ν K0.interior_nonempty).ne'
  have hν_fin : ν ↑K0 ≠ ⊤ := (IsCompact.measure_lt_top K0.isCompact).ne
  refine ⟨c, ENNReal.div_ne_zero.mpr ⟨hν_pos, hμ_fin⟩,
         ENNReal.div_ne_top hν_fin hμ_pos, ?_⟩


  have hμ_eq := addHaarMeasure_unique μ K0
  have hν_eq := addHaarMeasure_unique ν K0
  rw [hμ_eq, hν_eq, smul_smul, hc_def, ENNReal.div_mul_cancel hμ_pos hμ_fin]

def mulLeftContinuousAddEquiv {K : Type*} [NormedField K]
    {a : K} (ha : a ≠ 0) : K ≃ₜ+ K :=
  ContinuousAddEquiv.mk
    { toFun := (a * ·)
      invFun := (a⁻¹ * ·)
      left_inv := fun x => by
        show a⁻¹ * (a * x) = x; rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      right_inv := fun x => by
        show a * (a⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      map_add' := fun x y => by show a * (x + y) = a * x + a * y; ring }

@[simp] lemma mulLeftContinuousAddEquiv_apply {K : Type*} [NormedField K]
    {a : K} (ha : a ≠ 0) (x : K) :
    mulLeftContinuousAddEquiv ha x = a * x := rfl

lemma mulLeftContinuousAddEquiv_preimage_smul {K : Type*} [NormedField K]
    {a : K} (ha : a ≠ 0) (S : Set K) :
    (mulLeftContinuousAddEquiv ha) ⁻¹' (a • S) = S := by
  ext x
  simp only [Set.mem_preimage, mulLeftContinuousAddEquiv_apply,
    Set.mem_smul_set_iff_inv_smul_mem₀ ha, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ ha, one_mul]

lemma mulLeftContinuousAddEquiv_symm {K : Type*} [NormedField K]
    {a : K} (ha : a ≠ 0) :
    (mulLeftContinuousAddEquiv ha).symm = mulLeftContinuousAddEquiv (inv_ne_zero ha) := by
  ext x; show a⁻¹ * x = a⁻¹ * x; rfl

theorem proposition_13_16_haar_scaling
    (K : Type*) [NormedField K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (a : K) (ha : a ≠ 0) (S : Set K) :
    μ (a • S) = ↑(addEquivAddHaarChar (mulLeftContinuousAddEquiv ha)) * μ S := by
  have hscale := addEquivAddHaarChar_smul_preimage μ (mulLeftContinuousAddEquiv ha) (X := a • S)
  rw [mulLeftContinuousAddEquiv_preimage_smul ha S] at hscale
  rw [← hscale]; simp

lemma distribHaarChar_eq_addEquivAddHaarChar_mulLeft
    {K : Type*} [NormedField K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    {a : K} (ha : a ≠ 0) :
    distribHaarChar K (Units.mk0 a ha) =
    addEquivAddHaarChar (mulLeftContinuousAddEquiv ha) := by
  obtain ⟨s, hs_compact, hs_nhd⟩ := exists_compact_mem_nhds (0 : K)
  have hs_ne_zero : (addHaar : Measure K) s ≠ 0 := by
    obtain ⟨U, hU_sub, hU_open, h0U⟩ := mem_nhds_iff.mp hs_nhd
    exact ne_of_gt (lt_of_lt_of_le (hU_open.measure_pos addHaar ⟨0, h0U⟩) (measure_mono hU_sub))
  have hs_ne_top : (addHaar : Measure K) s ≠ ⊤ := hs_compact.measure_lt_top.ne
  apply distribHaarChar_eq_of_measure_smul_eq_mul (s := s) (μ := addHaar) hs_ne_zero hs_ne_top
  have h := addEquivAddHaarChar_smul_preimage addHaar (mulLeftContinuousAddEquiv ha)
    (X := (Units.mk0 a ha) • s)
  have preimage_eq : (mulLeftContinuousAddEquiv ha) ⁻¹' ((Units.mk0 a ha) • s) = s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : a * y = a * x := by
        simp only [Units.smul_def, smul_eq_mul, Units.val_mk0] at hxy; exact hxy
      exact mul_left_cancel₀ ha this ▸ hy
    · intro hx
      exact ⟨x, hx, by simp [Units.smul_def, smul_eq_mul, mulLeftContinuousAddEquiv]⟩
  rw [preimage_eq] at h
  rw [← h]; simp [ENNReal.smul_def, smul_eq_mul]

lemma units_smul_closedBall_zero_one {K : Type*} [NormedField K] (g : Kˣ) :
    (g : K) • Metric.closedBall (0 : K) 1 = Metric.closedBall (0 : K) ‖(g : K)‖ := by
  ext x
  simp only [Set.mem_smul_set, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [smul_eq_mul]
    calc ‖(g : K) * y‖ = ‖(g : K)‖ * ‖y‖ := norm_mul _ _
    _ ≤ ‖(g : K)‖ * 1 := by gcongr
    _ = ‖(g : K)‖ := mul_one _
  · intro hx
    refine ⟨(g : K)⁻¹ * x, ?_, ?_⟩
    · show ‖(↑g)⁻¹ * x‖ ≤ 1
      calc ‖(g : K)⁻¹ * x‖ = ‖(g : K)‖⁻¹ * ‖x‖ := by rw [norm_mul, norm_inv]
      _ ≤ ‖(g : K)‖⁻¹ * ‖(g : K)‖ := by gcongr
      _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr g.ne_zero)
    · simp [smul_eq_mul]

lemma units_smul_ball_zero_one {K : Type*} [NormedField K] (g : Kˣ) :
    (g : K) • Metric.ball (0 : K) 1 = Metric.ball (0 : K) ‖(g : K)‖ := by
  ext x
  simp only [Set.mem_smul_set, Metric.mem_ball, dist_zero_right]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [smul_eq_mul, norm_mul]
    exact mul_lt_of_lt_one_right (norm_pos_iff.mpr g.ne_zero) hy
  · intro hx
    refine ⟨(g : K)⁻¹ * x, ?_, ?_⟩
    · simp only [norm_mul, norm_inv]
      rw [inv_mul_lt_iff₀ (norm_pos_iff.mpr g.ne_zero)]
      linarith
    · simp [smul_eq_mul]

end



noncomputable section
open MeasureTheory Measure TopologicalSpace Pointwise Filter Topology Metric










def IsNormalizedAbsVal
    {K : Type*} [Field K] [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K]
    (f : K → ℝ) : Prop :=
  (∀ a, 0 ≤ f a) ∧
  ∀ (μ : Measure K) [μ.IsAddHaarMeasure] (a : K) (S : Set K),
    μ ((a * ·) '' S) = ENNReal.ofReal (f a) * μ S

lemma isNormalizedAbsVal_unique
    {K : Type*} [Field K] [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K]
    [IsTopologicalAddGroup K]
    (f g : K → ℝ) (hf : IsNormalizedAbsVal f) (hg : IsNormalizedAbsVal g) :
    f = g := by
  ext a
  obtain ⟨U, hU_compact, hU_nhd⟩ := exists_compact_mem_nhds (0 : K)
  set μ : Measure K := addHaar with hμ_def
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hU_pos : μ U ≠ 0 := ne_of_gt (measure_pos_of_mem_nhds μ hU_nhd)
  have hU_fin : μ U ≠ ⊤ := ne_of_lt hU_compact.measure_lt_top
  have h1 := @hf.2 μ hμ a U
  have h2 := @hg.2 μ hμ a U
  rw [h1] at h2
  have h3 : ENNReal.ofReal (f a) = ENNReal.ofReal (g a) :=
    (ENNReal.mul_left_inj hU_pos hU_fin).mp h2
  exact (ENNReal.ofReal_eq_ofReal_iff (hf.1 a) (hg.1 a)).mp h3





class IsGlobalField (K : Type*) [Field K] where
  PlaceType : Type*
  place_nonempty : Nonempty PlaceType
  Completion : PlaceType → Type*
  completionField : ∀ v, Field (Completion v)
  completionTopologicalSpace : ∀ v, TopologicalSpace (Completion v)
  completionLocallyCompact : ∀ v,
    @LocallyCompactSpace (Completion v) (completionTopologicalSpace v)
  completionNontrivial : ∀ v, @Nontrivial (Completion v)
  absVal : PlaceType → AbsoluteValue K ℝ
  exponent : PlaceType → ℝ
  exponent_pos : ∀ v, 0 < exponent v
  normAbsVal : PlaceType → K → ℝ
  normAbsVal_nonneg : ∀ v x, 0 ≤ normAbsVal v x
  normAbsVal_eq : ∀ v x, normAbsVal v x = (absVal v x) ^ (exponent v)
  normAbsVal_eq_one_of_finite : ∀ x, x ≠ 0 →
    Set.Finite {v | normAbsVal v x ≠ 1}
  product_formula : ∀ x, x ≠ 0 → ∏ᶠ v, normAbsVal v x = 1

theorem theorem_13_21_product_formula_global (K : Type*) [Field K] [NumberField K]
    {x : K} (hx : x ≠ 0) :
    (∏ w : NumberField.InfinitePlace K, (w x) ^ w.mult) *
    ∏ᶠ w : NumberField.FinitePlace K, (w x) = 1 :=
  NumberField.prod_abs_eq_one hx


end
