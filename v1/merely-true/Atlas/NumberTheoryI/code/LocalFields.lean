/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.NumberTheory.Ostrowski
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Atlas.NumberTheoryI.code.Adeles

open Metric Filter Set Topology

class IsLocalField (K : Type*) extends NontriviallyNormedField K where
  locallyCompact : LocallyCompactSpace K

attribute [instance] IsLocalField.locallyCompact

instance IsLocalField.properSpace (K : Type*) [IsLocalField K] : ProperSpace K :=
  ProperSpace.of_locallyCompactSpace K


noncomputable instance : IsLocalField ℝ where
  locallyCompact := inferInstance


noncomputable instance : IsLocalField ℂ where
  locallyCompact := inferInstance


noncomputable instance instIsLocalFieldPadic (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocalField ℚ_[p] where
  locallyCompact := inferInstance

theorem isLocalField_iff_closedBalls_compact (K : Type*) [NontriviallyNormedField K] :
    LocallyCompactSpace K ↔ ∀ (x : K) (r : ℝ), IsCompact (closedBall x r) := by
  constructor
  · intro hlc
    haveI : ProperSpace K := ProperSpace.of_locallyCompactSpace K
    exact fun x r => isCompact_closedBall x r
  · intro h
    haveI : ProperSpace K := ⟨h⟩
    exact locallyCompact_of_proper


theorem IsLocalField.completeSpace (K : Type*) [IsLocalField K] : CompleteSpace K :=
  complete_of_proper


section DiscreteValuationCharacterization

open scoped Valued

theorem isLocalField_iff_complete_dvr_finiteResidue
    {K : Type*} {Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [(Valued.v : Valuation K Γ₀).RankOne] :
    ProperSpace K ↔
      CompleteSpace K ∧ IsDiscreteValuationRing (Valued.integer K) ∧
        Finite (Valued.ResidueField K) :=
  Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField

theorem isLocalField_iff_complete_finiteResidue_of_dvr
    {K : Type*} {Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [(Valued.v : Valuation K Γ₀).RankOne]
    [IsDiscreteValuationRing (Valued.integer K)] :
    ProperSpace K ↔
      CompleteSpace K ∧ Finite (Valued.ResidueField K) := by
  rw [isLocalField_iff_complete_dvr_finiteResidue]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, inferInstance, h3⟩

end DiscreteValuationCharacterization

theorem locallyCompact_of_finiteDimensional_over_localField (K : Type*) [IsLocalField K]
    (L : Type*) [NontriviallyNormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
    LocallyCompactSpace L := by
  haveI : ProperSpace L := FiniteDimensional.proper K L
  exact locallyCompact_of_proper

@[reducible] noncomputable def isLocalField_real : IsLocalField ℝ := inferInstance

@[reducible] noncomputable def corollary_9_7_archimedean : IsLocalField ℝ := isLocalField_real

@[reducible] noncomputable def isLocalField_padic (p : ℕ) [Fact (Nat.Prime p)] : IsLocalField ℚ_[p] :=
  instIsLocalFieldPadic p

@[reducible] noncomputable def corollary_9_7_padic (p : ℕ) [Fact (Nat.Prime p)] : IsLocalField ℚ_[p] :=
  isLocalField_padic p

@[reducible] noncomputable def isLocalField_of_finiteDimensional_extension (K : Type*) [IsLocalField K]
    (L : Type*) [NontriviallyNormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
    IsLocalField L where
  locallyCompact := locallyCompact_of_finiteDimensional_over_localField K L

@[reducible] noncomputable def corollary_9_7_finite_extension (K : Type*) [IsLocalField K]
    (L : Type*) [NontriviallyNormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
    IsLocalField L :=
  isLocalField_of_finiteDimensional_extension K L

@[reducible] noncomputable def localField_Qp (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocalField ℚ_[p] := isLocalField_padic p

@[reducible] noncomputable def localField_R : IsLocalField ℝ := isLocalField_real

@[reducible] noncomputable def localField_C : IsLocalField ℂ := inferInstance


theorem IsLocalField.finiteDimensional_of_locallyCompact_module (K : Type*) [IsLocalField K]
    {E : Type*} [AddCommGroup E] [UniformSpace E] [T2Space E] [IsUniformAddGroup E]
    [Module K E] [ContinuousSMul K E] [LocallyCompactSpace E] :
    FiniteDimensional K E := by
  haveI : CompleteSpace K := IsLocalField.completeSpace K
  exact FiniteDimensional.of_locallyCompactSpace K

lemma not_accPt_of_separated {X : Type*} [MetricSpace X] {S : Set X}
    (h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ dist x y) (a : X) :
    ¬ AccPt a (𝓟 S) := by
  intro hacc; rw [accPt_iff_nhds] at hacc
  obtain ⟨y₁, ⟨hy₁_ball, hy₁_S⟩, hy₁_ne⟩ :=
    hacc (ball a (1/2)) (ball_mem_nhds a (by positivity))
  obtain ⟨y₂, ⟨hy₂_ball, hy₂_S⟩, _⟩ :=
    hacc (ball a (1/2) \ {y₁}) (by
      apply diff_mem (ball_mem_nhds a (by positivity))
      exact isOpen_ne.mem_nhds (Ne.symm hy₁_ne))
  linarith [h_sep y₁ hy₁_S y₂ hy₂_S (Ne.symm (fun h => hy₂_ball.2 (mem_singleton_iff.mpr h))),
            dist_triangle y₁ a y₂, mem_ball.mp hy₁_ball, mem_ball.mp hy₂_ball.1, dist_comm a y₂]

noncomputable def absValFromNorm (L : Type*) [NormedField L] [CharZero L] :
    AbsoluteValue ℚ ℝ where
  toFun q := ‖(q : L)‖
  map_mul' x y := by simp [norm_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by
    simp only [norm_eq_zero]; constructor
    · intro h; exact_mod_cast h
    · intro h; simp [h]
  add_le' x y := by
    show ‖((x + y : ℚ) : L)‖ ≤ ‖(x : L)‖ + ‖(y : L)‖
    rw [show ((x + y : ℚ) : L) = (x : L) + (y : L) from by push_cast; ring]
    exact norm_add_le _ _

theorem absValFromNorm_isNontrivial (L : Type*) [IsLocalField L] [CharZero L] :
    (absValFromNorm L).IsNontrivial := by
  by_contra h_triv
  simp only [AbsoluteValue.IsNontrivial, absValFromNorm, AbsoluteValue.coe_mk,
    MulHom.coe_mk, not_exists, not_and, not_not] at h_triv
  let S : Set L := range (fun n : ℤ => (n : L))
  have h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ dist x y := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩ hnm
    simp only [dist_eq_norm]
    rw [show (n : L) - (m : L) = ((n - m : ℤ) : L) from by push_cast; ring,
        show ‖((n - m : ℤ) : L)‖ = ‖((n - m : ℚ) : L)‖ from by push_cast; ring_nf,
        h_triv _ (by exact_mod_cast sub_ne_zero.mpr (fun h => hnm (congrArg _ h)))]
  have hS_sub : S ⊆ closedBall (0 : L) 1 := by
    rintro _ ⟨n, rfl⟩; simp only [mem_closedBall, dist_zero_right]
    by_cases hn : (n : ℚ) = 0
    · simp [show (n : L) = 0 from by exact_mod_cast hn]
    · rw [show ‖(n : L)‖ = ‖((n : ℚ) : L)‖ from by push_cast; ring_nf, h_triv _ hn]
  obtain ⟨x, _, hx⟩ := (infinite_range_of_injective (fun (_ : ℤ) _ h => by
    exact_mod_cast h) : S.Infinite).exists_accPt_of_subset_isCompact
    (isCompact_closedBall 0 1) hS_sub
  exact not_accPt_of_separated h_sep x hx

noncomputable def normAbsValQ {L_v : Type*} [NontriviallyNormedField L_v]
    (j : ℚ →+* L_v) : AbsoluteValue ℚ ℝ where
  toFun q := ‖j q‖
  map_mul' x y := by simp [map_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by rw [norm_eq_zero, map_eq_zero_iff j j.injective]
  add_le' x y := by simp only [map_add]; exact norm_add_le _ _

lemma absValFromNorm_eq_normAbsValQ_castHom
    (L : Type*) [NontriviallyNormedField L] [CharZero L] :
    absValFromNorm L = normAbsValQ (Rat.castHom L) := by
  ext q; simp [absValFromNorm, normAbsValQ]

lemma normAbsValQ_isEquiv_real_uniformContinuous
    {L_v : Type*} [NontriviallyNormedField L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real) :
    UniformContinuous j := by
  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  refine ⟨ε ^ c, by positivity, fun q₁ q₂ hd => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  have key : ‖j (q₁ - q₂)‖ ^ c = Rat.AbsoluteValue.real (q₁ - q₂) := congr_fun hpow (q₁ - q₂)
  have hdist : dist q₁ q₂ = Rat.AbsoluteValue.real (q₁ - q₂) := by
    rw [Rat.AbsoluteValue.real_eq_abs, Rat.dist_eq]; push_cast; rfl
  have h2 : ‖j (q₁ - q₂)‖ ^ c < ε ^ c := by rw [key]; linarith [hdist]
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hc).mp h2

noncomputable def extendRingHom_real
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real) :
    ℝ →+* L_v :=
  @IsDenseInducing.extendRingHom ℚ _ _ ℝ _ _ _ L_v _ _ _ _ _
    (Rat.castHom ℝ) j
    Rat.isUniformEmbedding_coe_real.isUniformInducing
    Rat.isDenseEmbedding_coe_real.dense
    (normAbsValQ_isEquiv_real_uniformContinuous j hequiv)

lemma extendRingHom_real_continuous
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real) :
    Continuous (extendRingHom_real j hequiv) :=
  (uniformContinuous_uniformly_extend
    Rat.isUniformEmbedding_coe_real.isUniformInducing
    Rat.isDenseEmbedding_coe_real.dense
    (normAbsValQ_isEquiv_real_uniformContinuous j hequiv)).continuous

lemma extendRingHom_real_extends
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real)
    (q : ℚ) : extendRingHom_real j hequiv (q : ℝ) = j q :=
  IsDenseInducing.extend_eq
    (Rat.isUniformEmbedding_coe_real.isUniformInducing.isDenseInducing
      Rat.isDenseEmbedding_coe_real.dense)
    (normAbsValQ_isEquiv_real_uniformContinuous j hequiv).continuous q

lemma normAbsValQ_isEquiv_padic_eq
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p))
    (hnorm_p : ‖j (↑p : ℚ)‖ = (↑p : ℝ)⁻¹) :
    normAbsValQ j = Rat.AbsoluteValue.padic p := by

  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  have hpow_fun : ∀ q : ℚ, (normAbsValQ j q) ^ c = (Rat.AbsoluteValue.padic p) q :=
    fun q => congr_fun hpow q

  have hp_val : normAbsValQ j (↑p : ℚ) = (↑p : ℝ)⁻¹ := hnorm_p
  have hp_padic : (Rat.AbsoluteValue.padic p) (↑p : ℚ) = (↑p : ℝ)⁻¹ := by
    rw [Rat.AbsoluteValue.padic_eq_padicNorm]
    simp [padicNorm.padicNorm_p_of_prime]
  have hpc : ((↑p : ℝ)⁻¹) ^ c = (↑p : ℝ)⁻¹ := by
    specialize hpow_fun (↑p : ℚ); rw [hp_val, hp_padic] at hpow_fun; exact hpow_fun
  have hp_pos : (0 : ℝ) < (↑p : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p))
  have hp_lt_one : (↑p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; exact_mod_cast Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  have hc_eq : c = 1 := by
    have hlog_neg := Real.log_neg hp_pos hp_lt_one
    have := congr_arg Real.log hpc
    rw [Real.log_rpow hp_pos] at this
    nlinarith

  ext q
  have := hpow_fun q
  rw [hc_eq, Real.rpow_one] at this
  exact this

lemma j_comp_equiv_continuous
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (heq : normAbsValQ j = Rat.AbsoluteValue.padic p) :
    Continuous (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
  let e := WithVal.equiv (Rat.padicValuation p)
  let ι := (Rat.castHom ℚ_[p]).comp e.toRingHom
  have hι : IsUniformInducing (ι : WithVal (Rat.padicValuation p) → ℚ_[p]) :=
    Padic.isUniformInducing_cast_withVal
  have hfι : ∀ a : WithVal (Rat.padicValuation p),
      ‖j.comp e.toRingHom a‖ = ‖ι a‖ := by
    intro a; show ‖j (e a)‖ = ‖(↑(e a) : ℚ_[p])‖
    have h1 : normAbsValQ j (e a) = Rat.AbsoluteValue.padic p (e a) := by rw [heq]
    simp only [normAbsValQ, AbsoluteValue.coe_mk, MulHom.coe_mk, Rat.AbsoluteValue.padic] at h1
    rw [h1, Padic.eq_padicNorm]
  apply continuous_of_continuousAt_zero (j.comp e.toRingHom : WithVal (Rat.padicValuation p) →+ L_v)
  rw [ContinuousAt, map_zero, Filter.tendsto_iff_forall_eventually_mem]
  intro s hs; rw [Metric.mem_nhds_iff] at hs; obtain ⟨ε, hε, hs⟩ := hs
  apply Filter.mem_of_superset
    ((hι.isInducing.continuous).continuousAt.preimage_mem_nhds
      (show Metric.ball 0 ε ∈ nhds (ι 0) by rw [map_zero]; exact Metric.ball_mem_nhds 0 hε))
  intro a ha; simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at ha
  apply hs; simp only [Metric.mem_ball, dist_zero_right]
  show ‖j.comp e.toRingHom a‖ < ε; rw [hfι]; exact ha

noncomputable def extendRingHom_padic
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (heq : normAbsValQ j = Rat.AbsoluteValue.padic p) :
    ℚ_[p] →+* L_v :=
  (UniformSpace.Completion.extensionHom
    (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
    (j_comp_equiv_continuous j p heq)).comp
  Padic.withValRingEquiv.symm.toRingHom

lemma extendRingHom_padic_on_rat
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (heq : normAbsValQ j = Rat.AbsoluteValue.padic p)
    (q : ℚ) : extendRingHom_padic j p heq (q : ℚ_[p]) = j q := by
  simp only [extendRingHom_padic, RingHom.coe_comp, Function.comp_apply,
             RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  have h1 : Padic.withValRingEquiv.symm (q : ℚ_[p]) =
      ((WithVal.equiv (Rat.padicValuation p)).symm q : (Rat.padicValuation p).Completion) := by
    apply Padic.withValRingEquiv.injective
    rw [Padic.withValRingEquiv.apply_symm_apply]; symm
    simp only [Padic.withValRingEquiv]
    erw [UniformSpace.Completion.extensionHom_coe _
      (Padic.isUniformInducing_cast_withVal.uniformContinuous.continuous)]
    simp
  rw [h1]
  erw [UniformSpace.Completion.extensionHom_coe _ (j_comp_equiv_continuous j p heq)]
  simp

lemma extendRingHom_padic_continuous
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (heq : normAbsValQ j = Rat.AbsoluteValue.padic p) :
    Continuous (extendRingHom_padic j p heq) := by
  show Continuous (fun x : ℚ_[p] =>
    (UniformSpace.Completion.extensionHom
      (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
      (j_comp_equiv_continuous j p heq))
      (Padic.withValRingEquiv.symm x))
  exact Continuous.comp
    (show Continuous (UniformSpace.Completion.extension
      (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)) from
      UniformSpace.Completion.continuous_extension)
    Padic.withValUniformEquiv.symm.continuous

lemma extendRingHom_padic_isometry
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (heq : normAbsValQ j = Rat.AbsoluteValue.padic p)
    (x : ℚ_[p]) :
    ‖extendRingHom_padic j p heq x‖ = ‖x‖ := by
  have key : (fun x => ‖extendRingHom_padic j p heq x‖) = (fun x => ‖x‖) := by
    apply DenseRange.equalizer (Padic.denseRange_ratCast p)
    · exact continuous_norm.comp (extendRingHom_padic_continuous j p heq)
    · exact continuous_norm
    · ext q; simp only [Function.comp_apply]
      rw [extendRingHom_padic_on_rat]
      have h1 : normAbsValQ j q = Rat.AbsoluteValue.padic p q := by rw [heq]
      simp only [normAbsValQ, AbsoluteValue.coe_mk, MulHom.coe_mk, Rat.AbsoluteValue.padic] at h1
      rw [h1, Padic.eq_padicNorm]
  exact congr_fun key x

@[reducible]
noncomputable def completion_normedAlgebra_padic_of_eq
    (L_v : Type*) [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (p : ℕ) [Fact (Nat.Prime p)]
    (heq : normAbsValQ j = Rat.AbsoluteValue.padic p) :
    NormedAlgebra ℚ_[p] L_v := by
  let f := extendRingHom_padic j p heq
  have hiso := extendRingHom_padic_isometry j p heq
  letI : Algebra ℚ_[p] L_v := f.toAlgebra
  exact NormedAlgebra.mk (fun r x => by
    have : (algebraMap ℚ_[p] L_v) r = f r := rfl
    rw [Algebra.smul_def, norm_mul, this, hiso])

@[reducible]
noncomputable def completion_normedAlgebra_padic
    (L_v : Type*) [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (p : ℕ) [Fact (Nat.Prime p)]
    (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p))
    (hnorm_p : ‖j (↑p : ℚ)‖ = (↑p : ℝ)⁻¹) :
    NormedAlgebra ℚ_[p] L_v :=
  completion_normedAlgebra_padic_of_eq L_v j p
    (normAbsValQ_isEquiv_padic_eq j p hequiv hnorm_p)

lemma normAbsValQ_isEquiv_real_eq
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real)
    (hnorm_2 : ‖j (2 : ℚ)‖ = 2) :
    normAbsValQ j = Rat.AbsoluteValue.real := by

  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  have hpow_fun : ∀ q : ℚ, (normAbsValQ j q) ^ c = (Rat.AbsoluteValue.real) q :=
    fun q => congr_fun hpow q

  have h2_val : normAbsValQ j (2 : ℚ) = (2 : ℝ) := hnorm_2
  have h2_real : (Rat.AbsoluteValue.real) (2 : ℚ) = (2 : ℝ) := by
    rw [Rat.AbsoluteValue.real_eq_abs]; norm_num
  have h2c : (2 : ℝ) ^ c = (2 : ℝ) := by
    specialize hpow_fun (2 : ℚ); rw [h2_val, h2_real] at hpow_fun; exact hpow_fun
  have hc_eq : c = 1 := by
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have h1 := congr_arg Real.log h2c
    rw [Real.log_rpow h2pos] at h1
    have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have : c * Real.log 2 = 1 * Real.log 2 := by linarith
    exact mul_right_cancel₀ (ne_of_gt hlog2_pos) this

  ext q
  have := hpow_fun q
  rw [hc_eq, Real.rpow_one] at this
  exact this

@[reducible]
noncomputable def completion_normedAlgebra_real_of_eq
    (L_v : Type*) [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (heq : normAbsValQ j = Rat.AbsoluteValue.real) :
    NormedAlgebra ℝ L_v := by
  have hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real :=
    heq ▸ AbsoluteValue.IsEquiv.refl _

  let f := extendRingHom_real j hequiv


  have hiso : ∀ r : ℝ, ‖f r‖ = ‖r‖ := by
    intro r
    have hclosed : IsClosed {x : ℝ | ‖f x‖ = ‖x‖} := by
      apply isClosed_eq
      · exact continuous_norm.comp (extendRingHom_real_continuous j hequiv)
      · exact continuous_norm
    have hdense : closure (Set.range (Rat.cast : ℚ → ℝ)) ⊆ {x | ‖f x‖ = ‖x‖} := by
      apply hclosed.closure_subset_iff.mpr
      rintro _ ⟨q, rfl⟩
      show ‖f (q : ℝ)‖ = ‖(q : ℝ)‖
      rw [extendRingHom_real_extends j hequiv q]
      have h1 : (normAbsValQ j) q = Rat.AbsoluteValue.real q := congr_fun (congr_arg _ heq) q
      change ‖j q‖ = _ at h1
      rw [h1, Rat.AbsoluteValue.real_eq_abs, Real.norm_eq_abs]
      push_cast; rfl
    exact hdense (Rat.isDenseEmbedding_coe_real.dense r)

  letI : Algebra ℝ L_v := f.toAlgebra
  exact NormedAlgebra.mk (fun r x => by
    have : (algebraMap ℝ L_v) r = f r := rfl
    rw [Algebra.smul_def, norm_mul, this, hiso])

@[reducible]
noncomputable def completion_normedAlgebra_real
    (L_v : Type*) [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real)
    (hnorm_2 : ‖j (2 : ℚ)‖ = 2) :
    NormedAlgebra ℝ L_v :=
  completion_normedAlgebra_real_of_eq L_v j
    (normAbsValQ_isEquiv_real_eq j hequiv hnorm_2)

lemma j_comp_equiv_continuous_of_equiv
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p)) :
    Continuous (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  let e := WithVal.equiv (Rat.padicValuation p)
  let ι := (Rat.castHom ℚ_[p]).comp e.toRingHom
  have hι : IsUniformInducing (ι : WithVal (Rat.padicValuation p) → ℚ_[p]) :=
    Padic.isUniformInducing_cast_withVal
  apply continuous_of_continuousAt_zero
    (j.comp e.toRingHom : WithVal (Rat.padicValuation p) →+ L_v)
  rw [ContinuousAt, map_zero, Filter.tendsto_iff_forall_eventually_mem]
  intro s hs
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hs⟩ := hs
  apply Filter.mem_of_superset
    ((hι.isInducing.continuous).continuousAt.preimage_mem_nhds
      (show Metric.ball 0 (ε ^ c) ∈ nhds (ι 0) by
        rw [map_zero]; exact Metric.ball_mem_nhds 0 (by positivity)))
  intro a ha
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at ha
  apply hs; simp only [Metric.mem_ball, dist_zero_right]
  show ‖j (e a)‖ < ε
  have hpow_a := congr_fun hpow (e a)
  simp only [normAbsValQ, AbsoluteValue.coe_mk, MulHom.coe_mk] at hpow_a
  rw [Rat.AbsoluteValue.padic_eq_padicNorm, ← Padic.eq_padicNorm] at hpow_a
  have h1 : ‖j (e a)‖ ^ c < ε ^ c := by rw [hpow_a]; exact ha
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hc).mp h1

noncomputable def extendRingHom_padic_of_equiv
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p)) :
    ℚ_[p] →+* L_v :=
  (UniformSpace.Completion.extensionHom
    (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
    (j_comp_equiv_continuous_of_equiv j p hequiv)).comp
  Padic.withValRingEquiv.symm.toRingHom

lemma extendRingHom_padic_of_equiv_continuous
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p)) :
    Continuous (extendRingHom_padic_of_equiv j p hequiv) := by
  show Continuous (fun x : ℚ_[p] =>
    (UniformSpace.Completion.extensionHom
      (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
      (j_comp_equiv_continuous_of_equiv j p hequiv))
      (Padic.withValRingEquiv.symm x))
  exact Continuous.comp
    (show Continuous (UniformSpace.Completion.extension
      (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)) from
      UniformSpace.Completion.continuous_extension)
    Padic.withValUniformEquiv.symm.continuous

noncomputable def localField_charZero_normedAlgebra_structure
    (L : Type*) [IsLocalField L] [CharZero L] :
    (Σ' (_ : Algebra ℝ L), ContinuousSMul ℝ L) ⊕
    (Σ' (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : Algebra ℚ_[p] L), ContinuousSMul ℚ_[p] L) := by
  classical
  have hnt := absValFromNorm_isNontrivial L
  have hostr := Rat.AbsoluteValue.equiv_real_or_padic (absValFromNorm L) hnt
  haveI : CompleteSpace L := complete_of_proper
  by_cases h_real : (absValFromNorm L).IsEquiv Rat.AbsoluteValue.real
  ·

    rw [absValFromNorm_eq_normAbsValQ_castHom] at h_real
    let f := extendRingHom_real (Rat.castHom L) h_real
    letI : Algebra ℝ L := f.toAlgebra
    have hcont : Continuous (algebraMap ℝ L) :=
      extendRingHom_real_continuous (Rat.castHom L) h_real
    exact Sum.inl ⟨‹Algebra ℝ L›, continuousSMul_of_algebraMap ℝ L hcont⟩
  ·
    have h_padic := hostr.resolve_left h_real
    let p := Classical.choose h_padic.exists
    have hp_spec := Classical.choose_spec h_padic.exists
    have hfact : Fact (Nat.Prime p) := Classical.choose hp_spec
    have h_equiv : (absValFromNorm L).IsEquiv (Rat.AbsoluteValue.padic p) :=
      Classical.choose_spec hp_spec
    rw [absValFromNorm_eq_normAbsValQ_castHom] at h_equiv
    let f := extendRingHom_padic_of_equiv (Rat.castHom L) p h_equiv
    letI : Algebra ℚ_[p] L := f.toAlgebra
    have hcont : Continuous (algebraMap ℚ_[p] L) :=
      extendRingHom_padic_of_equiv_continuous (Rat.castHom L) p h_equiv
    exact Sum.inr ⟨p, hfact, ‹Algebra ℚ_[p] L›, continuousSMul_of_algebraMap ℚ_[p] L hcont⟩

theorem localField_charZero_classification
    (L : Type*) [IsLocalField L] [CharZero L] :
    (Nonempty (L ≃+* ℝ)) ∨ (Nonempty (L ≃+* ℂ)) ∨
    (∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : Algebra ℚ_[p] L),
      FiniteDimensional ℚ_[p] L) := by


  rcases localField_charZero_normedAlgebra_structure L with ⟨hAlg, hCSMul⟩ | ⟨p, hp, hAlg, hCSMul⟩
  ·


    letI := hAlg; letI := hCSMul
    haveI : CompleteSpace L := complete_of_proper
    haveI : FiniteDimensional ℝ L := FiniteDimensional.of_locallyCompactSpace ℝ
    haveI : Algebra.IsAlgebraic ℝ L := Algebra.IsAlgebraic.of_finite ℝ L
    cases Real.nonempty_algEquiv_or L with
    | inl h => exact Or.inl (h.map AlgEquiv.toRingEquiv)
    | inr h => exact Or.inr (Or.inl (h.map AlgEquiv.toRingEquiv))
  ·


    letI := hAlg; letI := hCSMul; haveI := hp
    right; right
    haveI : CompleteSpace L := complete_of_proper
    exact ⟨p, hp, inferInstance, FiniteDimensional.of_locallyCompactSpace ℚ_[p]⟩

theorem posChar_laurent_series_embedding
    (L : Type*) [IsLocalField L]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP L p] :
    ∃ (n : ℕ) (_ : 0 < n),
      ∃ (f : LaurentSeries (GaloisField p n) →+* L), Function.Injective f := by
  open PowerSeries Finset in
  refine ⟨1, Nat.one_pos, ?_⟩

  obtain ⟨π, hπ_lt, hπ_pos⟩ : ∃ (π : L), ‖π‖ < 1 ∧ 0 < ‖π‖ := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := L)
    by_cases h1 : ‖x‖ < 1
    · exact ⟨x, h1, by linarith⟩
    · push Not at h1
      have hx_ne : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; linarith
      exact ⟨x⁻¹, by rw [norm_inv, inv_lt_one₀ (by linarith)]; linarith,
             by rw [norm_inv]; positivity⟩

  let ι : GaloisField p 1 →+* L :=
    (ZMod.castHom (dvd_refl p) L).comp (GaloisField.equivZmodP p).toAlgHom.toRingHom

  have hι_bound : ∀ a : GaloisField p 1, ‖ι a‖ ≤ 1 := by
    intro a
    have ha_frob : a ^ p = a :=
      (GaloisField.equivZmodP p).injective (by rw [map_pow, ZMod.pow_card])
    have hia_frob : (ι a) ^ p = ι a := by rw [← map_pow, ha_frob]
    by_cases hx0 : ι a = 0
    · simp [hx0]
    · by_contra h; push Not at h
      linarith [pow_le_pow_right₀ h.le (Fact.out : Nat.Prime p).two_le,
                sq_nonneg (‖ι a‖ - 1),
                show ‖ι a‖ ^ p = ‖ι a‖ from by rw [← norm_pow, hia_frob]]

  have norm_bound : ∀ (f : PowerSeries (GaloisField p 1)) (n : ℕ),
      ‖ι (coeff n f) * π ^ n‖ ≤ ‖π‖ ^ n := by
    intro f n; rw [norm_mul, norm_pow]
    calc ‖ι (coeff n f)‖ * ‖π‖ ^ n ≤ 1 * ‖π‖ ^ n := by gcongr; exact hι_bound _
    _ = ‖π‖ ^ n := one_mul _
  have summ : ∀ f : PowerSeries (GaloisField p 1),
      Summable (fun n => ι (coeff n f) * π ^ n) := by
    intro f
    exact .of_norm_bounded (g := fun n => ‖π‖ ^ n)
      (summable_geometric_of_lt_one (norm_nonneg _) hπ_lt) (norm_bound f)
  have summ_norm : ∀ f : PowerSeries (GaloisField p 1),
      Summable (fun n => ‖ι (coeff n f) * π ^ n‖) := by
    intro f
    exact (summable_geometric_of_lt_one (norm_nonneg _) hπ_lt).of_nonneg_of_le
      (fun _ => norm_nonneg _) (norm_bound f)
  have hπ_ne : π ≠ 0 := norm_pos_iff.mp hπ_pos

  let evalPS : PowerSeries (GaloisField p 1) →+* L :=
    { toFun := fun f => ∑' n, ι (coeff n f) * π ^ n
      map_zero' := by simp only [map_zero, zero_mul, tsum_zero]
      map_one' := by
        rw [show (∑' n, ι (coeff n (1 : PowerSeries _)) * π ^ n) =
            ι (coeff 0 1) * π ^ 0 from
          tsum_eq_single 0 (fun n hn => by
            rw [coeff_one, if_neg hn, map_zero, zero_mul])]
        simp [coeff_one]
      map_add' := fun F G => by
        simp only [map_add, add_mul]
        exact (summ F).tsum_add (summ G)
      map_mul' := fun F G => by
        rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summ_norm F) (summ_norm G)]
        congr 1; ext n
        rw [PowerSeries.coeff_mul, map_sum ι, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ⟨i, j⟩ hij
        have hij' : i + j = n := Finset.mem_antidiagonal.mp hij
        rw [map_mul, mul_mul_mul_comm, ← pow_add, hij'] }

  have evalPS_X_pow : ∀ k : ℕ, evalPS (PowerSeries.X ^ k) = π ^ k := by
    intro k
    show (∑' n, ι (coeff n (PowerSeries.X ^ k)) * π ^ n) = π ^ k
    rw [tsum_eq_single k (fun n hn => by
      simp only [PowerSeries.coeff_X_pow]
      rw [if_neg hn, map_zero, zero_mul])]
    rw [PowerSeries.coeff_X_pow, if_pos rfl, map_one, one_mul]

  have eval_unit : ∀ y : Submonoid.powers (PowerSeries.X : PowerSeries (GaloisField p 1)),
      IsUnit (evalPS ↑y) := by
    rintro ⟨_, k, rfl⟩
    rw [evalPS_X_pow]
    exact IsUnit.pow k (Ne.isUnit hπ_ne)

  let f : LaurentSeries (GaloisField p 1) →+* L := IsLocalization.lift eval_unit
  exact ⟨f, f.injective⟩

noncomputable instance LaurentSeries.instIsRankOneDiscrete (K : Type*) [Field K] :
    Valuation.IsRankOneDiscrete (LaurentSeries.valued K).v := by
  change Valuation.IsRankOneDiscrete ((PowerSeries.idealX K).valuation (LaurentSeries K))
  have h : PowerSeries.idealX K = IsDiscreteValuationRing.maximalIdeal (PowerSeries K) := by
    ext : 1
    simp only [PowerSeries.idealX, IsDiscreteValuationRing.maximalIdeal]
    exact PowerSeries.maximalIdeal_eq_span_X.symm
  rw [h]; infer_instance

@[reducible]
noncomputable instance LaurentSeries.instRankOne (K : Type*) [Field K] :
    Valuation.RankOne (LaurentSeries.valued K).v :=
  Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)





section NumberFieldCompletions

open NumberField NumberField.InfinitePlace.Completion IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

noncomputable instance NumberField.InfinitePlace.Completion.instIsLocalField
    (v : NumberField.InfinitePlace K) : IsLocalField v.Completion where
  locallyCompact := inferInstance

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
noncomputable instance HeightOneSpectrum.adicCompletion.instIsLocalField
    (v : HeightOneSpectrum (𝓞 K)) : IsLocalField (v.adicCompletion K) := by
  open scoped Valued in
  haveI : Finite (Valued.ResidueField (v.adicCompletion K)) :=
    NumberField.Adeles.adicCompletion_finite_residueField K v
  open scoped Valued in
  haveI : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  haveI : CompleteSpace (v.adicCompletion K) := inferInstance
  open scoped Valued in
  haveI : ProperSpace (v.adicCompletion K) :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact { locallyCompact := inferInstance }

noncomputable def numberFieldCompletion_isLocalField
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)) :
    match v with
    | Sum.inl w => IsLocalField w.Completion
    | Sum.inr p => IsLocalField (p.adicCompletion K) :=
  match v with
  | Sum.inl w => NumberField.InfinitePlace.Completion.instIsLocalField w
  | Sum.inr p => HeightOneSpectrum.adicCompletion.instIsLocalField p

noncomputable def corollary_9_7
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)) :
    match v with
    | Sum.inl w => IsLocalField w.Completion
    | Sum.inr p => IsLocalField (p.adicCompletion K) :=
  numberFieldCompletion_isLocalField v

@[reducible] noncomputable def numberFieldCompletion_isLocalField_infinite
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    IsLocalField v.Completion :=
  NumberField.InfinitePlace.Completion.instIsLocalField v

@[reducible] noncomputable def corollary_9_7_infinite_place
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    IsLocalField v.Completion :=
  numberFieldCompletion_isLocalField_infinite v

@[reducible] noncomputable def numberFieldCompletion_isLocalField_finite
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsLocalField (v.adicCompletion K) :=
  HeightOneSpectrum.adicCompletion.instIsLocalField v

@[reducible] noncomputable def corollary_9_7_finite_place
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsLocalField (v.adicCompletion K) :=
  numberFieldCompletion_isLocalField_finite v

end NumberFieldCompletions


lemma normAbsValQ_nontrivial
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    {L : Type*} [Field L]
    (hAlg : Algebra ℚ L) (hFD : @FiniteDimensional ℚ L _ _ hAlg.toModule)
    (ι : L →+* L_v) (hdense : DenseRange ι) :
    (normAbsValQ (ι.comp (algebraMap ℚ L))).IsNontrivial := by
  by_contra h
  rw [AbsoluteValue.IsNontrivial] at h
  push Not at h


  have h_triv : ∀ q : ℚ, ‖ι ((algebraMap ℚ L) q)‖ ≤ 1 := by
    intro q
    by_cases hq : q = 0
    · simp [hq]
    · have := h q hq
      simp only [normAbsValQ, AbsoluteValue.coe_mk, MulHom.coe_mk, RingHom.coe_comp,
                  Function.comp_apply] at this
      linarith


  letI := hAlg
  letI := hFD
  haveI : Fintype (Module.Free.ChooseBasisIndex ℚ L) :=
    Module.Free.ChooseBasisIndex.fintype ℚ L
  set b := Module.Free.chooseBasis ℚ L
  have hbound_L : ∀ l : L, ‖ι l‖ ≤ ∑ i, ‖ι (b i)‖ := by
    intro l
    have hl : l = ∑ i, (b.repr l i) • (b i) := (b.sum_repr l).symm
    rw [hl, map_sum]
    calc ‖∑ i, ι ((b.repr l i) • b i)‖
        ≤ ∑ i, ‖ι ((b.repr l i) • b i)‖ := norm_sum_le _ _
      _ = ∑ i, (‖ι (algebraMap ℚ L (b.repr l i))‖ * ‖ι (b i)‖) := by
          congr 1; ext i; rw [Algebra.smul_def, map_mul, norm_mul]
      _ ≤ ∑ i, (1 * ‖ι (b i)‖) := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_right (h_triv _) (norm_nonneg _)
      _ = ∑ i, ‖ι (b i)‖ := by simp

  set M := (∑ i, ‖ι (b i)‖) + 1
  have hbound_Lv : ∀ y : L_v, ‖y‖ ≤ M := by
    intro y
    obtain ⟨l, hl⟩ := hdense.exists_dist_lt y (show (0 : ℝ) < 1 by norm_num)
    calc ‖y‖ ≤ ‖ι l‖ + ‖y - ι l‖ := norm_le_insert' y (ι l)

      _ ≤ (∑ i, ‖ι (b i)‖) + dist y (ι l) := by
          linarith [hbound_L l, (dist_eq_norm y (ι l)).symm]
      _ ≤ (∑ i, ‖ι (b i)‖) + 1 := by linarith

  obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := L_v)
  have hx_pow : ∀ n : ℕ, ‖x‖ ^ n ≤ M := fun n => by rw [← norm_pow]; exact hbound_Lv _
  have htend := tendsto_pow_atTop_atTop_of_one_lt hx
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨n, hn⟩ := htend (M + 1)
  linarith [hx_pow n, hn n le_rfl]

theorem completion_finiteDimensional_real
    (L_v : Type*) [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (L : Type*) [Field L] (ι : L →+* L_v) (hdense : DenseRange ι)
    (hAlg : Algebra ℚ L) (hFD : @FiniteDimensional ℚ L _ _ hAlg.toModule)
    (_hequiv : (normAbsValQ (ι.comp (algebraMap ℚ L))).IsEquiv Rat.AbsoluteValue.real)
    [inst : NormedAlgebra ℝ L_v] :
    FiniteDimensional ℝ L_v := by

  letI : Module ℚ L := hAlg.toModule
  haveI : Module.Finite ℚ L := hFD
  set n := Module.finrank ℚ L
  set b := Module.finBasis ℚ L

  set S := Submodule.span ℝ (Set.range (fun i : Fin n => ι (b i))) with hS_def

  haveI hSfd : FiniteDimensional ℝ S :=
    Module.Finite.span_of_finite ℝ (Set.finite_range _)

  have hιL_sub : Set.range ι ⊆ (S : Set L_v) := by
    rintro y ⟨x, rfl⟩

    have hx : x = ∑ i, (b.repr x i) • (b i) := (b.sum_repr x).symm
    rw [hx, map_sum]
    apply Submodule.sum_mem
    intro i _

    rw [show (b.repr x i) • (b i) = algebraMap ℚ L (b.repr x i) * b i
          from Algebra.smul_def _ _, map_mul]


    have hcompat : ι (algebraMap ℚ L (b.repr x i)) =
        algebraMap ℝ L_v (algebraMap ℚ ℝ (b.repr x i)) := by
      have h := DFunLike.congr_fun (RingHom.ext_rat (ι.comp (algebraMap ℚ L))
                                         ((algebraMap ℝ L_v).comp (algebraMap ℚ ℝ))) (b.repr x i)
      exact_mod_cast h
    rw [hcompat, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hSdense : Dense (S : Set L_v) := Dense.mono hιL_sub hdense

  have hSclosed : IsClosed (S : Set L_v) := Submodule.closed_of_finiteDimensional S

  have hStop : S = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have huniv : (S : Set L_v) = Set.univ := by
      rw [← hSclosed.closure_eq, hSdense.closure_eq]
    rw [← SetLike.mem_coe, huniv]
    exact Set.mem_univ x

  have hsurj : Function.Surjective S.subtype := by
    intro x; exact ⟨⟨x, hStop ▸ Submodule.mem_top⟩, rfl⟩
  exact Module.Finite.of_surjective S.subtype hsurj

set_option maxHeartbeats 400000 in
theorem completion_finiteDimensional_padic
    (L_v : Type*) [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (L : Type*) [Field L] (ι : L →+* L_v) (hdense : DenseRange ι)
    (hAlg : Algebra ℚ L) (hFD : @FiniteDimensional ℚ L _ _ hAlg.toModule)
    (p : ℕ) [Fact (Nat.Prime p)]
    (_hequiv : (normAbsValQ (ι.comp (algebraMap ℚ L))).IsEquiv (Rat.AbsoluteValue.padic p))
    [inst : NormedAlgebra ℚ_[p] L_v] :
    FiniteDimensional ℚ_[p] L_v := by
  letI := hAlg; letI := hFD
  haveI : Fintype (Module.Free.ChooseBasisIndex ℚ L) :=
    Module.Free.ChooseBasisIndex.fintype ℚ L
  set b := Module.Free.chooseBasis ℚ L

  set S := Submodule.span ℚ_[p] (Set.range (fun i => ι (b i))) with hS_def

  haveI hS_fd : FiniteDimensional ℚ_[p] S :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)

  have hcompat : ∀ q : ℚ,
      (algebraMap ℚ_[p] L_v) ((algebraMap ℚ ℚ_[p]) q) = ι ((algebraMap ℚ L) q) :=
    fun q => RingHom.congr_fun (RingHom.ext_rat
      ((algebraMap ℚ_[p] L_v).comp (algebraMap ℚ ℚ_[p])) (ι.comp (algebraMap ℚ L))) q

  have hrange : Set.range ι ⊆ ↑S := by
    rintro _ ⟨l, rfl⟩
    rw [(b.sum_repr l).symm, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [Algebra.smul_def, map_mul, ← hcompat, ← Algebra.smul_def]
    exact Submodule.smul_mem S _ (Submodule.subset_span ⟨i, rfl⟩)

  have hS_closed : IsClosed (S : Set L_v) := Submodule.closed_of_finiteDimensional S

  have hS_top : S = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hS_univ : (S : Set L_v) = Set.univ :=
      Set.eq_univ_of_univ_subset
        (hdense.closure_range ▸ hS_closed.closure_subset_iff.mpr hrange)
    rw [← SetLike.mem_coe]; rw [hS_univ]; exact Set.mem_univ x

  rw [FiniteDimensional, Module.finite_def]
  exact ⟨(Set.Finite.toFinset (Set.finite_range (fun i => ι (b i)))), by
    rw [Set.Finite.coe_toFinset]; exact hS_top⟩

lemma properSpace_of_isCompact_closedBall_one {K : Type*} [NontriviallyNormedField K]
    (h : IsCompact (closedBall (0 : K) 1)) : ProperSpace K := by
  obtain ⟨c, hc⟩ := NontriviallyNormedField.non_trivial (α := K)
  have h_pow : ∀ n : ℕ, IsCompact (closedBall (0:K) (‖c‖^n)) := by
    intro n
    have hcn : c^n ≠ 0 := pow_ne_zero n (norm_pos_iff.mp (by linarith))
    have key : closedBall (0:K) (‖c‖^n) = (· * c^n) '' closedBall 0 1 := by
      ext y
      simp only [mem_image, mem_closedBall, dist_zero_right]
      constructor
      · intro hy
        refine ⟨y / c^n, ?_, ?_⟩
        · rw [norm_div, norm_pow]
          exact div_le_one_of_le₀ hy (pow_nonneg (norm_nonneg c) n)
        · field_simp
      · rintro ⟨x, hx, rfl⟩
        rw [norm_mul, norm_pow]
        nlinarith [pow_nonneg (norm_nonneg c) n]
    rw [key]
    exact IsCompact.image h (continuous_mul_const (c^n))
  apply ProperSpace.mk
  intro x r
  by_cases hr : r < 0
  · simp [closedBall_eq_empty.mpr hr]
  push Not at hr
  have hsub : closedBall x r ⊆ closedBall (0:K) (‖x‖ + r) := by
    intro y hy
    simp only [mem_closedBall, dist_zero_right] at *
    linarith [norm_sub_norm_le y x, show ‖y - x‖ ≤ r from by rwa [← dist_eq_norm]]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖x‖ + r ≤ ‖c‖^N := by
    have := tendsto_pow_atTop_atTop_of_one_lt hc
    rw [tendsto_atTop_atTop] at this
    obtain ⟨N, hN⟩ := this (‖x‖ + r)
    exact ⟨N, hN N le_rfl⟩
  exact (h_pow N).of_isClosed_subset isClosed_closedBall
    (hsub.trans (closedBall_subset_closedBall hN))





lemma normAbsValQ_equiv_real_implies_eq
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real)
    (hnorm_2 : ‖j (2 : ℚ)‖ = 2) :
    normAbsValQ j = Rat.AbsoluteValue.real :=
  normAbsValQ_isEquiv_real_eq j hequiv hnorm_2




