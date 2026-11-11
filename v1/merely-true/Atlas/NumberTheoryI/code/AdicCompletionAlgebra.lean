/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Ideal.Over
import Atlas.NumberTheoryI.code.CompleteFields

open IsDedekindDomain UniformSpace

set_option maxHeartbeats 800000

theorem algebraMap_withVal_continuous_general
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
    Continuous ((WithVal.equiv (𝔮.valuation L)).symm ∘
      (algebraMap K L) ∘ (WithVal.equiv (𝔭.valuation K)) :
      WithVal (𝔭.valuation K) → WithVal (𝔮.valuation L)) := by

  haveI : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := by
    constructor
    exact le_antisymm h𝔮_over_𝔭
      ((𝔭.isPrime.isMaximal 𝔭.ne_bot).eq_of_le
        (Ideal.IsPrime.comap (algebraMap A B)).ne_top h𝔮_over_𝔭).ge

  haveI : FaithfulSMul A B := by
    constructor
    intro m₁ m₂ h
    have h1 := h 1
    simp only [Algebra.smul_def, mul_one] at h1
    have hAL : Function.Injective (algebraMap A L) := by
      intro x y hxy
      rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at hxy
      exact (IsFractionRing.injective A K) ((algebraMap K L).injective hxy)
    have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
    have hAB : Function.Injective (algebraMap A B) := by
      intro a b hab
      apply hAL
      have ha : (algebraMap A L) a = (algebraMap B L) ((algebraMap A B) a) :=
        IsScalarTower.algebraMap_apply A B L a
      have hb : (algebraMap A L) b = (algebraMap B L) ((algebraMap A B) b) :=
        IsScalarTower.algebraMap_apply A B L b
      rw [ha, hb, hab]
    exact hAB h1

  have hval : ∀ x : K, 𝔮.valuation L (algebraMap K L x) =
      (𝔭.valuation K x) ^ (Ideal.ramificationIdx 𝔭.asIdeal 𝔮.asIdeal) :=
    fun x => valuation_extends_with_ramificationIdx K L 𝔭 𝔮 x
  let e := Ideal.ramificationIdx 𝔭.asIdeal 𝔮.asIdeal
  have he : e ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver 𝔮.asIdeal 𝔭.ne_bot

  let f : WithVal (𝔭.valuation K) →+* WithVal (𝔮.valuation L) :=
    (WithVal.equiv (𝔮.valuation L)).symm.toRingHom.comp
      ((algebraMap K L).comp (WithVal.equiv (𝔭.valuation K)).toRingHom)
  show Continuous f

  have hfv : ∀ x : WithVal (𝔭.valuation K),
      @Valued.v (WithVal (𝔮.valuation L)) _ _ _ _ (f x) =
      (@Valued.v (WithVal (𝔭.valuation K)) _ _ _ _ x) ^ e := by
    intro x
    rw [← WithVal.val_apply_equiv (𝔮.valuation L)]
    show 𝔮.valuation L ((WithVal.equiv (𝔮.valuation L)) ((WithVal.equiv (𝔮.valuation L)).symm
      (algebraMap K L ((WithVal.equiv (𝔭.valuation K)) x)))) = _
    rw [RingEquiv.apply_symm_apply, hval, ← WithVal.val_apply_equiv (𝔭.valuation K)]

  apply continuous_of_continuousAt_zero f.toAddMonoidHom
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]

  intro γ

  let M := MonoidWithZeroHom.ValueGroup₀.embedding (↑γ : MonoidWithZeroHom.ValueGroup₀
    (@Valued.v (WithVal (𝔮.valuation L)) _ _ _ _))
  have hM_ne : M ≠ 0 := by
    simp only [M, ne_eq, map_eq_zero]
    exact Units.ne_zero γ


  have multiplicative_toAdd_pow : ∀ (h : Multiplicative ℤ) (n : ℕ),
      Multiplicative.toAdd (h ^ n) = n * Multiplicative.toAdd h := by
    intro h n
    induction n with
    | zero => simp
    | succ k ih => simp [pow_succ, ih, add_mul, one_mul]

  obtain ⟨g, hgM⟩ := WithZero.ne_zero_iff_exists.mp hM_ne
  set n := Multiplicative.toAdd g
  set d : WithZero (Multiplicative ℤ) := ↑(Multiplicative.ofAdd (n / (e : ℤ))) with hd_def
  have hd_ne : d ≠ 0 := WithZero.coe_ne_zero
  have hd_pow : ∀ a : WithZero (Multiplicative ℤ), a < d → a ^ e < M := by
    intro a ha
    cases a with
    | zero => rw [zero_pow he]; rw [← hgM]; exact WithZero.zero_lt_coe g
    | coe h =>
      rw [WithZero.coe_lt_coe] at ha
      rw [← hgM, ← WithZero.coe_pow, WithZero.coe_lt_coe]
      suffices (e : ℤ) * Multiplicative.toAdd h < n by
        rwa [show h ^ e < g ↔ Multiplicative.toAdd (h ^ e) < n from Iff.rfl,
             multiplicative_toAdd_pow]
      have he_pos : (0 : ℤ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
      have hle : Multiplicative.toAdd h ≤ n / (e : ℤ) - 1 :=
        Int.le_sub_one_of_lt ha
      calc (e : ℤ) * Multiplicative.toAdd h
          ≤ (e : ℤ) * (n / (e : ℤ) - 1) := mul_le_mul_of_nonneg_left hle he_pos.le
        _ = (e : ℤ) * (n / (e : ℤ)) - (e : ℤ) := by ring
        _ ≤ n - 1 := by linarith [Int.ediv_mul_le n he_pos.ne']
        _ < n := by omega

  obtain ⟨y, hy⟩ := 𝔭.valuation_surjective K d
  set y' : WithVal (𝔭.valuation K) := (WithVal.equiv (𝔭.valuation K)).symm y with hy'_def
  set δ_vg := MonoidWithZeroHom.ValueGroup₀.restrict₀
    (@Valued.v (WithVal (𝔭.valuation K)) _ _ _ _) y' with hδ_vg_def
  have hδ_emb : MonoidWithZeroHom.ValueGroup₀.embedding δ_vg = d := by
    rw [hδ_vg_def, MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
    show @Valued.v (WithVal (𝔭.valuation K)) _ _ _ _ y' = d
    rw [← WithVal.val_apply_equiv (𝔭.valuation K), hy'_def]
    simp [hy]
  have hδ_ne : δ_vg ≠ 0 := by
    intro h; rw [h, map_zero] at hδ_emb; exact hd_ne hδ_emb.symm
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact hd_ne hy.symm
  set y'_inv : WithVal (𝔭.valuation K) := (WithVal.equiv (𝔭.valuation K)).symm y⁻¹
  have hδ_unit : IsUnit δ_vg := by
    rw [isUnit_iff_exists_inv]
    use MonoidWithZeroHom.ValueGroup₀.restrict₀
      (@Valued.v (WithVal (𝔭.valuation K)) _ _ _ _) y'_inv
    rw [← map_mul]
    have : y' * y'_inv = 1 := by
      show (WithVal.equiv (𝔭.valuation K)).symm y *
        (WithVal.equiv (𝔭.valuation K)).symm y⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    rw [this, map_one]
  obtain ⟨δ, hδ⟩ := hδ_unit
  use δ
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rw [hδ, hδ_emb] at hx
  change @Valued.v (WithVal (𝔮.valuation L)) _ _ _ _ (f x) < M
  rw [hfv]
  exact hd_pow _ hx

namespace AdicCompletionAlgebra

theorem continuous_algebraMap_adicCompletion
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
    Continuous ((algebraMap L (𝔮.adicCompletion L)).comp
      ((algebraMap K L).comp (WithVal.equiv (𝔭.valuation K)).toRingHom) :
      WithVal (𝔭.valuation K) → 𝔮.adicCompletion L) := by

  suffices h : Continuous ((Completion.coe' : WithVal (𝔮.valuation L) → 𝔮.adicCompletion L) ∘
    ((WithVal.equiv (𝔮.valuation L)).symm ∘ (algebraMap K L) ∘
    (WithVal.equiv (𝔭.valuation K)))) by
    refine h.congr ?_
    intro x
    simp only [Function.comp, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    have := congr_fun (HeightOneSpectrum.algebraMap_adicCompletion (S := L) B L 𝔮)
      ((algebraMap K L) ((WithVal.equiv (𝔭.valuation K)) x))
    simp only [Function.comp] at this
    exact this.symm
  exact (Completion.continuous_coe _).comp
    (algebraMap_withVal_continuous_general K 𝔭 𝔮 h𝔮_over_𝔭)

noncomputable def adicCompletionMap
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
    𝔭.adicCompletion K →+* 𝔮.adicCompletion L :=
  Completion.extensionHom
    ((algebraMap L (𝔮.adicCompletion L)).comp
      ((algebraMap K L).comp (WithVal.equiv (𝔭.valuation K)).toRingHom))
    (continuous_algebraMap_adicCompletion K 𝔭 𝔮 h𝔮_over_𝔭)

theorem adicCompletionMap_comp_algebraMap
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
    (adicCompletionMap K 𝔭 𝔮 h𝔮_over_𝔭).comp (algebraMap K (𝔭.adicCompletion K)) =
      (algebraMap L (𝔮.adicCompletion L)).comp (algebraMap K L) := by
  ext x
  simp only [RingHom.comp_apply, adicCompletionMap]
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp]
  rw [Completion.extensionHom_coe]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  simp [WithVal.equiv]

end AdicCompletionAlgebra

@[reducible]
noncomputable def instAlgebraAdicCompletionOfLiesOver
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
    Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L) :=
  (AdicCompletionAlgebra.adicCompletionMap K 𝔭 𝔮 h𝔮_over_𝔭).toAlgebra

theorem isScalarTower_adicCompletion
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
    @IsScalarTower K (𝔭.adicCompletion K) (𝔮.adicCompletion L) _
      (instAlgebraAdicCompletionOfLiesOver K 𝔭 𝔮 h𝔮_over_𝔭).toSMul _ := by
  letI : Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L) :=
    instAlgebraAdicCompletionOfLiesOver K 𝔭 𝔮 h𝔮_over_𝔭
  apply IsScalarTower.of_algebraMap_eq' (R := K) (S := 𝔭.adicCompletion K)
    (A := 𝔮.adicCompletion L)
  ext x
  change (algebraMap K (𝔮.adicCompletion L)) x =
    (AdicCompletionAlgebra.adicCompletionMap K 𝔭 𝔮 h𝔮_over_𝔭)
      ((algebraMap K (𝔭.adicCompletion K)) x)
  rw [← RingHom.comp_apply,
      AdicCompletionAlgebra.adicCompletionMap_comp_algebraMap K 𝔭 𝔮 h𝔮_over_𝔭,
      RingHom.comp_apply,
      IsScalarTower.algebraMap_apply K L (𝔮.adicCompletion L)]
