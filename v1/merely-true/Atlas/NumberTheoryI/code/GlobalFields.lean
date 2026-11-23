/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Atlas.NumberTheoryI.code.CompleteFields
import Atlas.NumberTheoryI.code.KroneckerWeber

noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

namespace AbsoluteValue

variable {K : Type*} [Field K]

def IsTrivial (v : AbsoluteValue K ℝ) : Prop :=
  ∀ x : K, x ≠ 0 → v x = 1

theorem IsTrivial.map_ne_zero {v : AbsoluteValue K ℝ} (hv : v.IsTrivial) {x : K}
    (hx : x ≠ 0) : v x = 1 :=
  hv x hx

theorem IsTrivial.of_isEquiv {v w : AbsoluteValue K ℝ} (hv : v.IsTrivial) (h : v.IsEquiv w) :
    w.IsTrivial := by
  intro x hx
  have h0 : v x = v 1 := by rw [hv x hx, map_one]
  have h1 := h.eq_iff_eq.mp h0
  rw [map_one] at h1
  exact h1

end AbsoluteValue

section Place

variable (K : Type*) [Field K]

instance nontrivialAbsValSetoid :
    Setoid { v : AbsoluteValue K ℝ // ¬v.IsTrivial } where
  r v w := v.val.IsEquiv w.val
  iseqv := {
    refl := fun _ => AbsoluteValue.IsEquiv.refl _
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

def Place := Quotient (nontrivialAbsValSetoid K)

end Place

section PlaceExtension

def restrictPlace {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : NumberField.InfinitePlace L) : NumberField.InfinitePlace K :=
  w.comap (algebraMap K L)

def InfinitePlace.LiesAbove {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K) : Prop :=
  restrictPlace w = v

def FinitePlace.LiesAbove {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal

end PlaceExtension

instance instAlgebraBaseOfExtCompletion {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L] (w : NumberField.InfinitePlace L) :
    Algebra K w.Completion :=
  ((algebraMap L w.Completion).comp (algebraMap K L)).toAlgebra

instance instAlgebraBaseOfExtAdicCompletion {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    Algebra K (w.adicCompletion L) := inferInstance

section TensorProductDecomposition

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 80000

theorem theorem_13_5_dense_embedding (K : Type*) [Field K] [NumberField K] :
    DenseRange (algebraMap K ((v : NumberField.InfinitePlace K) → WithAbs v.1)) :=
  denseRange_algebraMap_pi K

def algebraMapLToCompletion {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L] (w : NumberField.InfinitePlace L) :
    L →ₐ[K] w.Completion where
  toFun := algebraMap L w.Completion
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun _ => rfl

set_option backward.isDefEq.respectTransparency false in
def completionEmbedding {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K)
    (w : NumberField.InfinitePlace L) (hw : w.comap (algebraMap K L) = v) :
    v.Completion →ₐ[K] w.Completion := by
  haveI : w.1.LiesOver v.1 := ⟨by
    have : (w.comap (algebraMap K L)).1 = v.1 := by rw [hw]
    rw [← this]; rfl⟩
  let iso := LiesOver.isometry_algebraMap w (v := v)
  let f : v.Completion →+* w.Completion := iso.mapRingHom
  exact {
    toRingHom := f
    commutes' := by
      intro r
      show f (algebraMap K v.Completion r) = algebraMap K w.Completion r
      change f (↑(algebraMap K (WithAbs v.1) r)) = ↑(algebraMap K (WithAbs w.1) r)
      rw [iso.mapRingHom_coe]
      congr 1
  }

def canonicalMap {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    TensorProduct K L v.Completion →ₐ[K]
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) :=
  Pi.algHom K
    (fun (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) =>
      w.val.Completion)
    (fun (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) =>
      Algebra.TensorProduct.productMap
        (algebraMapLToCompletion w.val)
        (completionEmbedding v w.val w.prop))

instance nontriviallyNormedField_infinitePlace_completion {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) : NontriviallyNormedField v.Completion := by
  constructor; use 2
  have h1 : Completion.extensionEmbedding v 2 = (2 : ℂ) := by simp [map_ofNat]
  have h2 : ‖(2 : v.Completion)‖ = ‖(2 : ℂ)‖ := by
    rw [← h1]
    exact ((Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) 2).symm
  rw [h2]; norm_num

set_option backward.isDefEq.respectTransparency false in
theorem completionEmbedding_continuous {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K)
    (w : NumberField.InfinitePlace L) (hw : w.comap (algebraMap K L) = v) :
    Continuous (completionEmbedding v w hw) := by
  simp only [completionEmbedding, Isometry.mapRingHom, UniformSpace.Completion.mapRingHom]
  exact UniformSpace.Completion.continuous_extension

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 40000 in
theorem canonicalMap_surjective_hfd_tgt {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    @FiniteDimensional v.Completion
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) _ _
      (@Pi.module
        { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }
        (fun w => w.val.Completion) v.Completion _ _
        (fun w => (completionEmbedding v w.val w.prop).toAlgebra.toModule)) := by


  have h_fin : ∀ (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }),
    @Module.Finite v.Completion w.val.Completion _ _
      (completionEmbedding v w.val w.prop).toAlgebra.toModule := by
    intro w
    letI myAlg : Algebra v.Completion w.val.Completion :=
      (completionEmbedding v w.val w.prop).toAlgebra
    letI mySMul : SMul v.Completion w.val.Completion := myAlg.toSMul
    haveI : ContinuousMul w.val.Completion :=
      (inferInstance : IsTopologicalRing w.val.Completion).toContinuousMul
    haveI : @ContinuousSMul v.Completion w.val.Completion mySMul _ _ := by
      refine ⟨?_⟩
      show Continuous (fun p : v.Completion × w.val.Completion =>
        completionEmbedding v w.val w.prop p.1 * p.2)
      exact ((completionEmbedding_continuous v w.val w.prop).comp continuous_fst).mul continuous_snd
    exact @FiniteDimensional.of_locallyCompactSpace v.Completion _ _ w.val.Completion _ _ _ _
      myAlg.toModule this _

  exact @Module.Finite.pi v.Completion _
    { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }
    (fun w => w.val.Completion) _
    (fun w => inferInstance)
    (fun w => (completionEmbedding v w.val w.prop).toAlgebra.toModule)
    h_fin







theorem canonicalMap_tmul_one {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) (l : L)
    (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) :
    (canonicalMap (L := L) v) (l ⊗ₜ[K] 1) w = algebraMap L w.val.Completion l := by
  simp only [canonicalMap, Pi.algHom_apply,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, algebraMapLToCompletion]
  exact mul_one _

set_option maxHeartbeats 8000000



def completionEmbedding_finite_ringHom {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) :
    WithVal (v.valuation K) →+* w.adicCompletion L :=
  (algebraMap K (w.adicCompletion L)).comp (WithVal.equiv (v.valuation K)).toRingHom


lemma multiplicative_toAdd_pow (h : Multiplicative ℤ) (e : ℕ) :
    Multiplicative.toAdd (h ^ e) = e * Multiplicative.toAdd h := by
  induction e with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, add_mul, one_mul]


lemma exists_pow_lt_of_ne_zero (m : WithZero (Multiplicative ℤ)) (hm : m ≠ 0)
    (e : ℕ) (he : e ≠ 0) :
    ∃ d : WithZero (Multiplicative ℤ), d ≠ 0 ∧ ∀ a : WithZero (Multiplicative ℤ),
      a < d → a ^ e < m := by
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.mp hm
  set n := Multiplicative.toAdd g
  use ↑(Multiplicative.ofAdd (n / (e : ℤ)))
  refine ⟨WithZero.coe_ne_zero, fun a ha => ?_⟩
  cases a with
  | zero => rw [zero_pow he]; exact WithZero.zero_lt_coe g
  | coe h =>
    rw [WithZero.coe_lt_coe] at ha
    rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
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

set_option maxHeartbeats 1600000 in
theorem algebraMap_withVal_continuous {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hw : FinitePlace.LiesAbove w v) :
    Continuous
      ((WithVal.equiv (w.valuation L)).symm.toRingHom.comp
        ((algebraMap K L).comp (WithVal.equiv (v.valuation K)).toRingHom) :
        WithVal (v.valuation K) →+* WithVal (w.valuation L)) := by

  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩

  have hval : ∀ x : K, w.valuation L (algebraMap K L x) =
      (v.valuation K x) ^ (Ideal.ramificationIdx v.asIdeal w.asIdeal) :=
    fun x => valuation_extends_with_ramificationIdx K L v w x
  let e := Ideal.ramificationIdx v.asIdeal w.asIdeal
  have he : e ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot

  let f : WithVal (v.valuation K) →+* WithVal (w.valuation L) :=
    (WithVal.equiv (w.valuation L)).symm.toRingHom.comp
      ((algebraMap K L).comp (WithVal.equiv (v.valuation K)).toRingHom)
  show Continuous f

  have hfv : ∀ x : WithVal (v.valuation K),
      @Valued.v (WithVal (w.valuation L)) _ _ _ _ (f x) =
      (@Valued.v (WithVal (v.valuation K)) _ _ _ _ x) ^ e := by
    intro x
    rw [← WithVal.val_apply_equiv (w.valuation L)]
    show w.valuation L ((WithVal.equiv (w.valuation L)) ((WithVal.equiv (w.valuation L)).symm
      (algebraMap K L ((WithVal.equiv (v.valuation K)) x)))) = _
    rw [RingEquiv.apply_symm_apply, hval, ← WithVal.val_apply_equiv (v.valuation K)]

  apply continuous_of_continuousAt_zero f.toAddMonoidHom
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]

  intro γ


  set M := MonoidWithZeroHom.ValueGroup₀.embedding (↑γ : MonoidWithZeroHom.ValueGroup₀
    (@Valued.v (WithVal (w.valuation L)) _ _ _ _)) with hM_def
  have hM_ne : M ≠ 0 := by
    simp only [M, ne_eq, map_eq_zero]
    exact Units.ne_zero γ

  obtain ⟨d, hd_ne, hd_pow⟩ := exists_pow_lt_of_ne_zero M hM_ne e he


  obtain ⟨y, hy⟩ := v.valuation_surjective K d

  set y' : WithVal (v.valuation K) := (WithVal.equiv (v.valuation K)).symm y with hy'_def

  set δ_vg := MonoidWithZeroHom.ValueGroup₀.restrict₀
    (@Valued.v (WithVal (v.valuation K)) _ _ _ _) y' with hδ_vg_def

  have hδ_emb : MonoidWithZeroHom.ValueGroup₀.embedding δ_vg = d := by
    rw [hδ_vg_def, MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
    show @Valued.v (WithVal (v.valuation K)) _ _ _ _ y' = d
    rw [← WithVal.val_apply_equiv (v.valuation K), hy'_def]
    simp [hy]

  have hδ_ne : δ_vg ≠ 0 := by
    intro h; rw [h, map_zero] at hδ_emb; exact hd_ne hδ_emb.symm
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact hd_ne hy.symm

  set y'_inv : WithVal (v.valuation K) := (WithVal.equiv (v.valuation K)).symm y⁻¹
  have hδ_unit : IsUnit δ_vg := by
    rw [isUnit_iff_exists_inv]
    use MonoidWithZeroHom.ValueGroup₀.restrict₀
      (@Valued.v (WithVal (v.valuation K)) _ _ _ _) y'_inv
    rw [← map_mul]
    have : y' * y'_inv = 1 := by
      show (WithVal.equiv (v.valuation K)).symm y *
        (WithVal.equiv (v.valuation K)).symm y⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    rw [this, map_one]
  obtain ⟨δ, hδ⟩ := hδ_unit
  use δ
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢

  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢


  rw [hδ, hδ_emb] at hx

  change @Valued.v (WithVal (w.valuation L)) _ _ _ _ (f x) < M

  rw [hfv]

  exact hd_pow _ hx

theorem completionEmbedding_finite_continuous {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    Continuous (completionEmbedding_finite_ringHom v w) := by


  let g : WithVal (v.valuation K) → WithVal (w.valuation L) :=
    fun x => (WithVal.equiv (w.valuation L)).symm
      (algebraMap K L ((WithVal.equiv (v.valuation K)) x))
  have hg : Continuous g := algebraMap_withVal_continuous v w hw
  have hcoe : Continuous (fun x : WithVal (w.valuation L) => (↑x : w.adicCompletion L)) :=
    (UniformSpace.Completion.uniformContinuous_coe _).continuous
  have heq : (completionEmbedding_finite_ringHom v w : WithVal (v.valuation K) → w.adicCompletion L) =
      (fun x : WithVal (w.valuation L) => (↑x : w.adicCompletion L)) ∘ g := by
    funext x
    simp only [g, completionEmbedding_finite_ringHom, Function.comp, RingHom.coe_comp,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    rfl
  rw [show (↑(completionEmbedding_finite_ringHom v w) :
    WithVal (v.valuation K) → w.adicCompletion L) =
    (fun x : WithVal (w.valuation L) => (↑x : w.adicCompletion L)) ∘ g from heq]
  exact hcoe.comp hg

def completionEmbedding_finite {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    v.adicCompletion K →ₐ[K] w.adicCompletion L :=
  AlgHom.mk'
    (UniformSpace.Completion.extensionHom
      (completionEmbedding_finite_ringHom v w)
      (completionEmbedding_finite_continuous v w hw))
    (fun k x => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      show (UniformSpace.Completion.extensionHom
        (completionEmbedding_finite_ringHom v w)
        (completionEmbedding_finite_continuous v w hw))
        (algebraMap K (v.adicCompletion K) k) =
        algebraMap K (w.adicCompletion L) k
      have : algebraMap K (v.adicCompletion K) k =
        (↑(algebraMap K (WithVal (v.valuation K)) k) : v.adicCompletion K) := rfl
      rw [this, UniformSpace.Completion.extensionHom_coe]
      rfl)

def algebraMapLToAdicCompletion {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    L →ₐ[K] w.adicCompletion L where
  toFun := algebraMap L (w.adicCompletion L)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun _ => rfl

def canonicalMap_finite {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    TensorProduct K L (v.adicCompletion K) →ₐ[K]
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L) :=
  Pi.algHom K
    (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) =>
      w.val.adicCompletion L)
    (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) =>
      Algebra.TensorProduct.productMap
        (algebraMapLToAdicCompletion w.val)
        (completionEmbedding_finite v w.val w.prop))

set_option synthInstance.maxHeartbeats 80000 in
theorem prop_4_36_tensorProduct_finite_isSemisimpleRing
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsSemisimpleRing (TensorProduct K L (v.adicCompletion K)) := by

  haveI : Algebra.Unramified K L :=
    ⟨Algebra.FormallyUnramified.of_isSeparable K L, inferInstance⟩

  haveI := (Algebra.Unramified.baseChange K L (v.adicCompletion K)).formallyUnramified

  haveI : IsReduced (TensorProduct K (v.adicCompletion K) L) :=
    Algebra.FormallyUnramified.isReduced_of_field (v.adicCompletion K) _

  haveI : IsArtinianRing (TensorProduct K (v.adicCompletion K) L) :=
    IsArtinianRing.of_finite (v.adicCompletion K) _

  haveI : IsSemisimpleRing (TensorProduct K (v.adicCompletion K) L) :=
    @IsArtinianRing.isSemisimpleRing_of_isReduced _ _ _ _

  exact (Algebra.TensorProduct.comm K L (v.adicCompletion K)).toRingEquiv.symm.isSemisimpleRing

theorem finitePlacesAbove_finite
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Finite { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } := by
  haveI := v.isMaximal
  apply Finite.of_injective
    (fun ⟨w, hw⟩ => (⟨w.asIdeal, w.isPrime, ⟨hw.symm⟩⟩ : Ideal.primesOver v.asIdeal (𝓞 L)))
  intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (HeightOneSpectrum.ext_iff.mpr h)

theorem prop_10_3_10_4_finiteDimensional_completion
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    letI := (completionEmbedding_finite v w hw).toAlgebra
    FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) := by
  letI := (completionEmbedding_finite v w hw).toAlgebra
  haveI : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) := by
    apply continuousSMul_of_algebraMap
    show Continuous (completionEmbedding_finite v w hw).toRingHom
    exact UniformSpace.Completion.continuous_extension
  haveI : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap K (w.adicCompletion L) x =
      (completionEmbedding_finite v w hw) (algebraMap K (v.adicCompletion K) x)
    rw [AlgHom.commutes]
  exact inferInstance




theorem canonicalMap_finite_isKvLinear
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
      Algebra.TensorProduct.rightAlgebra
    letI : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
        Module (v.adicCompletion K) (w.val.adicCompletion L) :=
      fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra.toModule
    ∃ f : TensorProduct K L (v.adicCompletion K) →ₗ[v.adicCompletion K]
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L),
      (∀ x, f x = (canonicalMap_finite (L := L) v) x) := by
  letI instSrc : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
    Algebra.TensorProduct.rightAlgebra
  letI instTgt : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Module (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra.toModule
  letI instPiMod : Module (v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L) :=
    @Pi.module _ (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) =>
      w.val.adicCompletion L) (v.adicCompletion K) _ _ instTgt
  have hsmul : ∀ (c : v.adicCompletion K) (x : TensorProduct K L (v.adicCompletion K)),
    (canonicalMap_finite (L := L) v) (c • x) =
      @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * 0) = _
      rw [mul_zero, map_zero]
      exact (@smul_zero _ _ _
        instPiMod.toDistribMulAction.toDistribSMul.toSMulZeroClass c).symm

    | tmul l y =>
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * (l ⊗ₜ y)) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      ext ⟨w, hw⟩
      simp only [canonicalMap_finite, Pi.algHom_apply,
        Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      exact mul_left_comm _ _ _
    | add a b ha hb =>
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * (a + b)) =
        @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) (a + b))
      rw [mul_add, map_add, map_add]
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * a) +
        (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * b) =
        @SMul.smul _ _ instPiMod.toSMul c
          ((canonicalMap_finite (L := L) v) a + (canonicalMap_finite (L := L) v) b)
      rw [show (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * a) =
        @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) a) from ha,
        show (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * b) =
        @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) b) from hb]
      exact (@smul_add _ _ _
        instPiMod.toDistribMulAction.toDistribSMul c
        ((canonicalMap_finite v) a) ((canonicalMap_finite v) b)).symm
  exact ⟨{ toFun := canonicalMap_finite v
           map_add' := (canonicalMap_finite v).map_add
           map_smul' := hsmul }, fun _ => rfl⟩









theorem completion_real_ringEquiv {K : Type*} [Field K]
    {w : NumberField.InfinitePlace K} (hw : w.IsReal) :
    Nonempty (w.Completion ≃+* ℝ) :=
  ⟨NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw⟩

theorem completion_complex_ringEquiv {K : Type*} [Field K]
    {w : NumberField.InfinitePlace K} (hw : w.IsComplex) :
    Nonempty (w.Completion ≃+* ℂ) :=
  ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw⟩

end TensorProductDecomposition

section IrreducibleFactorsAndPlaces

open Polynomial UniqueFactorizationMonoid Classical




theorem corollary_13_6_factor_count (K : Type*) [Field K] [NumberField K] :
    Fintype.card (NumberField.InfinitePlace K) =
      nrRealPlaces K + nrComplexPlaces K :=
  card_eq_nrRealPlaces_add_nrComplexPlaces K








end IrreducibleFactorsAndPlaces

section GaloisOrbitsAndPlaces

def corollary_13_7_orbit_equiv
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsGalois k K] :
    Quotient (MulAction.orbitRel (K ≃ₐ[k] K) (NumberField.InfinitePlace K)) ≃
      NumberField.InfinitePlace k :=
  InfinitePlace.orbitRelEquiv

theorem corollary_13_7_mem_orbit_iff
    {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {w w' : NumberField.InfinitePlace K} :
    w' ∈ MulAction.orbit (K ≃ₐ[k] K) w ↔
      w.comap (algebraMap k K) = w'.comap (algebraMap k K) :=
  InfinitePlace.mem_orbit_iff

theorem corollary_13_7_exists_smul_eq
    {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {w w' : NumberField.InfinitePlace K}
    (h : w.comap (algebraMap k K) = w'.comap (algebraMap k K)) :
    ∃ σ : K ≃ₐ[k] K, σ • w = w' :=
  InfinitePlace.exists_smul_eq_of_comap_eq h

theorem corollary_13_7_comap_surjective
    (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    Function.Surjective
      (InfinitePlace.comap · (algebraMap k K) : InfinitePlace K → InfinitePlace k) :=
  InfinitePlace.comap_surjective

theorem corollary_13_7_mk_eq_iff {K : Type*} [Field K] {φ ψ : K →+* ℂ} :
    InfinitePlace.mk φ = InfinitePlace.mk ψ ↔
      φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ :=
  InfinitePlace.mk_eq_iff

theorem place_isReal_or_isComplex {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) : w.IsReal ∨ w.IsComplex :=
  InfinitePlace.isReal_or_isComplex w

def ComplexEmbedding.conjugateSetoid (L : Type*) [Field L] :
    Setoid (L →+* ℂ) where
  r φ ψ := InfinitePlace.mk φ = InfinitePlace.mk ψ
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

theorem ComplexEmbedding.conjugateSetoid_rel_iff {L : Type*} [Field L]
    {φ ψ : L →+* ℂ} :
    (ComplexEmbedding.conjugateSetoid L).r φ ψ ↔
      (φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ) :=
  mk_eq_iff

def corollary_13_7_embedding_orbit_equiv_Q (L : Type*) [Field L] :
    Quotient (ComplexEmbedding.conjugateSetoid L) ≃
      NumberField.InfinitePlace L where
  toFun := Quotient.lift InfinitePlace.mk (fun _ _ h => h)
  invFun w := Quotient.mk (ComplexEmbedding.conjugateSetoid L) w.embedding
  left_inv := by
    intro q
    exact Quotient.inductionOn q fun φ => by
      simp only [Quotient.lift_mk]
      exact Quotient.sound (mk_embedding (mk φ))
  right_inv := by
    intro w
    simp only [Quotient.lift_mk]
    exact w.mk_embedding

def EmbeddingsAbove (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) : Type _ :=
  { φ : L →+* ℂ // (InfinitePlace.mk φ).comap (algebraMap K L) = v }

def conjugateSetoidAbove {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    Setoid (EmbeddingsAbove K v (L := L)) where
  r φ ψ := InfinitePlace.mk φ.val = InfinitePlace.mk ψ.val
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

def corollary_13_7_embeddings_equiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    Quotient (conjugateSetoidAbove v (K := K) (L := L)) ≃
      { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v } where
  toFun := Quotient.lift
    (fun (φ : EmbeddingsAbove K v) =>
      (⟨InfinitePlace.mk φ.val, by rw [comap_mk]; exact φ.prop⟩ :
        { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }))
    (fun φ ψ (h : InfinitePlace.mk φ.val = InfinitePlace.mk ψ.val) => by
      simp only [Subtype.mk.injEq]
      exact h)
  invFun w := by
    refine Quotient.mk (conjugateSetoidAbove v) ⟨w.val.embedding, ?_⟩
    rw [comap_mk]
    rw [← comap_mk]
    rw [w.val.mk_embedding]
    exact w.prop
  left_inv := by
    intro q
    exact Quotient.inductionOn q fun ⟨φ, hφ⟩ => by
      simp only [Quotient.lift_mk]
      apply Quotient.sound
      show InfinitePlace.mk (InfinitePlace.mk φ).embedding = InfinitePlace.mk φ
      exact (InfinitePlace.mk φ).mk_embedding
  right_inv := by
    intro ⟨w, hw⟩
    simp only [Quotient.lift_mk, Subtype.mk.injEq]
    exact w.mk_embedding

end GaloisOrbitsAndPlaces

section RealComplexEmbeddings

variable {K : Type*} [Field K]

abbrev IsRealEmbedding (φ : K →+* ℂ) : Prop := ComplexEmbedding.IsReal φ

abbrev IsComplexEmbedding (φ : K →+* ℂ) : Prop := ¬ ComplexEmbedding.IsReal φ

theorem isRealEmbedding_iff_isReal_place {φ : K →+* ℂ} :
    IsRealEmbedding φ ↔ (InfinitePlace.mk φ).IsReal := by
  constructor
  · intro h
    exact ⟨φ, h, rfl⟩
  · intro h
    exact InfinitePlace.isReal_of_mk_isReal h

theorem isComplexEmbedding_iff_isComplex_place {φ : K →+* ℂ} :
    IsComplexEmbedding φ ↔ (InfinitePlace.mk φ).IsComplex := by
  rw [IsComplexEmbedding, ← InfinitePlace.not_isReal_iff_isComplex]
  exact not_congr isRealEmbedding_iff_isReal_place

end RealComplexEmbeddings

section DegreeFormula

theorem corollary_13_9 (K : Type*) [Field K] [NumberField K] :
    nrRealPlaces K + 2 * nrComplexPlaces K = finrank ℚ K :=
  card_add_two_mul_card_eq_rank K

open Classical in
theorem card_complex_embeddings_eq (K : Type*) [Field K] [NumberField K] :
    card { φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ } = 2 * nrComplexPlaces K :=
  card_complex_embeddings K

open Classical in
theorem card_real_embeddings_eq (K : Type*) [Field K] [NumberField K] :
    card { φ : K →+* ℂ // ComplexEmbedding.IsReal φ } = nrRealPlaces K :=
  card_real_embeddings K

end DegreeFormula

section DiscriminantSign

theorem proposition_13_11 (K : Type*) [Field K] [NumberField K] :
    (NumberField.discr K).sign = (-1) ^ nrComplexPlaces K :=
  NumberField.sign_discr K

theorem discr_ne_zero' (K : Type*) [Field K] [NumberField K] :
    NumberField.discr K ≠ 0 :=
  NumberField.discr_ne_zero K

end DiscriminantSign


alias tensorProductDecomp_denseRange := theorem_13_5_dense_embedding


alias infinitePlace_card_eq_real_add_complex := corollary_13_6_factor_count


alias galoisOrbit_infinitePlace_equiv := corollary_13_7_orbit_equiv
alias infinitePlace_mem_orbit_iff_comap_eq := corollary_13_7_mem_orbit_iff
alias infinitePlace_exists_smul_eq_of_comap_eq := corollary_13_7_exists_smul_eq
alias infinitePlace_comap_surjective := corollary_13_7_comap_surjective
alias infinitePlace_mk_eq_iff_conjugate := corollary_13_7_mk_eq_iff
alias conjugateOrbit_equiv_infinitePlace := corollary_13_7_embedding_orbit_equiv_Q
alias conjugateOrbitAbove_equiv_placesAbove := corollary_13_7_embeddings_equiv


alias nrRealPlaces_add_two_nrComplexPlaces_eq_finrank := corollary_13_9


alias discr_sign_eq_neg_one_pow_nrComplexPlaces := proposition_13_11


alias tensorProduct_isSemisimpleRing_finitePlace := prop_4_36_tensorProduct_finite_isSemisimpleRing
alias completionEmbedding_finiteDimensional := prop_10_3_10_4_finiteDimensional_completion
alias completionProd_finiteDimensional_infinitePlace := canonicalMap_surjective_hfd_tgt
alias canonicalMap_finite_completionLinear := canonicalMap_finite_isKvLinear

end
