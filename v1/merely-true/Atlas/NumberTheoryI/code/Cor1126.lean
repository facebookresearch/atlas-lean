/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.GlobalFields
import Atlas.NumberTheoryI.code.CompleteFields

noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

theorem algebraMap_valuation_le_one {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hw : FinitePlace.LiesAbove w v)
    (k : K) (hk : v.valuation K k ≤ 1) :
    w.valuation L (algebraMap K L k) ≤ 1 := by
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  rw [valuation_extends_with_ramificationIdx K L v w k]
  exact pow_le_one₀ (WithZero.zero_le _) hk

set_option synthInstance.maxHeartbeats 80000

instance adicCompletionIntegers_algebra_over_base {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    Algebra (𝓞 K) (w.adicCompletionIntegers L) :=
  RingHom.toAlgebra
    ((algebraMap (𝓞 L) (w.adicCompletionIntegers L)).comp (algebraMap (𝓞 K) (𝓞 L)))

instance adicCompletionIntegers_isScalarTower_base {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    IsScalarTower (𝓞 K) (𝓞 L) (w.adicCompletionIntegers L) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem completionEmbedding_finite_mem_integers {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v)
    (x : v.adicCompletionIntegers K) :
    (completionEmbedding_finite v w hw) x.val ∈ w.adicCompletionIntegers L := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hx_mem := x.prop
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx_mem


  let emb := completionEmbedding_finite v w hw

  have hclosed : IsClosed {y : v.adicCompletion K |
      Valued.v y ≤ 1 → Valued.v (emb y) ≤ 1} := by


    have h1 : {y : v.adicCompletion K | Valued.v y ≤ 1 → Valued.v (emb y) ≤ 1} =
        {y | ¬(Valued.v y ≤ 1)} ∪ {y | Valued.v (emb y) ≤ 1} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_union]
      tauto
    rw [h1]
    apply IsClosed.union
    ·

      have : {y : v.adicCompletion K | ¬(Valued.v y ≤ 1)} =
          ((Valued.v.valuationSubring : ValuationSubring (v.adicCompletion K)) :
            Set (v.adicCompletion K))ᶜ := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClopen_valuationSubring (v.adicCompletion K)).2.isClosed_compl
    ·
      have hemb_cont : Continuous (emb : v.adicCompletion K → w.adicCompletion L) := by
        show Continuous (UniformSpace.Completion.extensionHom
          (completionEmbedding_finite_ringHom v w)
          (completionEmbedding_finite_continuous v w hw))
        exact UniformSpace.Completion.continuous_extension
      have : {y : v.adicCompletion K | Valued.v (emb y) ≤ 1} =
          (emb : v.adicCompletion K → w.adicCompletion L) ⁻¹'
            ((Valued.v.valuationSubring : ValuationSubring (w.adicCompletion L)) :
              Set (w.adicCompletion L)) := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClosed_valuationSubring (w.adicCompletion L)).preimage hemb_cont

  have hdense : ∀ (k : WithVal (v.valuation K)),
      Valued.v (↑k : v.adicCompletion K) ≤ 1 →
        Valued.v (emb (↑k : v.adicCompletion K)) ≤ 1 := by
    intro k hk
    rw [Valued.valuedCompletion_apply] at hk

    have hemb : (emb (↑k : v.adicCompletion K)) = completionEmbedding_finite_ringHom v w k :=
      UniformSpace.Completion.extensionHom_coe _ (completionEmbedding_finite_continuous v w hw) k
    rw [hemb]


    have hval : Valued.v ((completionEmbedding_finite_ringHom v w) k) =
        w.valuation L (algebraMap K L ((WithVal.equiv (v.valuation K)) k)) := by
      simp only [completionEmbedding_finite_ringHom, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      simp only [Function.comp_apply]
      exact Valued.valuedCompletion_apply _
    rw [hval]
    exact algebraMap_valuation_le_one v w hw _ hk

  exact UniformSpace.Completion.induction_on (x : v.adicCompletion K) hclosed
    (fun k => hdense k) hx_mem

theorem completionEmbedding_finite_commutes {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v)
    (r : 𝓞 K) :
    (completionEmbedding_finite v w hw)
      ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) r).val) =
    ((algebraMap (𝓞 K) (w.adicCompletionIntegers L) r).val) := by
  have h_lhs : (completionEmbedding_finite v w hw)
      ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) r).val) =
    algebraMap K (w.adicCompletion L) (algebraMap (𝓞 K) K r) := by
    rw [← AlgHom.commutes (completionEmbedding_finite v w hw)]
    congr 1
  rw [h_lhs]
  rw [IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) K L]
  rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
  rfl

def completionEmbeddingIntegers {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    v.adicCompletionIntegers K →ₐ[𝓞 K] w.adicCompletionIntegers L where
  toFun x := ⟨(completionEmbedding_finite v w hw) x.val,
    completionEmbedding_finite_mem_integers v w hw x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  commutes' r := Subtype.ext (completionEmbedding_finite_commutes v w hw r)

def integralTensorToProduct {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    TensorProduct (𝓞 K) (𝓞 L) (v.adicCompletionIntegers K) →ₐ[𝓞 K]
      ((ω : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        ω.val.adicCompletionIntegers L) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom (𝓞 K) _ (fun w =>
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) (w.val.adicCompletionIntegers L))))
    (Pi.algHom (𝓞 K) _ (fun w => completionEmbeddingIntegers v w.val w.prop))





theorem integralTensorToProduct_algebraMap_comm {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (r : v.adicCompletionIntegers K) :
    integralTensorToProduct (L := L) v ((
      letI := @Algebra.TensorProduct.rightAlgebra (𝓞 K) (𝓞 L)
          (v.adicCompletionIntegers K) _ _ _ _ _
      algebraMap (v.adicCompletionIntegers K)
        (TensorProduct (𝓞 K) (𝓞 L) (v.adicCompletionIntegers K))) r) =
    (
      letI : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
        Algebra (v.adicCompletionIntegers K) (w.val.adicCompletionIntegers L) :=
        fun w => (completionEmbeddingIntegers v w.val w.prop).toAlgebra
      @algebraMap (v.adicCompletionIntegers K)
        ((ω : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
          ω.val.adicCompletionIntegers L)
        _ _ (Pi.algebra _ _)) r := by


  funext w
  show (integralTensorToProduct (L := L) v
      (Algebra.TensorProduct.includeRight (R := 𝓞 K) r)) w =
    completionEmbeddingIntegers v w.val w.prop r
  have h1 : Algebra.TensorProduct.includeRight (R := 𝓞 K) r =
      (1 : 𝓞 L) ⊗ₜ[𝓞 K] r := Algebra.TensorProduct.includeRight_apply r
  rw [h1, integralTensorToProduct]
  simp only [Algebra.TensorProduct.productMap_apply_tmul, Pi.algHom_apply, map_one, one_mul]



end
