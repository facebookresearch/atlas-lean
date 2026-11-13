/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Ideles
import Atlas.NumberTheoryI.code.AdicCompletionAlgebra
import Atlas.NumberTheoryI.code.KroneckerWeber

noncomputable section

open NumberField IsDedekindDomain Ideles

def InfinitePlace.localNormHom {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : InfinitePlace L) (v : InfinitePlace K) :
    w.Completion →* v.Completion := by
  classical
  exact
    if hv : v.IsReal then
      if hw : w.IsReal then

        (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom.comp
          (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMonoidHom
      else

        (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom.comp
          (Complex.normSq.toMonoidHom.comp
            (InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (InfinitePlace.not_isReal_iff_isComplex.mp hw)).toMonoidHom)
    else
      if hw : w.IsReal then

        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).symm.toMonoidHom.comp
          (Complex.ofRealHom.toMonoidHom.comp
            (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMonoidHom)
      else

        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).symm.toMonoidHom.comp
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).toMonoidHom

open Classical in
def infiniteNormComponent (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : InfinitePlace K) :
    InfiniteAdeleRing L →* v.Completion where
  toFun b := ∏ w : InfinitePlace L,
    if w.comap (algebraMap K L) = v then
      InfinitePlace.localNormHom w v (b w)
    else 1
  map_one' := by
    apply Finset.prod_eq_one
    intro w _
    split_ifs with h
    · exact (InfinitePlace.localNormHom w v).map_one
    · rfl
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    congr 1
    ext w
    split_ifs with h
    · exact (InfinitePlace.localNormHom w v).map_mul _ _
    · exact (mul_one 1).symm

def infiniteAdeleNormHom (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    InfiniteAdeleRing L →* InfiniteAdeleRing K :=
  Pi.monoidHom (fun v => infiniteNormComponent K L v)


lemma extensionEmbedding_algebraMap {K : Type*} [Field K] [NumberField K]
    (v : InfinitePlace K) (y : K) :
    InfinitePlace.Completion.extensionEmbedding v (algebraMap K v.Completion y) =
      v.embedding y := by
  rw [show algebraMap K v.Completion y =
    ((WithAbs.equiv v.1).symm y : v.Completion) from rfl,
    InfinitePlace.Completion.extensionEmbedding_coe, RingEquiv.apply_symm_apply]



@[reducible]
def HeightOneSpectrum.adicCompletionAlgebra {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K))
    (hw : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal) :
    Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  instAlgebraAdicCompletionOfLiesOver K v w hw

def HeightOneSpectrum.localNormHom {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K))
    (hw : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal) :
    (w.adicCompletion L →* v.adicCompletion K) :=
  letI := HeightOneSpectrum.adicCompletionAlgebra w v hw
  Algebra.norm (v.adicCompletion K)


theorem HeightOneSpectrum.finite_placesAbove {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Set.Finite ({w : HeightOneSpectrum (𝓞 L) | w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal}) := by
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
    NumberField.RingOfIntegers.algebraMap.injective K L
  have hv_ne : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ 0 := by
    intro h
    apply v.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have hxm : algebraMap (𝓞 K) (𝓞 L) x ∈ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal :=
      Ideal.mem_map_of_mem _ hx
    rw [h] at hxm
    change algebraMap (𝓞 K) (𝓞 L) x ∈ (⊥ : Ideal (𝓞 L)) at hxm
    rw [Ideal.mem_bot] at hxm
    have : x = 0 := hinj (by rw [hxm, map_zero])
    exact this ▸ Ideal.zero_mem _
  apply Set.Finite.subset (Ideal.finite_factors hv_ne)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  exact Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr (hw ▸ le_refl _))

def HeightOneSpectrum.placesAbove {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K)) : Finset (HeightOneSpectrum (𝓞 L)) :=
  (HeightOneSpectrum.finite_placesAbove v).toFinset

lemma HeightOneSpectrum.liesOver_of_mem_placesAbove {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ HeightOneSpectrum.placesAbove v (L := L)) :
    v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal := by
  have hmem := (HeightOneSpectrum.finite_placesAbove v).mem_toFinset.mp hw
  simp only [Set.mem_setOf_eq] at hmem
  exact hmem ▸ le_refl _

def finiteNormComponent (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    FiniteAdeleRing (𝓞 L) L →* v.adicCompletion K where
  toFun b := (HeightOneSpectrum.placesAbove v (L := L)).attach.prod fun w =>
    HeightOneSpectrum.localNormHom w.1 v
      (HeightOneSpectrum.liesOver_of_mem_placesAbove w.2) (b w.1)
  map_one' := by
    apply Finset.prod_eq_one
    intro w _
    exact (HeightOneSpectrum.localNormHom w.1 v
      (HeightOneSpectrum.liesOver_of_mem_placesAbove w.2)).map_one
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    congr 1
    ext w
    exact (HeightOneSpectrum.localNormHom w.1 v
      (HeightOneSpectrum.liesOver_of_mem_placesAbove w.2)).map_mul _ _











end
