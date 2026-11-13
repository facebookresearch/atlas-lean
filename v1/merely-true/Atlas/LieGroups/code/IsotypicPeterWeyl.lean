/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.KFinite
import Atlas.LieGroups.code.KFiniteProps
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

section IsotypicHomDef

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
variable [IsTopologicalGroup G]

def IsotypicComponentHom
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (π : ContinuousRep G V) (K : Subgroup G)
    (σ : ContinuousRep K Wσ) :
    Submodule ℂ V :=
  ⨆ (T : RepHom σ (π.restrictSubgroup K)),
    LinearMap.range T.toContinuousLinearMap.toLinearMap

def isotypicEvaluation
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (π : ContinuousRep G V) (K : Subgroup G)
    (σ : ContinuousRep K Wσ)
    (T : RepHom σ (π.restrictSubgroup K)) (u : Wσ) : V :=
  T.toContinuousLinearMap u

end IsotypicHomDef

section MatrixCoefficients

variable (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

def matrixCoefficient
    {Wρ : Type*} [AddCommGroup Wρ] [Module ℂ Wρ] [TopologicalSpace Wρ]
    (ρ : ContinuousRep K Wρ) (φ : Wρ →L[ℂ] ℂ) (v : Wρ) :
    K → ℂ :=
  fun g => φ ((ρ.toMonoidHom g) v)

def MatrixCoefficientSubspace
    {Wρ : Type*} [AddCommGroup Wρ] [Module ℂ Wρ] [TopologicalSpace Wρ]
    (ρ : ContinuousRep K Wρ) :
    Submodule ℂ (K → ℂ) :=
  Submodule.span ℂ { f : K → ℂ | ∃ (φ : Wρ →L[ℂ] ℂ) (v : Wρ), f = matrixCoefficient K ρ φ v }

end MatrixCoefficients

section IrrK

structure IrrFinDimRep (K : Type*) [Group K] [TopologicalSpace K]
    [CompactSpace K] where
  carrier : Type
  [instNACG : NormedAddCommGroup carrier]
  [instIPS : InnerProductSpace ℂ carrier]
  [instFD : FiniteDimensional ℂ carrier]
  [instCS : CompleteSpace carrier]
  rep : ContinuousRep K carrier
  irred : rep.IsIrreducible
  unitary : rep.IsUnitary
  [instNT : Nontrivial carrier]

attribute [instance] IrrFinDimRep.instNACG IrrFinDimRep.instIPS
  IrrFinDimRep.instFD IrrFinDimRep.instCS IrrFinDimRep.instNT

def IrrFinDimRep.dim {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] (ρ : IrrFinDimRep K) : ℕ :=
  Module.finrank ℂ ρ.carrier

end IrrK

section L2K

variable (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsHaarMeasure]

open MeasureTheory in
abbrev L2 := MeasureTheory.Lp ℂ 2 μ

def leftTranslationCM : C(K, C(K, K)) :=
  ContinuousMap.curry ⟨fun p : K × K => p.1⁻¹ * p.2, continuous_fst.inv.mul continuous_snd⟩

open MeasureTheory in
def leftRegularRep : ContinuousRep K (L2 K μ) where
  toMonoidHom := {
    toFun := fun g =>
      (Lp.compMeasurePreservingₗ ℂ (fun x => g⁻¹ * x)
        (measurePreserving_mul_left μ g⁻¹)).mkContinuous 1 (by
        intro f; simp only [one_mul]
        exact le_of_eq (Lp.norm_compMeasurePreserving f (measurePreserving_mul_left μ g⁻¹)))
    map_one' := by
      apply ContinuousLinearMap.ext; intro f
      simp only [LinearMap.mkContinuous_apply, Lp.compMeasurePreservingₗ_apply,
        ContinuousLinearMap.one_apply]
      ext1
      refine (Lp.coeFn_compMeasurePreserving _ _).trans ?_
      filter_upwards with x; simp
    map_mul' := fun g₁ g₂ => by
      apply ContinuousLinearMap.ext; intro f
      simp only [LinearMap.mkContinuous_apply, Lp.compMeasurePreservingₗ_apply,
        ContinuousLinearMap.mul_apply]
      change Lp.compMeasurePreserving _ _ f =
             Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f)
      rw [← Lp.compMeasurePreserving_comp_apply]
      ext1
      refine ((Lp.coeFn_compMeasurePreserving _ _).trans ?_).trans
        (Lp.coeFn_compMeasurePreserving _ _).symm
      filter_upwards with x; simp [mul_assoc]
  }
  continuous_action := by
    have : Continuous (fun (z : K × L2 K μ) =>
        Lp.compMeasurePreserving (leftTranslationCM K z.1)
          (measurePreserving_mul_left μ z.1⁻¹) z.2) := by
      haveI : MeasureTheory.Measure.Regular μ :=
        MeasureTheory.Measure.instRegularOfIsHaarMeasureOfCompactSpace μ
      exact Continuous.compMeasurePreservingLp (μ := μ) (ν := μ) continuous_snd
        ((leftTranslationCM K).continuous.comp continuous_fst)
        (fun z => measurePreserving_mul_left μ z.1⁻¹)
        (ENNReal.ofNat_ne_top)
    convert this using 1

end L2K

section PeterWeyl

variable (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsHaarMeasure]







end PeterWeyl

end ContinuousRep

end
