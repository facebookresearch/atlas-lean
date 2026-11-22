/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SchurLemma
import Atlas.LieGroups.code.IsotypicPeterWeyl
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace

noncomputable section

open MeasureTheory ContinuousRep
open scoped ComplexConjugate

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsHaarMeasure]



def matrixCoefficientOfEnd
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] [CompleteSpace W]
    (ρ : ContinuousRep K W) (A : W →L[ℂ] W) : K → ℂ :=
  fun g => (LinearMap.trace ℂ W) (A.comp (ρ.toMonoidHom g)).toLinearMap

lemma trace_eq_sum_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : OrthonormalBasis ι ℂ E) (L : E →ₗ[ℂ] E) :
    (LinearMap.trace ℂ E) L = ∑ i, @inner ℂ _ _ (b i) (L (b i)) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  congr 1; ext i
  rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  simp [OrthonormalBasis.coe_toBasis]


end
