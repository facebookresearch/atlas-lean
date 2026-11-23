/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped Manifold

/-- The type of smooth `k`-forms on a manifold `M`: pointwise alternating multilinear maps
`(T_xM)^k → ℝ` indexed by `x : M`. -/
def MfdDiffForm (k : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :=
  ∀ x : M, (TangentSpace I x) [⋀^(Fin k)]→ₗ[ℝ] ℝ

namespace MfdDiffForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ}

/-- Pointwise addition makes `MfdDiffForm k I M` into an additive commutative group. -/
noncomputable instance instAddCommGroup : AddCommGroup (MfdDiffForm k I M) :=
  Pi.addCommGroup

/-- Pointwise scalar multiplication makes `MfdDiffForm k I M` into a real vector space. -/
noncomputable instance instModule : Module ℝ (MfdDiffForm k I M) :=
  Pi.module _ _ _

/-- Evaluation of a `k`-form `ω` at a point `x : M`, yielding the alternating map `ω_x` on `T_xM`. -/
def evalAt (ω : MfdDiffForm k I M) (x : M) : (TangentSpace I x) [⋀^(Fin k)]→ₗ[ℝ] ℝ :=
  ω x

/-- Pointwise extensionality: two `k`-forms are equal if they agree at every point. -/
theorem ext {ω η : MfdDiffForm k I M} (h : ∀ x, ω x = η x) : ω = η :=
  funext h







/-- Pullback of a differential form along a map `f : M → N`: $(f^*\omega)_x = \omega_{f(x)} \circ df_x$. -/
noncomputable def pullbackForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {k : ℕ} (f : M → N) (ω : MfdDiffForm k J N) : MfdDiffForm k I M :=
  fun x => (ω (f x)).compLinearMap ((mfderiv I J f x).toLinearMap)

/-- Pullback by the identity map is the identity: $\mathrm{id}^* \omega = \omega$. -/
theorem pullbackForm_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    {k : ℕ} (ω : MfdDiffForm k I M) :
    pullbackForm (I := I) (J := I) id ω = ω := by
  funext x
  simp only [pullbackForm, id, mfderiv_id]
  exact AlternatingMap.compLinearMap_id (ω x)






end MfdDiffForm
