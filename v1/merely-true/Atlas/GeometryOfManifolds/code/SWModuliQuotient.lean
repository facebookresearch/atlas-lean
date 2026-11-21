/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.GaugeAction
import Atlas.GeometryOfManifolds.code.SWModuliGoal62

set_option autoImplicit false

noncomputable section


/-- The canonical quotient map from Seiberg–Witten solutions to the moduli space
$\mathcal{M} = \{\text{SW solutions}\}/\mathcal{G}$ is surjective. -/
theorem SWModuliQuotient.mk_surjective
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc) :
    Function.Surjective (SWModuliQuotient.mk gd) := by
  intro q
  induction q using Quotient.ind with
  | _ sol => exact ⟨sol, rfl⟩


/-- Gauge-invariant sup-norm-squared $\|\Phi\|_\infty^2$ descends to the moduli quotient. -/
def SWModuliQuotient.supNormSq
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc)
    (q : SWModuliQuotient gd) : ℝ :=
  Quotient.lift (fun sol => sol.supNormSq)
    (by
      intro a b hab
      obtain ⟨g, hg⟩ := hab
      rw [← hg]
      exact (gd.gauge_action_preserves_supNormSq g a).symm) q

/-- The sup-norm-squared on the moduli quotient is nonnegative. -/
theorem SWModuliQuotient.supNormSq_nonneg
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc)
    (q : SWModuliQuotient gd) :
    0 ≤ SWModuliQuotient.supNormSq gd q := by
  induction q using Quotient.ind with
  | _ sol => exact sol.supNormSq_nonneg


/-- A moduli class is reducible iff its sup-norm-squared vanishes, i.e. the spinor field $\Phi$
is identically zero. -/
def SWModuliQuotient.IsReducible
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc)
    (q : SWModuliQuotient gd) : Prop :=
  SWModuliQuotient.supNormSq gd q = 0


/-- When $b_2^+ \geq 1$ and the metric/perturbation pair is generic, no SW solution descends to a
reducible class in the moduli space. -/
theorem SWModuliQuotient.no_reducibles_generic
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    [CompactSpace M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    [htop : Has4ManifoldTopology M]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc)
    [hgeneric : IsGenericPair spinc]
    (hb₂_pos : htop.Q.b₂_plus ≥ 1)
    (sol : SWSolution spinc) :
    ¬(SWModuliQuotient.IsReducible gd (SWModuliQuotient.mk gd sol)) := by
  intro hred
  have h_no_red := IsGenericPair.no_reducible_solutions hb₂_pos sol
  exact h_no_red ((sol.isReducible_iff_supNormSq_zero).mpr hred)



end
