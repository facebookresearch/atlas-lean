/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.FourManifoldsSW


section SWSolutionNonVacuous

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
variable {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
variable {spinc : SpinCStructure M Ω1 Ω2}

/-- **Bochner-type constraint from the Seiberg-Witten equations.** For any solution
$(A, \psi)$, combining the Weitzenbock formula with $\|\nabla\psi\|^2 \ge 0$ yields
$$\tfrac{s}{4}\,\|\psi\|^2_{\sup} + \tfrac{1}{4}\,\|\psi\|^4_{\sup} \le 0,$$
where $s$ is the (sampled) scalar curvature value. -/
theorem sw_solution_bochner_constrains_fields
    (sol : SWSolution spinc) :
    (sol.scalarCurvatureVal / 4) * sol.supNormSq +
      (1/4) * sol.supNormSq ^ 2 ≤ 0 := by
  have h1 := sol.laplacianTerm_nonneg
  have h2 := sol.covDerivNormSq_nonneg
  have h3 := sol.bochner_eq
  linarith

/-- **Positive scalar curvature forces $\psi \equiv 0$.** If $s > 0$, then the Bochner
constraint forces $\|\psi\|^2_{\sup} = 0$, so every SW solution is reducible. This is the
analytic core of the vanishing of SW invariants on PSC manifolds. -/
theorem sw_solution_positive_scalar_forces_reducible
    (sol : SWSolution spinc)
    (hs : sol.scalarCurvatureVal > 0) :
    sol.supNormSq = 0 := by
  have hbound := sw_solution_bochner_constrains_fields sol
  have hnn := sol.supNormSq_nonneg
  by_contra h
  push Not at h
  have hpos : sol.supNormSq > 0 := lt_of_le_of_ne hnn (Ne.symm h)
  have h1 : (sol.scalarCurvatureVal / 4) * sol.supNormSq > 0 := by positivity
  have h2 : (1/4 : ℝ) * sol.supNormSq ^ 2 ≥ 0 := by positivity
  linarith

/-- **Solutions on PSC manifolds are reducible.** Combining the previous lemma with the
reducibility characterization $\|\psi\|^2_{\sup} = 0 \iff \text{reducible}$: any SW solution
on a manifold of positive scalar curvature is reducible. -/
theorem sw_solution_positive_scalar_is_reducible
    (sol : SWSolution spinc)
    (hs : sol.scalarCurvatureVal > 0) :
    sol.isReducible := by
  exact (sol.isReducible_iff_supNormSq_zero).mpr
    (sw_solution_positive_scalar_forces_reducible sol hs)

end SWSolutionNonVacuous


section HasGaugeActionNonVacuous

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
variable {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
variable {spinc : SpinCStructure M Ω1 Ω2}

end HasGaugeActionNonVacuous


section CrossStructureConsistency

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
variable {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
variable {spinc : SpinCStructure M Ω1 Ω2}

end CrossStructureConsistency
