/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.Parametrix
import Atlas.DifferentialAnalysis.code.CauchyKernelIntegrability

open scoped SchwartzMap
open MvPolynomial MeasureTheory Complex Real Set Metric

noncomputable section

namespace DifferentialOperators

/-- Identification of the Euclidean norm on `ℝ²` with the complex modulus on `ℂ` under the
canonical map `(x, y) ↦ x + iy`. -/
lemma norm_complex_eq_euclidean (v : EuclideanSpace ℝ (Fin 2)) :
    ‖(↑(v 0) + I * ↑(v 1) : ℂ)‖ = ‖v‖ := by
  rw [mul_comm I (↑(v 1) : ℂ), Complex.norm_add_mul_I, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two, sq_abs]

/-- Pointwise norm of the Cauchy–Riemann kernel `1 / (2π · z)`:
`‖K(v)‖ = (2π)⁻¹ · ‖v‖⁻¹` for `v ≠ 0`. -/
lemma norm_cauchyRiemannKernel_eq (v : EuclideanSpace ℝ (Fin 2)) :
    ‖cauchyRiemannKernel v‖ = (2 * Real.pi)⁻¹ * ‖v‖⁻¹ := by
  show ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((↑(v 0) + I * ↑(v 1) : ℂ))⁻¹‖ = _
  rw [norm_mul, norm_inv, norm_inv, Complex.norm_real, norm_complex_eq_euclidean]
  simp only [Real.norm_eq_abs, abs_of_pos (by positivity : (2 : ℝ) * Real.pi > 0)]

/-- Uniform bound on the Cauchy–Riemann kernel away from the origin: for `‖v‖ ≥ 1`,
`‖K(v)‖ ≤ (2π)⁻¹`. -/
lemma norm_cauchyRiemannKernel_le_of_one_le_norm (v : EuclideanSpace ℝ (Fin 2))
    (hv : 1 ≤ ‖v‖) :
    ‖cauchyRiemannKernel v‖ ≤ (2 * Real.pi)⁻¹ := by
  rw [norm_cauchyRiemannKernel_eq]
  calc (2 * Real.pi)⁻¹ * ‖v‖⁻¹ ≤ (2 * Real.pi)⁻¹ * 1 := by
        apply mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hv)
        positivity
      _ = (2 * Real.pi)⁻¹ := mul_one _

/-- Integrability of `φ · K` where `φ` is Schwartz and `K` is the Cauchy–Riemann kernel:
the product is integrable on `ℝ²`, by splitting into the unit ball (where `K` is locally
integrable and `φ` is bounded) and its complement (where `K` is bounded and `φ` is integrable). -/
theorem integrable_schwartz_mul_cauchyRiemannKernel
    (φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) :
    Integrable (fun v => φ v * cauchyRiemannKernel v) := by

  rw [← integrableOn_univ]
  rw [← union_compl_self (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)]
  exact IntegrableOn.union

    (IntegrableOn.continuousOn_mul_of_subset
      φ.continuous.continuousOn
      (cauchyRiemannKernel_locallyIntegrable.integrableOn_isCompact
        (isCompact_closedBall 0 1))
      (isCompact_closedBall 0 1)
      measurableSet_closedBall
      (Subset.refl _))

    (Integrable.mul_bdd
      φ.integrable.integrableOn
      (cauchyRiemannKernel_locallyIntegrable.aestronglyMeasurable.restrict)
      (ae_restrict_of_forall_mem measurableSet_closedBall.compl
        (fun v hv => by
          apply norm_cauchyRiemannKernel_le_of_one_le_norm
          rw [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hv
          linarith)))

/-- Schwartz-seminorm bound on the integral `∫ φ · K`: there exists a finite set of indices
and a constant such that `‖∫ φ · K‖` is controlled by the corresponding Schwartz seminorm
of `φ`, expressing the continuity of the linear functional `φ ↦ ∫ φ · K` on Schwartz space. -/
lemma norm_integral_schwartz_cauchyRiemannKernel_le :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ),
        ‖∫ v, φ v * cauchyRiemannKernel v‖ ≤
          C * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2)) ℂ)) φ := by
  obtain ⟨s, C, hC, hbound⟩ := cauchyRiemannKernel_integral_bound
  exact ⟨s, C, hC, fun φ => by
    have : (fun v => φ v * cauchyRiemannKernel v) =
        (fun v => φ v • cauchyRiemannKernel v) :=
      funext (fun v => (smul_eq_mul (φ v) (cauchyRiemannKernel v)).symm)
    rw [this]
    exact hbound φ⟩

/-- The tempered distribution `E` defined by integration against the Cauchy–Riemann kernel
`K(z) = 1 / (2π z)`. This is the candidate fundamental solution of `∂̄` on `ℝ²`. -/
def dbarFundSolDist :
    𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace
    (fun φ => ∫ v, φ v * cauchyRiemannKernel v)
    (fun f g => by
      simp only [SchwartzMap.add_apply, add_mul]
      exact integral_add (integrable_schwartz_mul_cauchyRiemannKernel f)
        (integrable_schwartz_mul_cauchyRiemannKernel g))
    (fun c f => by
      simp only [SchwartzMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
      exact integral_smul c _)
    norm_integral_schwartz_cauchyRiemannKernel_le

/-- Evaluation formula for the candidate fundamental solution distribution `E`: pairing with
a Schwartz function `φ` is `∫ φ(v) · K(v) dv`. -/
@[simp]
theorem dbarFundSolDist_apply (φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) :
    dbarFundSolDist φ = ∫ v, φ v * cauchyRiemannKernel v := by
  rfl

/-- The `mkCLM`-packaged distribution `dbarFundSolDist` agrees with the underlying
`cauchyRiemannDistribution` already defined elsewhere. -/
lemma dbarFundSolDist_eq_cauchyRiemannDistribution :
    dbarFundSolDist = cauchyRiemannDistribution := by
  ext φ
  simp only [dbarFundSolDist_apply, cauchyRiemannDistribution_apply]
  simp only [smul_eq_mul]



end DifferentialOperators

end
