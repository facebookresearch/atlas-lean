/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Atlas.DifferentialAnalysis.code.HormanderFundamental
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section

open scoped SchwartzMap
open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}


/-- For a continuous linear functional on `E n = EuclideanSpace ℝ (Fin n)`, the operator norm
is bounded by the sum of the absolute values on the standard basis vectors. -/
lemma clm_norm_le_sum_basis (L : E n →L[ℝ] ℂ) :
    ‖L‖ ≤ ∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have hv_decomp : v = ∑ i : Fin n, (v i : ℝ) • EuclideanSpace.single i (1 : ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv_decomp]
  calc ‖L (∑ i, (v i : ℝ) • EuclideanSpace.single i 1)‖
      = ‖∑ i, (v i : ℝ) • L (EuclideanSpace.single i 1)‖ := by
        simp [map_sum, map_smul]
    _ ≤ ∑ i, ‖(v i : ℝ) • L (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ * ‖L (EuclideanSpace.single i 1)‖ := by simp
    _ ≤ ∑ i, ‖v‖ * ‖L (EuclideanSpace.single i 1)‖ := by
        gcongr with i _; exact PiLp.norm_apply_le v i
    _ = (∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖) * ‖v‖ := by
        simp_rw [mul_comm ‖v‖ _]; rw [← Finset.sum_mul]


/-- The norm of the iterated derivative of `fderiv f` at `x` is bounded by the sum over the
standard basis directions `eᵢ` of the iterated-derivative norms of the directional derivative
`y ↦ ⟨df y, eᵢ⟩`. -/
theorem norm_iteratedFDeriv_fderiv_le_sum
    {m : ℕ} (f : E n → ℂ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (x : E n) :
    ‖iteratedFDeriv ℝ m (fderiv ℝ f) x‖ ≤
      ∑ i : Fin n, ‖iteratedFDeriv ℝ m
        (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x‖ := by
  have hfderiv_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (by simp)
  have hcomp : ∀ i : Fin n,
      (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) =
      (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))) ∘ (fderiv ℝ f) := by
    intro i; ext y; simp [ContinuousLinearMap.apply_apply]
  have hcomp2 : ∀ i : Fin n,
    iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x =
    (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).compContinuousMultilinearMap
      (iteratedFDeriv ℝ m (fderiv ℝ f) x) := by
    intro i
    rw [hcomp i]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left _
      hfderiv_smooth.contDiffAt (WithTop.coe_le_coe.mpr le_top)
  set M := iteratedFDeriv ℝ m (fderiv ℝ f) x
  apply (ContinuousMultilinearMap.opNorm_le_iff (by positivity)).mpr
  intro v
  calc ‖M v‖
      ≤ ∑ i : Fin n, ‖M v (EuclideanSpace.single i 1)‖ :=
        clm_norm_le_sum_basis (M v)
    _ = ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x v‖ := by
        congr 1; ext i; rw [hcomp2]; rfl
    _ ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x‖ * ∏ j, ‖v j‖ := by
        gcongr with i _
        exact (iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x).le_opNorm v
    _ = (∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x‖) * ∏ j, ‖v j‖ := by
        rw [Finset.sum_mul]









end ConeSupport

end
