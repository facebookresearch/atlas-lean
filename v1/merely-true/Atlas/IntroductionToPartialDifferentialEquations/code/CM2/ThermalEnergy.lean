/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
open MeasureTheory Filter

set_option maxHeartbeats 800000

noncomputable section

namespace HeatEquation

/-- The total thermal energy at time $t$ associated to $u(t, x)$, defined by
$\mathcal{T}(t) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} u(t, x) \, d^n x$.
(Definition 2.0.2.) -/
def totalThermalEnergy (n : ℕ) (u : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, u t x


/-- Under the decay assumption $\lim_{|x| \to \infty} |x|^{n-1} |\nabla_x u(t, x)| = 0$
together with integrability of the Laplacian and the divergence-theorem bound, the global
integral of the Laplacian over $\mathbb{R}^n$ vanishes:
$\int_{\mathbb{R}^n} \Delta u(t, x) \, d^n x = 0$. -/
theorem integral_laplacian_eq_zero
    {n : ℕ}
    (laplacian_u : ℝ → (Fin n → ℝ) → ℝ)
    (grad_u_norm : ℝ → (Fin n → ℝ) → ℝ)


    (hdecay : ∀ t, Tendsto
      (fun (R : ℝ) => sSup ((fun x => R ^ ((n : ℝ) - 1) * |grad_u_norm t x|) ''
        (Metric.sphere (0 : Fin n → ℝ) R)))
      atTop (nhds 0))
    (hlapl_int : ∀ t, Integrable (laplacian_u t))


    (hdiv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t R, 0 < R →
      |∫ x in Metric.ball (0 : Fin n → ℝ) R, laplacian_u t x| ≤
      C * sSup ((fun x => R ^ ((n : ℝ) - 1) * |grad_u_norm t x|) ''
        Metric.sphere (0 : Fin n → ℝ) R))
    (t : ℝ) :
    ∫ x : Fin n → ℝ, laplacian_u t x = 0 := by
  obtain ⟨C, hC_nn, hbound⟩ := hdiv_bound


  have hcover : AECover (volume : Measure (Fin n → ℝ)) atTop
      (fun R : ℝ => Metric.ball (0 : Fin n → ℝ) R) :=
    MeasureTheory.aecover_ball tendsto_id


  have htend : Tendsto (fun R => ∫ x in Metric.ball (0 : Fin n → ℝ) R, laplacian_u t x)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply squeeze_zero'
    · filter_upwards with R; exact abs_nonneg _
    · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with R hR; exact hbound t R hR
    · rw [show (0 : ℝ) = C * 0 from by ring]; exact (hdecay t).const_mul C

  exact hcover.integral_eq_of_tendsto 0 (hlapl_int t) htend



end HeatEquation
