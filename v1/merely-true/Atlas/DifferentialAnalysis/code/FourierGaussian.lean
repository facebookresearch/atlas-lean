/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

open Real MeasureTheory Complex
open scoped RealInnerProductSpace

namespace FourierAnalysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform as defined in Melrose's book: `(Ff)(w) = ∫ e^{-i⟨v,w⟩} f(v) dv`,
on a real finite-dimensional inner product space `V`. -/
def bookFourierTransform (f : V → ℂ) (w : V) : ℂ :=
  ∫ v, cexp (-(I : ℂ) * ↑(⟪v, w⟫)) * f v

/-- Lemma 8.12 (Gaussian Fourier transform): the Fourier transform of the standard
Gaussian `v ↦ exp(-‖v‖²/2)` on a finite-dimensional real inner product space `V`
equals `(2π)^{dim V / 2} · exp(-‖w‖²/2)`. -/
theorem fourier_transform_gaussian (w : V) :
    bookFourierTransform (fun v => cexp (-(1 / 2 : ℂ) * ‖v‖ ^ 2)) w =
    ↑((2 * π) ^ ((Module.finrank ℝ V : ℝ) / 2)) * cexp (-(1 / 2 : ℂ) * ‖w‖ ^ 2) := by

  show ∫ v, cexp (-(I : ℂ) * ↑(⟪v, w⟫)) * cexp (-(1 / 2 : ℂ) * ‖v‖ ^ 2) =
    ↑((2 * π) ^ ((Module.finrank ℝ V : ℝ) / 2)) * cexp (-(1 / 2 : ℂ) * ‖w‖ ^ 2)


  have hcomb : ∀ v : V, cexp (-(I : ℂ) * ↑(⟪v, w⟫)) * cexp (-(1 / 2 : ℂ) * ‖v‖ ^ 2) =
      cexp (-(1 / 2 : ℂ) * ‖v‖ ^ 2 + (-I : ℂ) * (⟪w, v⟫ : ℝ)) := fun v => by
    rw [← Complex.exp_add]; congr 1; rw [real_inner_comm v w]; push_cast; ring
  simp_rw [hcomb]

  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (show (0 : ℝ) < ((1 / 2 : ℂ)).re by norm_num) (-I : ℂ) w]

  have h_exp : (-I : ℂ) ^ 2 * ‖w‖ ^ 2 / (4 * (1 / 2 : ℂ)) = -(1 / 2 : ℂ) * ‖w‖ ^ 2 := by
    rw [neg_sq, I_sq]; ring
  rw [h_exp]

  have h_coeff : (π : ℂ) / (1 / 2 : ℂ) = ↑(2 * π) := by push_cast; ring
  rw [h_coeff]
  congr 1
  rw [show (Module.finrank ℝ V / 2 : ℂ) = ↑((Module.finrank ℝ V : ℝ) / 2) from by
    push_cast; ring]
  exact (ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * π) _).symm

end FourierAnalysis

end
