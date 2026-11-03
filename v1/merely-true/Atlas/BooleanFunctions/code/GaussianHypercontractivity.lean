/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.RingTheory.Polynomial.Hermite.Basic

noncomputable section

open MeasureTheory Real Finset

namespace GaussianHypercontractivity

noncomputable def stdGaussianMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)

noncomputable def gaussianLpNorm (n : ℕ) (p : ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  (∫ x : Fin n → ℝ, |f x| ^ p ∂(stdGaussianMeasure n)) ^ (1 / p)

noncomputable def hermiteEval (k : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.map (Int.castRingHom ℝ) (Polynomial.hermite k)).eval x

noncomputable def multiHermiteEval (n : ℕ) (α : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, hermiteEval (α i) (x i)

def HasGaussianDegreeAtMost (n d : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ α : Fin n → ℕ, ∑ i : Fin n, α i > d →
    ∫ x : Fin n → ℝ, f x * (multiHermiteEval n α x) ∂(stdGaussianMeasure n) = 0



end GaussianHypercontractivity

end
