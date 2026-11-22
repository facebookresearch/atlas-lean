/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Fourier.FourierTransform

open MeasureTheory Function Set Metric
open scoped Convolution

noncomputable section

namespace BandlimitedBound

variable {d : ℕ}

/-- The Fourier transform `f̂` on `ℝ^d` (Euclidean space), defined via
`VectorFourier.fourierIntegral` using the standard character and inner product. -/
def fourierTransformRd (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) :
    EuclideanSpace ℝ (Fin d) → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume
    (innerₗ (EuclideanSpace ℝ (Fin d))) f

/-- `g` has Fourier support contained in `S`, i.e. `supp ĝ ⊆ S`. -/
def HasFourierSupportIn (g : EuclideanSpace ℝ (Fin d) → ℂ)
    (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Function.support (fourierTransformRd d g) ⊆ S

/-- A non-negative integrable majorant `ψ` at scale `r > 0`, used as an approximate
identity in the bandlimited bound. -/
structure IsApproxIdentityMajorant (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (r : ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ψ x
  integrable : Integrable ψ (volume : Measure (EuclideanSpace ℝ (Fin d)))
  pos_scale : 0 < r



end BandlimitedBound
