/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory

noncomputable section

namespace HeatFundamental

/-- The convolution of two functions $f, g : \mathbb{R}^n \to \mathbb{R}$
(Definition 1.1.1): $(f * g)(x) = \int_{\mathbb{R}^n} f(y)\, g(x - y)\, d^n y$. -/
def convolution {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ, f y * g (x - y)

end HeatFundamental

end
