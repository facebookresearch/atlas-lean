/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.Uniformization
import Mathlib.NumberTheory.ArithmeticFunction.Misc

noncomputable section

open Complex ArithmeticFunction

namespace ComplexLattice

variable (τ : UpperHalfPlane)

/-- The *nome* `q = e^{2πiτ}` associated to `τ ∈ ℍ`. -/
def nome (τ : UpperHalfPlane) : ℂ :=
  Complex.exp (2 * ↑Real.pi * I * (τ : ℂ))




end ComplexLattice
