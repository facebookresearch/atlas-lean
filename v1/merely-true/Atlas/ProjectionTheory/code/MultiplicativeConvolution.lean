/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Complex.Basic

open Nat Finset

/-- The multiplicative (Dirichlet) convolution of two functions $f, g : \mathbb{N} \to \mathbb{C}$:
$(f *_M g)(n) = \sum_{n_1 n_2 = n} f(n_1)\, g(n_2)$. -/
noncomputable def mulConv (f g : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ Nat.divisorsAntidiagonal n, f d.1 * g d.2

namespace MultiplicativeConvolution

/-- The multiplicative convolution `mulConv` agrees pointwise with the product `f * g` of
arithmetic functions (i.e. with Dirichlet convolution defined on `ArithmeticFunction ℂ`). -/
theorem mulConv_eq_arithmeticFunction_mul (f g : ArithmeticFunction ℂ) (n : ℕ) :
    mulConv (fun n => f n) (fun n => g n) n = (f * g) n := by
  simp [mulConv, ArithmeticFunction.mul_apply]

end MultiplicativeConvolution
