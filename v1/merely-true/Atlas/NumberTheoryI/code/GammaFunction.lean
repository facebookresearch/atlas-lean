/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open scoped FourierTransform
open Complex Real

theorem gaussian_fourier_self :
    (𝓕 fun (x : ℝ) ↦ cexp (-(π : ℂ) * (x : ℂ) ^ 2)) =
    fun (y : ℝ) ↦ cexp (-(π : ℂ) * (y : ℂ) ^ 2) := by
  have := fourier_gaussian_pi (b := 1) (by simp : (0 : ℝ) < (1 : ℂ).re)
  simp only [mul_one, div_one, one_cpow, one_div, one_mul] at this
  exact this
