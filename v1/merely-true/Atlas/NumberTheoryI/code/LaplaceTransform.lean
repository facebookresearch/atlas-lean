/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Complex Set

noncomputable def laplaceTransform (h : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), exp (-s * ↑t) * ↑(h t)
