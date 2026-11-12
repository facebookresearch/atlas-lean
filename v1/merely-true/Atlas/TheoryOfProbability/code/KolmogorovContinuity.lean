/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

/-- The set of **dyadic rationals** in ℝ, i.e., real numbers of the form `k / 2 ^ n` for some
integer `k` and natural number `n`. This is the dense countable set on which the Kolmogorov
continuity theorem first establishes Hölder continuity. -/
def dyadicRationals : Set ℝ :=
  { x : ℝ | ∃ (k : ℤ) (n : ℕ), x = k / (2 : ℝ) ^ n }

