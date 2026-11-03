/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Stopping

open scoped ENNReal NNReal MeasureTheory

open MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **Continuous-time stopping time.** A random variable `S : Ω → [0, ∞]` is a
stopping time relative to a continuous-time filtration `f` (indexed by `ℝ≥0`) when
the event `{S > t}` lies in `f t` for every `t ≥ 0`. This is the continuous-time
analogue used for Brownian motion and related processes. -/
abbrev IsStoppingTimeContinuous (f : Filtration ℝ≥0 m) (S : Ω → ℝ≥0∞) : Prop :=
  IsStoppingTime f S
