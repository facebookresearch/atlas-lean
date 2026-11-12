/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.MeasurableSpace.Basic

open MeasureTheory

/-- **Discrete-time filtration.** An increasing sequence of sub-σ-algebras
`(ℱ_n)_{n ∈ ℕ}` of `m`. Abbreviation for `Filtration ℕ m`. -/
abbrev DiscreteFiltration (Ω : Type*) (m : MeasurableSpace Ω) :=
  Filtration ℕ m
