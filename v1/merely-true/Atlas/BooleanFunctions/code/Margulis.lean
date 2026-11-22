/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Influence

namespace BooleanFourier

open Finset BigOperators

noncomputable def vertexBoundaryMeasure {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  ((Finset.univ.filter fun x => ∃ i : Fin n, f x ≠ f (flipCoord x i)).card : ℝ) / (2 ^ n : ℝ)

noncomputable def boolVariance {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  let mean := ((Finset.univ.filter (fun x => f x = true)).card : ℝ) / (2 ^ n : ℝ)
  mean * (1 - mean)



end BooleanFourier
