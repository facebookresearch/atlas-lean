/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Finprod

namespace BooleanFourier

abbrev BoolFn (n : ℕ) := (Fin n → Bool) → ℝ

open Finset in
noncomputable def lpNorm (p : ℝ) (f : BoolFn n) : ℝ :=
  ((1 / (2 ^ n : ℝ)) * ∑ x : Fin n → Bool, |f x| ^ p) ^ (1 / p)

end BooleanFourier
