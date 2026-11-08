/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset BigOperators

namespace DoubleCountingSimple

/-- Simple projection map on `F × F` in direction `θ`: `projMap θ (x₁, x₂) = x₁ + θ · x₂`. -/
def projMap {F : Type*} [Mul F] [Add F] (θ : F) (x : F × F) : F := x.1 + θ * x.2

end DoubleCountingSimple
