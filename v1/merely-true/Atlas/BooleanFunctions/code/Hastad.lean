/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.PCP
import Mathlib.Data.Real.Basic

namespace Hastad

open PCP

def HasMaxSatFractionAtMost_Real (φ : ThreeSATFormula) (s : ℝ) : Prop :=
  ∀ σ : Assignment φ.numVars,
    (numSatisfied φ σ : ℝ) ≤ s * (φ.clauses.length : ℝ)


end Hastad


