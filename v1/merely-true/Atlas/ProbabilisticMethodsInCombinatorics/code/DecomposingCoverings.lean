/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Atlas.ProbabilisticMethodsInCombinatorics.code.DecomposingCoveringsAxiom

open Set Metric

namespace DecomposingCoverings

noncomputable section

variable {ι : Type*}

/-- A family of unit balls with centres `center` is a covering of $\mathbb{R}^3$ when
every point is covered by at least one ball. -/
def IsCovering (center : ι → E3) : Prop :=
  ∀ x : E3, (coveringSet center x).Nonempty

/-- A family of unit balls is decomposable if its index set can be partitioned into two
classes $A$ and $A^c$ such that both subfamilies still cover $\mathbb{R}^3$. -/
def IsDecomposable (center : ι → E3) : Prop :=
  ∃ (A : Set ι), IsCovering (fun i : A => center i.val) ∧
                  IsCovering (fun i : ↥Aᶜ => center i.val)


end

end DecomposingCoverings
