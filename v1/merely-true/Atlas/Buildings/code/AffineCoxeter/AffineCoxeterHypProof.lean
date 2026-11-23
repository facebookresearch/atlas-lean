/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusCorollary
import Atlas.Buildings.code.AffineCoxeter.FiniteProperParabolicsInstance
import Atlas.Buildings.code.AffineCoxeter.AffineCriterion

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone PerronFrobeniusProof

namespace AffineCoxeterHypProof

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- A Coxeter matrix is **crystallographic** if $2 \cos(\pi/m_{st}) \in \mathbb Z$ for all $s,t \in B$,
i.e. all entries of the doubled Gram matrix are integers. This is the condition for the associated
root system to admit an integral coroot lattice. -/
def IsCrystallographic (M : CoxeterMatrix B) : Prop :=
  ∀ s t : B, ∃ n : ℤ, 2 * CoxeterGroup.formVal M s t = ↑n




end AffineCoxeterHypProof
