/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.YoungEigenvalues
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

noncomputable section

open scoped Classical
open Finset BigOperators

namespace PartitionCycles

def PartitionCovers {n : ℕ} (μ : Nat.Partition n) (ν : Nat.Partition (n + 1)) : Prop :=
  ∃ k ∈ ν.parts, μ.parts = (ν.parts.erase k) + (if k = 1 then 0 else {k - 1})

def IsValidCycle (n m : ℕ)
    (ν : Fin (m + 1) → Nat.Partition (n + 1))
    (μ : Fin m → Nat.Partition n) : Prop :=
  ν 0 = ν (Fin.last m) ∧
  ∀ i : Fin m,
    PartitionCovers (μ i) (ν i.castSucc) ∧
    PartitionCovers (μ i) (ν i.succ)

def partitionCycleCount (n m : ℕ) : ℕ :=
  Fintype.card
    { walk : (Fin (m + 1) → Nat.Partition (n + 1)) × (Fin m → Nat.Partition n) //
      IsValidCycle n m walk.1 walk.2 }

def eigenMult (j s : ℕ) : ℤ :=
  (YoungEigenvalues.p (j - s) : ℤ) -
    if s + 1 ≤ j then (YoungEigenvalues.p (j - (s + 1)) : ℤ) else 0

def eigenvaluePowerSum (j m : ℕ) : ℤ :=
  eigenMult j 0 * (0 : ℤ) ^ (2 * m) +
  ∑ s ∈ Icc 1 j, 2 * eigenMult j s * (s : ℤ) ^ m

def closedWalkTraceSum (n m : ℕ) : ℤ := eigenvaluePowerSum (n + 1) m



end PartitionCycles
