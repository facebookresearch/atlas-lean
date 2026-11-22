/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Group.Conj

open Equiv Equiv.Perm

namespace SymmetricGroups

variable {α : Type*} [Fintype α] [DecidableEq α]

def cycleType (σ : Perm α) : Multiset ℕ := σ.cycleType

theorem conjugate_iff_same_cycleType {n : ℕ} {σ τ : Perm (Fin n)} :
    IsConj σ τ ↔ σ.cycleType = τ.cycleType :=
  Equiv.Perm.isConj_iff_cycleType_eq
