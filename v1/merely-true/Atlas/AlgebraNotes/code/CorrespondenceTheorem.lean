/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

namespace CorrespondenceTheorem

variable {G G' : Type*} [Group G] [Group G']

def correspondenceOrderIso (f : G →* G') (hf : Function.Surjective f) :
    { H : Subgroup G // f.ker ≤ H } ≃o Subgroup G' where
  toFun H := Subgroup.map f H
  invFun H' := ⟨Subgroup.comap f H', Subgroup.ker_le_comap f H'⟩
  left_inv := fun ⟨H, hH⟩ => Subtype.ext (Subgroup.comap_map_eq_self hH)
  right_inv H' := Subgroup.map_comap_eq_self_of_surjective hf H'
  map_rel_iff' := by
    intro ⟨H, hH⟩ ⟨K, hK⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk]
    constructor
    · intro h
      calc H = Subgroup.comap f (Subgroup.map f H) := (Subgroup.comap_map_eq_self hH).symm
        _ ≤ Subgroup.comap f (Subgroup.map f K) := Subgroup.comap_mono h
        _ = K := Subgroup.comap_map_eq_self hK
    · exact Subgroup.map_mono
