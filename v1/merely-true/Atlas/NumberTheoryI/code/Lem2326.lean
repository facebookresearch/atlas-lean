/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.GroupCohomology
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

noncomputable section

universe u

namespace GroupCohomology

open CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

theorem homology_induced_vanishing
    [DecidableEq G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) (n : ℕ) :
    Limits.IsZero
      (groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) := by
  haveI : Subsingleton ↥(⊥ : Subgroup G) := Unique.instSubsingleton
  exact (isZero_groupHomology_succ_of_subsingleton A n).of_iso
    (groupHomology.indIso (⊥ : Subgroup G) A (n + 1))

def homology_induced_H0_iso
    [DecidableEq G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupHomology A 0 :=
  groupHomology.indIso (⊥ : Subgroup G) A 0

end GroupCohomology
