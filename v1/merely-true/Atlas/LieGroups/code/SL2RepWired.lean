/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SL2Classification

inductive KTypeBoundedness' where
  | boundedBoth
  | unboundedBoth
  | boundedBelow
  | boundedAbove
  deriving DecidableEq, Repr

namespace SL2GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable {K : Type*} [Group K]
variable {𝔨 : LieSubalgebra ℂ 𝔤}
variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

noncomputable def ktypeBoundedness (M : SL2GKModule 𝔤 K 𝔨 Ad V) : KTypeBoundedness' :=
  open Classical in
  if BddAbove M.ktypeSet then
    if BddBelow M.ktypeSet then
      KTypeBoundedness'.boundedBoth
    else
      KTypeBoundedness'.boundedAbove
  else
    if BddBelow M.ktypeSet then
      KTypeBoundedness'.boundedBelow
    else
      KTypeBoundedness'.unboundedBoth

theorem ktypeBoundedness_eq_boundedBoth_iff (M : SL2GKModule 𝔤 K 𝔨 Ad V) :
    M.ktypeBoundedness = KTypeBoundedness'.boundedBoth ↔
      (BddAbove M.ktypeSet ∧ BddBelow M.ktypeSet) := by
  classical
  simp only [ktypeBoundedness]
  split_ifs with h1 h2 <;> simp_all

theorem ktypeBoundedness_eq_boundedAbove_iff (M : SL2GKModule 𝔤 K 𝔨 Ad V) :
    M.ktypeBoundedness = KTypeBoundedness'.boundedAbove ↔
      (BddAbove M.ktypeSet ∧ ¬ BddBelow M.ktypeSet) := by
  classical
  simp only [ktypeBoundedness]
  split_ifs with h1 h2 <;> simp_all

theorem ktypeBoundedness_eq_boundedBelow_iff (M : SL2GKModule 𝔤 K 𝔨 Ad V) :
    M.ktypeBoundedness = KTypeBoundedness'.boundedBelow ↔
      (¬ BddAbove M.ktypeSet ∧ BddBelow M.ktypeSet) := by
  classical
  simp only [ktypeBoundedness]
  split_ifs with h1 h2 <;> simp_all

theorem ktypeBoundedness_eq_unboundedBoth_iff (M : SL2GKModule 𝔤 K 𝔨 Ad V) :
    M.ktypeBoundedness = KTypeBoundedness'.unboundedBoth ↔
      (¬ BddAbove M.ktypeSet ∧ ¬ BddBelow M.ktypeSet) := by
  classical
  simp only [ktypeBoundedness]
  split_ifs with h1 h2 <;> simp_all

end SL2GKModule
