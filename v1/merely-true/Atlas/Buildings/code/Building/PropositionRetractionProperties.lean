/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.FixedPointSubgroups

set_option linter.unusedSectionVars false

noncomputable section

open Set

namespace PropositionRetractionProperties

open FixedPointSubgroups in
/-- A subset $E \subseteq G$ is bounded in the building-bornology if and only
if there exists some $x \in X$ whose $E$-orbit is bounded in the apartment. -/
theorem boundedSubsets_iff_exists_orbit_bounded
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (E : Set Gt) :
    ctx.born.isBounded E ↔
      ∃ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x) := by
  constructor
  ·
    intro hE
    obtain ⟨x⟩ := ctx.nonempty
    exact ⟨x, (BoundedSubsetsEquivalence ctx E).1 hE x⟩
  ·

    intro ⟨x, hx⟩
    exact (BoundedSubsetsEquivalence ctx E).2.2
      (fun Y hY => (BoundedSubsetsEquivalence ctx E).2.1 ⟨x, hx⟩ Y hY)

open FixedPointSubgroups in
/-- A subset $E \subseteq G$ is bounded in the bornology iff its action sends
every bounded subset $Y \subseteq X$ to a bounded subset. -/
theorem boundedSubsets_iff_forall_action_bounded
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (E : Set Gt) :
    ctx.born.isBounded E ↔
      (∀ Y : Set ctx.X, Bornology.IsBounded Y →
        Bornology.IsBounded (actionOnSet ctx.action E Y)) := by
  constructor
  ·
    intro hE Y hY
    have h12 := (BoundedSubsetsEquivalence ctx E).1 hE
    obtain ⟨x⟩ := ctx.nonempty
    exact (BoundedSubsetsEquivalence ctx E).2.1 ⟨x, h12 x⟩ Y hY
  ·
    exact (BoundedSubsetsEquivalence ctx E).2.2

open FixedPointSubgroups in
/-- There exists some $x \in X$ with bounded orbit iff every bounded subset
of $X$ has bounded image under $E$. -/
theorem exists_orbit_bounded_iff_forall_action_bounded
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (E : Set Gt) :
    (∃ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x)) ↔
      (∀ Y : Set ctx.X, Bornology.IsBounded Y →
        Bornology.IsBounded (actionOnSet ctx.action E Y)) := by
  constructor
  ·
    exact (BoundedSubsetsEquivalence ctx E).2.1
  ·
    intro h_all
    obtain ⟨x₀⟩ := ctx.nonempty
    exact ⟨x₀, by rw [← actionOnSet_singleton]; exact h_all {x₀} Bornology.isBounded_singleton⟩

open FixedPointSubgroups in
/-- The point stabilizer of $x$ is bounded in the bornology iff its orbit at
$x$ is bounded. -/
theorem stabilizer_born_bounded_iff_orbit_bounded
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (x : ctx.X) :
    ctx.born.isBounded (pointStabilizer ctx.action x : Set Gt) ↔
      Bornology.IsBounded (orbitSet ctx.action (pointStabilizer ctx.action x : Set Gt) x) := by
  constructor
  · intro h
    exact born_bounded_orbit_bounded ctx _ h x
  · intro h
    exact orbit_bounded_born_bounded ctx _ ⟨x, h⟩

open FixedPointSubgroups in
/-- For subsets contained in $G$, the bornology bound is equivalent to the
existence of a bounded orbit. -/
theorem boundedSubsets_G_iff_orbit_bounded
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (E : Set Gt)
    (hE_in_G : E ⊆ (ctx.gbnpair.G : Set Gt)) :
    ctx.born.isBounded E ↔
      ∃ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x) :=
  boundedSubsets_iff_exists_orbit_bounded ctx E

end PropositionRetractionProperties
