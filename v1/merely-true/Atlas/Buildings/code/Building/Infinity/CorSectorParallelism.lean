/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Infinity.SectorParallelism

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- A wall's defining functional is either strictly positive on all of $S$ or
strictly negative on all of $S$ — sectors do not straddle walls. -/
theorem sector_functional_strictly_positive_or_negative
    (b : Building V) (S : Sector b) (eta : Wall b)
    (heta_apt : eta.apartment = S.apartment) :
    (∀ v ∈ S.vertices, 0 < eta.functional v) ∨
    (∀ v ∈ S.vertices, eta.functional v < 0) := by
  have hvanish : ∀ v ∈ eta.vertices, eta.functional v = 0 := eta.functional_vanishes
  have hds := eta.functional_definite_sign S (heta_apt ▸ rfl) eta.functional hvanish
  rcases hds with h_base_le | h_le_base
  · left
    have hbelow : BoundedBelowOn eta.functional S.vertices :=
      ⟨eta.functional S.baseVertex, fun z hz => h_base_le z hz⟩
    have hnot_above : ¬ BoundedAboveOn eta.functional S.vertices :=
      not_bounded_above_of_bounded_below_and_unbounded S eta heta_apt hbelow
    obtain ⟨v₁, hv₁_mem, hv₁_pos⟩ := exists_vertex_above S eta.functional hnot_above 0
    let S' : Sector b :=
      ⟨S.apartment, S.apartment_mem, v₁,
       S.vertices_in_apartment v₁ hv₁_mem,
       S.vertices, S.vertices_in_apartment,
       hv₁_mem, S.nonempty⟩
    have hds' := eta.functional_definite_sign S' (heta_apt ▸ rfl) eta.functional hvanish
    have h_incr : ∀ v ∈ S'.vertices, eta.functional v₁ ≤ eta.functional v := by
      rcases hds' with h_incr' | h_decr'
      · exact h_incr'
      · exfalso; exact hnot_above ⟨eta.functional v₁, fun z hz => h_decr' z hz⟩
    intro v hv
    calc 0 < eta.functional v₁ := hv₁_pos
      _ ≤ eta.functional v := h_incr v hv
  · right
    have habove : BoundedAboveOn eta.functional S.vertices :=
      ⟨eta.functional S.baseVertex, fun z hz => h_le_base z hz⟩
    have hnot_below : ¬ BoundedBelowOn eta.functional S.vertices :=
      not_bounded_below_of_bounded_above_and_unbounded S eta heta_apt habove
    obtain ⟨v₁, hv₁_mem, hv₁_neg⟩ := exists_vertex_below S eta.functional hnot_below 0
    let S' : Sector b :=
      ⟨S.apartment, S.apartment_mem, v₁,
       S.vertices_in_apartment v₁ hv₁_mem,
       S.vertices, S.vertices_in_apartment,
       hv₁_mem, S.nonempty⟩
    have hds' := eta.functional_definite_sign S' (heta_apt ▸ rfl) eta.functional hvanish
    have h_decr : ∀ v ∈ S'.vertices, eta.functional v ≤ eta.functional v₁ := by
      rcases hds' with h_incr' | h_decr'
      · exfalso; exact hnot_below ⟨eta.functional v₁, fun z hz => h_incr' z hz⟩
      · exact h_decr'
    intro v hv
    calc eta.functional v ≤ eta.functional v₁ := h_decr v hv
      _ < 0 := hv₁_neg

/-- A positive half-apartment for $(S, \eta)$ is exactly one of the canonical halves
`eta.halfPos` or `eta.halfNeg`, determined by the sign of $\eta$ on $S$. -/
theorem positive_half_apartment_canonical_side
    {b : Building V} {S : Sector b} {eta : Wall b} {H : HalfApartment b}
    (heta_apt : eta.apartment = S.apartment)
    (hpos : IsPositiveHalfApartment S eta H) :
    (H.vertices = eta.halfPos ∧ ∀ v ∈ S.vertices, 0 < eta.functional v) ∨
    (H.vertices = eta.halfNeg ∧ ∀ v ∈ S.vertices, eta.functional v < 0) := by
  obtain ⟨hwall, T, hT_sub, hT_in_H⟩ := hpos
  have hbase_in_S : T.baseVertex ∈ S.vertices := hT_sub.1 T.baseVertex_in_sector
  have hbase_in_H : T.baseVertex ∈ H.vertices :=
    hT_in_H T.baseVertex T.baseVertex_in_sector

  have hH_canon : H.vertices = eta.halfPos ∨ H.vertices = eta.halfNeg := by
    rcases H.is_canonical with h | h
    · left; rw [← hwall]; exact h
    · right; rw [← hwall]; exact h
  rcases sector_functional_strictly_positive_or_negative b S eta heta_apt with
    hall_pos | hall_neg
  ·
    left
    constructor
    ·
      have hbase_pos : 0 < eta.functional T.baseVertex := hall_pos _ hbase_in_S
      rcases hH_canon with h | h
      · exact h
      · exfalso
        have hbase_in_neg : T.baseVertex ∈ eta.halfNeg := h ▸ hbase_in_H
        linarith [eta.neg_nonpos T.baseVertex hbase_in_neg]
    · exact hall_pos
  ·
    right
    constructor
    ·
      have hbase_neg : eta.functional T.baseVertex < 0 := hall_neg _ hbase_in_S
      rcases hH_canon with h | h
      · exfalso
        have hbase_in_pos : T.baseVertex ∈ eta.halfPos := h ▸ hbase_in_H
        linarith [eta.pos_nonneg T.baseVertex hbase_in_pos]
      · exact h
    · exact hall_neg

/-- Two positive half-apartments for the same sector and wall have the same vertex
set — the positive side is canonical. -/
theorem positive_half_apartment_unique_vertices
    {b : Building V} {S : Sector b} {eta : Wall b}
    {H₁ H₂ : HalfApartment b}
    (heta_apt : eta.apartment = S.apartment)
    (hpos₁ : IsPositiveHalfApartment S eta H₁)
    (hpos₂ : IsPositiveHalfApartment S eta H₂) :
    H₁.vertices = H₂.vertices := by
  rcases positive_half_apartment_canonical_side heta_apt hpos₁ with
    ⟨h₁, hstrict₁⟩ | ⟨h₁, hstrict₁⟩ <;>
  rcases positive_half_apartment_canonical_side heta_apt hpos₂ with
    ⟨h₂, hstrict₂⟩ | ⟨h₂, hstrict₂⟩
  ·
    rw [h₁, h₂]
  ·
    exfalso
    obtain ⟨_, T₁, hT₁_sub, _⟩ := hpos₁
    have hbase_in_S : T₁.baseVertex ∈ S.vertices := hT₁_sub.1 T₁.baseVertex_in_sector
    linarith [hstrict₁ T₁.baseVertex hbase_in_S, hstrict₂ T₁.baseVertex hbase_in_S]
  ·
    exfalso
    obtain ⟨_, T₁, hT₁_sub, _⟩ := hpos₁
    have hbase_in_S : T₁.baseVertex ∈ S.vertices := hT₁_sub.1 T₁.baseVertex_in_sector
    linarith [hstrict₁ T₁.baseVertex hbase_in_S, hstrict₂ T₁.baseVertex hbase_in_S]
  ·
    rw [h₁, h₂]

/-- Parallel sectors $S_1 \sim S_2$ select the same positive half-apartment with
respect to a fixed wall $\eta$. -/
theorem parallel_sectors_positive_half_apartment_unique_vertices
    {b : Building V} {S₁ S₂ : Sector b} {eta : Wall b}
    {H₁ H₂ : HalfApartment b}
    (hpar : Sector.SameDirection b S₁ S₂)
    (heta_apt₁ : eta.apartment = S₁.apartment)
    (heta_apt₂ : eta.apartment = S₂.apartment)
    (hpos₁ : IsPositiveHalfApartment S₁ eta H₁)
    (hpos₂ : IsPositiveHalfApartment S₂ eta H₂) :
    H₁.vertices = H₂.vertices := by

  have hpos₁_for_S₂ : IsPositiveHalfApartment S₂ eta H₁ :=
    parallel_sectors_same_positive_half_apartment hpar heta_apt₁ heta_apt₂ hpos₁

  exact positive_half_apartment_unique_vertices heta_apt₂ hpos₁_for_S₂ hpos₂

end AffineBuilding
