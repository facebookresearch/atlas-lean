/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Infinity.Sectors

set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- $f$ is bounded above on the set $S$: $∃ c, ∀ z ∈ S, f(z) ≤ c$. -/
def BoundedAboveOn (f : V → ℝ) (S : Set V) : Prop :=
  ∃ c : ℝ, ∀ z ∈ S, f z ≤ c

/-- $f$ is bounded below on $S$: $∃ c, ∀ z ∈ S, c ≤ f(z)$. -/
def BoundedBelowOn (f : V → ℝ) (S : Set V) : Prop :=
  ∃ c : ℝ, ∀ z ∈ S, c ≤ f z

/-- An *affine functional* on an apartment $A$: a function $V → ℝ$ which is affine
along the apartment's geodesic combinations. -/
structure AffineFunctional (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  toFun : V → ℝ
  affineComb : ℝ → V → V → V
  isAffine : ∀ (t : ℝ) (x y : V),
    (∃ s ∈ apartment.faces, x ∈ s) →
    (∃ s ∈ apartment.faces, y ∈ s) →
    toFun (affineComb t x y) = t * toFun x + (1 - t) * toFun y

/-- A *wall* $\eta$ in an apartment: the zero-set of an affine functional, together
with its two half-apartments $\eta^+, \eta^-$ and the axioms that the functional
is unbounded in any sector direction and has a definite sign on each sector. -/
structure Wall (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  vertices : Set V
  vertices_in_apartment : ∀ v ∈ vertices, ∃ s ∈ apartment.faces, v ∈ s
  functional : V → ℝ
  affineComb : ℝ → V → V → V
  functionalIsAffine : ∀ (t : ℝ) (x y : V),
    (∃ s ∈ apartment.faces, x ∈ s) →
    (∃ s ∈ apartment.faces, y ∈ s) →
    functional (affineComb t x y) = t * functional x + (1 - t) * functional y
  functional_vanishes : ∀ v ∈ vertices, functional v = 0
  halfPos : Set V
  halfNeg : Set V
  halfPos_def : ∀ v, (∃ s ∈ apartment.faces, v ∈ s) →
    (v ∈ halfPos ↔ 0 ≤ functional v)
  halfNeg_def : ∀ v, (∃ s ∈ apartment.faces, v ∈ s) →
    (v ∈ halfNeg ↔ functional v ≤ 0)
  halfPos_in_apartment : ∀ v ∈ halfPos, ∃ s ∈ apartment.faces, v ∈ s
  halfNeg_in_apartment : ∀ v ∈ halfNeg, ∃ s ∈ apartment.faces, v ∈ s
  functional_unbounded_on_sectors : ∀ (S : Sector b), S.apartment = apartment →
    ∀ M : ℝ, (∃ v ∈ S.vertices, functional v > M) ∨
             (∃ v ∈ S.vertices, functional v < -M)
  functional_definite_sign : ∀ (S : Sector b), S.apartment = apartment →
    ∀ (f : V → ℝ), (∀ v ∈ vertices, f v = 0) →
    (∀ v ∈ S.vertices, f S.baseVertex ≤ f v) ∨
    (∀ v ∈ S.vertices, f v ≤ f S.baseVertex)

/-- The wall functional is nonnegative on its positive half-apartment. -/
theorem Wall.pos_nonneg {b : Building V} (eta : Wall b) :
    ∀ v ∈ eta.halfPos, 0 ≤ eta.functional v := by
  intro v hv
  have hv_apt := eta.halfPos_in_apartment v hv
  exact (eta.halfPos_def v hv_apt).mp hv

/-- The wall functional is nonpositive on its negative half-apartment. -/
theorem Wall.neg_nonpos {b : Building V} (eta : Wall b) :
    ∀ v ∈ eta.halfNeg, eta.functional v ≤ 0 := by
  intro v hv
  have hv_apt := eta.halfNeg_in_apartment v hv
  exact (eta.halfNeg_def v hv_apt).mp hv

/-- A wall partitions the vertices of a sector into $\eta^+$, $\eta^-$, and the wall itself. -/
theorem Wall.sector_partition
    {b : Building V}
    (eta : Wall b) (S : Sector b) (hS : S.apartment = eta.apartment) :
    ∀ v ∈ S.vertices, v ∈ eta.halfPos ∨ v ∈ eta.halfNeg ∨ v ∈ eta.vertices := by
  intro v hv
  have hv_apt : ∃ s ∈ eta.apartment.faces, v ∈ s := by
    have := S.vertices_in_apartment v hv
    rwa [hS] at this

  rcases le_or_gt 0 (eta.functional v) with h_nonneg | h_neg
  · left
    exact (eta.halfPos_def v hv_apt).mpr h_nonneg
  · right; left
    exact (eta.halfNeg_def v hv_apt).mpr (le_of_lt h_neg)

/-- The wall functional cannot be simultaneously bounded above and below on a sector. -/
theorem Wall.sector_unbounded
    {b : Building V}
    (eta : Wall b) (S : Sector b) (hS : S.apartment = eta.apartment) :
    ¬ ((∃ c : ℝ, ∀ z ∈ S.vertices, eta.functional z ≤ c) ∧
       (∃ c : ℝ, ∀ z ∈ S.vertices, c ≤ eta.functional z)) := by
  intro ⟨⟨c_up, hup⟩, ⟨c_lo, hlo⟩⟩
  have hM := eta.functional_unbounded_on_sectors S hS (|c_up| + |c_lo| + 1)
  rcases hM with ⟨v, hv, hgt⟩ | ⟨v, hv, hlt⟩
  ·
    have := hup v hv
    linarith [abs_nonneg c_lo, le_abs_self c_up]
  ·
    have := hlo v hv
    linarith [abs_nonneg c_up, neg_abs_le c_lo]

/-- A *half-apartment*: a subset of an apartment equal to one of the canonical halves
$\eta^+$ or $\eta^-$ of some wall $\eta$. -/
structure HalfApartment (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  wall : Wall b
  wall_in_apartment : wall.apartment = apartment
  vertices : Set V
  vertices_in_apartment : ∀ v ∈ vertices, ∃ s ∈ apartment.faces, v ∈ s
  is_canonical : vertices = wall.halfPos ∨ vertices = wall.halfNeg

/-- An affine functional *vanishes on the wall* $\eta$ if it agrees on the apartment
and is zero on every wall vertex. -/
def AffineFunctional.VanishesOnWall {b : Building V}
    (af : AffineFunctional b) (eta : Wall b) : Prop :=
  af.apartment = eta.apartment ∧ ∀ v ∈ eta.vertices, af.toFun v = 0

/-- Decomposition: any affine functional on a sector can be written as a constant
(value at the base) plus a linear part vanishing at the base. -/
theorem sector_affine_decomposition {b : Building V}
    (S : Sector b) (af : AffineFunctional b)
    (_haf_apt : af.apartment = S.apartment) :
    ∃ (linear_part : V → ℝ),
      (∀ v ∈ S.vertices, af.toFun v = af.toFun S.baseVertex + linear_part v) ∧
      linear_part S.baseVertex = 0 :=
  ⟨fun v => af.toFun v - af.toFun S.baseVertex,
   fun v _ => by ring,
   by ring⟩

/-- The linear part of an affine functional vanishing on a wall has a definite sign
on a sector parallel to that wall. -/
theorem linear_part_definite_sign {V : Type} [DecidableEq V]
    {b : Building V}
    (S : Sector b) (af : AffineFunctional b) (eta : Wall b)
    (_haf_apt : af.apartment = S.apartment)
    (heta_apt : eta.apartment = S.apartment)
    (hvanish : af.VanishesOnWall eta)
    (linear_part : V → ℝ)
    (hdecomp : ∀ v ∈ S.vertices, af.toFun v = af.toFun S.baseVertex + linear_part v)
    (_hbase_zero : linear_part S.baseVertex = 0) :
    (∀ v ∈ S.vertices, 0 ≤ linear_part v) ∨
    (∀ v ∈ S.vertices, linear_part v ≤ 0) := by

  have hvanish_wall : ∀ v ∈ eta.vertices, af.toFun v = 0 := hvanish.2
  have hsect_apt : S.apartment = eta.apartment := heta_apt.symm
  have hds := eta.functional_definite_sign S hsect_apt af.toFun hvanish_wall

  rcases hds with h_ge | h_le
  ·
    left
    intro v hv
    have := h_ge v hv
    have hd := hdecomp v hv
    linarith
  ·
    right
    intro v hv
    have := h_le v hv
    have hd := hdecomp v hv
    linarith

/-- An affine functional vanishing on a wall is bounded above or below on any sector. -/
theorem affine_functional_bounded_on_sector
    (b : Building V) (S : Sector b) (af : AffineFunctional b) (eta : Wall b)
    (haf_apt : af.apartment = S.apartment)
    (heta_apt : eta.apartment = S.apartment)
    (hvanish : af.VanishesOnWall eta) :
    BoundedAboveOn af.toFun S.vertices ∨ BoundedBelowOn af.toFun S.vertices := by

  obtain ⟨linear_part, hdecomp, hbase_zero⟩ :=
    sector_affine_decomposition S af haf_apt

  have hsign := linear_part_definite_sign S af eta haf_apt heta_apt hvanish
    linear_part hdecomp hbase_zero

  rcases hsign with h_nonneg | h_nonpos
  ·
    right
    exact ⟨af.toFun S.baseVertex, fun z hz => by
      rw [hdecomp z hz]
      linarith [h_nonneg z hz]⟩
  ·
    left
    exact ⟨af.toFun S.baseVertex, fun z hz => by
      rw [hdecomp z hz]
      linarith [h_nonpos z hz]⟩

/-- Signed distance to the wall via the chosen affine functional. -/
def signedDistToWall {b : Building V} (af : AffineFunctional b)
    (_eta : Wall b) (z : V) : ℝ :=
  af.toFun z

/-- (Unsigned) distance to the wall: absolute value of `signedDistToWall`. -/
def distToWall {b : Building V} (af : AffineFunctional b)
    (eta : Wall b) (z : V) : ℝ :=
  |signedDistToWall af eta z|

/-- The wall-distance is bounded above by some $M$ on the intersection of a sector
with a half-apartment. -/
def DistBoundedInHalfApartment {b : Building V}
    (af : AffineFunctional b) (eta : Wall b)
    (S : Sector b) (H : HalfApartment b) : Prop :=
  ∃ M : ℝ, ∀ v ∈ S.vertices, v ∈ H.vertices → distToWall af eta v ≤ M

/-- The negation of `DistBoundedInHalfApartment`: wall-distance is unbounded. -/
def DistUnboundedInHalfApartment {b : Building V}
    (af : AffineFunctional b) (eta : Wall b)
    (S : Sector b) (H : HalfApartment b) : Prop :=
  ¬ DistBoundedInHalfApartment af eta S H

/-- Given a sector $S$ and wall $\eta$, there exists an affine functional vanishing
on $\eta$ that is bounded on one half-apartment and unbounded on the other. -/
theorem wall_distance_bounded_one_side
    (b : Building V)
    (S : Sector b) (eta : Wall b)
    (heta_apt : eta.apartment = S.apartment) :
    ∃ (af : AffineFunctional b) (H₁ H₂ : HalfApartment b),
      af.VanishesOnWall eta ∧
      H₁.wall = eta ∧
      H₂.wall = eta ∧
      DistBoundedInHalfApartment af eta S H₁ ∧
      DistUnboundedInHalfApartment af eta S H₂ := by

  let af : AffineFunctional b :=
    ⟨eta.apartment, eta.apartment_mem, eta.functional, eta.affineComb, eta.functionalIsAffine⟩
  have haf_apt : af.apartment = S.apartment := heta_apt
  have hvanish : af.VanishesOnWall eta := ⟨rfl, eta.functional_vanishes⟩

  have hbound := affine_functional_bounded_on_sector b S af eta haf_apt heta_apt hvanish

  have hnot_both : ¬ (BoundedAboveOn af.toFun S.vertices ∧ BoundedBelowOn af.toFun S.vertices) :=
    eta.sector_unbounded S (heta_apt ▸ rfl)

  let Hpos : HalfApartment b :=
    ⟨eta.apartment, eta.apartment_mem, eta, rfl, eta.halfPos, eta.halfPos_in_apartment, Or.inl rfl⟩
  let Hneg : HalfApartment b :=
    ⟨eta.apartment, eta.apartment_mem, eta, rfl, eta.halfNeg, eta.halfNeg_in_apartment, Or.inr rfl⟩

  have hHpos_wall : Hpos.wall = eta := rfl
  have hHneg_wall : Hneg.wall = eta := rfl
  have hpos_nonneg : ∀ v ∈ Hpos.vertices, 0 ≤ af.toFun v := eta.pos_nonneg
  have hneg_nonpos : ∀ v ∈ Hneg.vertices, af.toFun v ≤ 0 := eta.neg_nonpos

  have hpart : ∀ v ∈ S.vertices, v ∈ Hpos.vertices ∨ v ∈ Hneg.vertices ∨ v ∈ eta.vertices :=
    eta.sector_partition S (heta_apt ▸ rfl)

  rcases hbound with h_above | h_below
  ·
    obtain ⟨c_up, hc_up⟩ := h_above
    have h_not_below : ¬ BoundedBelowOn af.toFun S.vertices := by
      intro h_below_too
      exact hnot_both ⟨⟨c_up, hc_up⟩, h_below_too⟩


    refine ⟨af, Hpos, Hneg, hvanish, hHpos_wall, hHneg_wall, ?_, ?_⟩
    ·
      refine ⟨|c_up|, fun v hv hv_Hpos => ?_⟩
      unfold distToWall signedDistToWall
      have h1 : 0 ≤ af.toFun v := hpos_nonneg v hv_Hpos
      have h2 : af.toFun v ≤ c_up := hc_up v hv
      rw [abs_of_nonneg h1]
      exact le_trans h2 (le_abs_self c_up)
    ·
      intro ⟨M, hM⟩
      apply h_not_below
      refine ⟨-(|M| + 1), fun v hv => ?_⟩
      rcases hpart v hv with hv_pos | hv_neg | hv_wall
      ·
        linarith [hpos_nonneg v hv_pos, abs_nonneg M]
      ·
        have hd := hM v hv hv_neg
        unfold distToWall signedDistToWall at hd
        have h_neg_abs := neg_abs_le (af.toFun v)
        have h_abs_M := le_abs_self M
        linarith
      ·
        have := hvanish.2 v hv_wall
        linarith [abs_nonneg M]
  ·
    obtain ⟨c_lo, hc_lo⟩ := h_below
    have h_not_above : ¬ BoundedAboveOn af.toFun S.vertices := by
      intro h_above_too
      exact hnot_both ⟨h_above_too, ⟨c_lo, hc_lo⟩⟩


    refine ⟨af, Hneg, Hpos, hvanish, hHneg_wall, hHpos_wall, ?_, ?_⟩
    ·
      refine ⟨|c_lo|, fun v hv hv_Hneg => ?_⟩
      unfold distToWall signedDistToWall
      have h1 : af.toFun v ≤ 0 := hneg_nonpos v hv_Hneg
      have h2 : c_lo ≤ af.toFun v := hc_lo v hv
      rw [abs_of_nonpos h1]
      linarith [neg_abs_le c_lo]
    ·
      intro ⟨M, hM⟩
      apply h_not_above
      refine ⟨|M| + 1, fun v hv => ?_⟩
      rcases hpart v hv with hv_pos | hv_neg | hv_wall
      ·
        have hd := hM v hv hv_pos
        unfold distToWall signedDistToWall at hd
        rw [abs_of_nonneg (hpos_nonneg v hv_pos)] at hd
        have h_abs_M := le_abs_self M
        linarith
      ·
        linarith [hneg_nonpos v hv_neg, abs_nonneg M]
      ·
        have := hvanish.2 v hv_wall
        linarith [abs_nonneg M]

/-- Contrapositive corollary of `Wall.sector_unbounded`: bounded below implies not bounded above. -/
theorem not_bounded_above_of_bounded_below_and_unbounded {b : Building V}
    (S : Sector b) (eta : Wall b)
    (heta_apt : eta.apartment = S.apartment)
    (hbelow : BoundedBelowOn eta.functional S.vertices) :
    ¬ BoundedAboveOn eta.functional S.vertices := by
  intro habove
  exact eta.sector_unbounded S (heta_apt ▸ rfl) ⟨habove, hbelow⟩

/-- Symmetric corollary: bounded above implies not bounded below. -/
theorem not_bounded_below_of_bounded_above_and_unbounded {b : Building V}
    (S : Sector b) (eta : Wall b)
    (heta_apt : eta.apartment = S.apartment)
    (habove : BoundedAboveOn eta.functional S.vertices) :
    ¬ BoundedBelowOn eta.functional S.vertices := by
  intro hbelow
  exact eta.sector_unbounded S (heta_apt ▸ rfl) ⟨habove, hbelow⟩

/-- An unbounded-above function attains arbitrarily large values on the sector. -/
theorem exists_vertex_above {b : Building V}
    (S : Sector b) (f : V → ℝ)
    (hnot_above : ¬ BoundedAboveOn f S.vertices)
    (M : ℝ) :
    ∃ v ∈ S.vertices, M < f v := by
  by_contra h
  push_neg at h
  exact hnot_above ⟨M, h⟩

/-- An unbounded-below function attains arbitrarily small values on the sector. -/
theorem exists_vertex_below {b : Building V}
    (S : Sector b) (f : V → ℝ)
    (hnot_below : ¬ BoundedBelowOn f S.vertices)
    (M : ℝ) :
    ∃ v ∈ S.vertices, f v < M := by
  by_contra h
  push_neg at h
  exact hnot_below ⟨M, h⟩

/-- Every sector contains a subsector $S'$ lying entirely in one half-apartment of
a given wall $\eta$ (Section 16.7). -/
theorem sector_subsector_in_half_apartment
    (b : Building V) (S : Sector b) (eta : Wall b)
    (heta_apt : eta.apartment = S.apartment) :
    ∃ (H : HalfApartment b) (S' : Sector b),
      H.wall = eta ∧
      Sector.Subsector b S' S ∧
      ∀ v ∈ S'.vertices, v ∈ H.vertices := by

  have hvanish_func : ∀ v ∈ eta.vertices, eta.functional v = 0 :=
    eta.functional_vanishes
  have hds := eta.functional_definite_sign S (heta_apt ▸ rfl) eta.functional hvanish_func

  rcases hds with h_base_le | h_le_base
  ·

    have hbelow : BoundedBelowOn eta.functional S.vertices :=
      ⟨eta.functional S.baseVertex, fun z hz => h_base_le z hz⟩

    have hnot_above : ¬ BoundedAboveOn eta.functional S.vertices :=
      not_bounded_above_of_bounded_below_and_unbounded S eta heta_apt hbelow

    obtain ⟨v₀, hv₀_mem, hv₀_pos⟩ := exists_vertex_above S eta.functional hnot_above 0

    let S' : Sector b :=
      ⟨S.apartment, S.apartment_mem, v₀,
       S.vertices_in_apartment v₀ hv₀_mem,
       S.vertices, S.vertices_in_apartment,
       hv₀_mem, S.nonempty⟩

    have hds' := eta.functional_definite_sign S' (heta_apt ▸ rfl) eta.functional hvanish_func

    have hS'_verts : S'.vertices = S.vertices := rfl

    have h_incr : ∀ v ∈ S'.vertices, eta.functional v₀ ≤ eta.functional v := by
      rcases hds' with h_incr' | h_decr'
      · exact h_incr'
      ·


        exfalso
        have habove : BoundedAboveOn eta.functional S.vertices :=
          ⟨eta.functional v₀, fun z hz => h_decr' z hz⟩
        exact hnot_above habove

    have hall_pos : ∀ v ∈ S'.vertices, 0 < eta.functional v := by
      intro v hv
      calc 0 < eta.functional v₀ := hv₀_pos
        _ ≤ eta.functional v := h_incr v hv

    have hall_halfPos : ∀ v ∈ S'.vertices, v ∈ eta.halfPos := by
      intro v hv
      have hv_in_S : v ∈ S.vertices := hv
      rcases eta.sector_partition S (heta_apt ▸ rfl) v hv_in_S with hp | hn | hw
      · exact hp
      ·
        exfalso; linarith [eta.neg_nonpos v hn, hall_pos v hv]
      ·
        exfalso; linarith [eta.functional_vanishes v hw, hall_pos v hv]

    let Hpos : HalfApartment b :=
      ⟨eta.apartment, eta.apartment_mem, eta, rfl, eta.halfPos, eta.halfPos_in_apartment, Or.inl rfl⟩
    exact ⟨Hpos, S', rfl, ⟨Set.Subset.refl _, Sector.SameDirection.refl b S⟩, hall_halfPos⟩
  ·

    have habove : BoundedAboveOn eta.functional S.vertices :=
      ⟨eta.functional S.baseVertex, fun z hz => h_le_base z hz⟩

    have hnot_below : ¬ BoundedBelowOn eta.functional S.vertices :=
      not_bounded_below_of_bounded_above_and_unbounded S eta heta_apt habove

    obtain ⟨v₀, hv₀_mem, hv₀_neg⟩ := exists_vertex_below S eta.functional hnot_below 0

    let S' : Sector b :=
      ⟨S.apartment, S.apartment_mem, v₀,
       S.vertices_in_apartment v₀ hv₀_mem,
       S.vertices, S.vertices_in_apartment,
       hv₀_mem, S.nonempty⟩

    have hds' := eta.functional_definite_sign S' (heta_apt ▸ rfl) eta.functional hvanish_func

    have h_decr : ∀ v ∈ S'.vertices, eta.functional v ≤ eta.functional v₀ := by
      rcases hds' with h_incr' | h_decr'
      ·


        exfalso
        have hbelow : BoundedBelowOn eta.functional S.vertices :=
          ⟨eta.functional v₀, fun z hz => h_incr' z hz⟩
        exact hnot_below hbelow
      · exact h_decr'

    have hall_neg : ∀ v ∈ S'.vertices, eta.functional v < 0 := by
      intro v hv
      calc eta.functional v ≤ eta.functional v₀ := h_decr v hv
        _ < 0 := hv₀_neg

    have hall_halfNeg : ∀ v ∈ S'.vertices, v ∈ eta.halfNeg := by
      intro v hv
      have hv_in_S : v ∈ S.vertices := hv
      rcases eta.sector_partition S (heta_apt ▸ rfl) v hv_in_S with hp | hn | hw
      ·
        exfalso; linarith [eta.pos_nonneg v hp, hall_neg v hv]
      · exact hn
      ·
        exfalso; linarith [eta.functional_vanishes v hw, hall_neg v hv]

    let Hneg : HalfApartment b :=
      ⟨eta.apartment, eta.apartment_mem, eta, rfl, eta.halfNeg, eta.halfNeg_in_apartment, Or.inr rfl⟩
    exact ⟨Hneg, S', rfl, ⟨Set.Subset.refl _, Sector.SameDirection.refl b S⟩, hall_halfNeg⟩

/-- $H$ is the *positive* half-apartment for $(S, \eta)$: $H.\text{wall} = \eta$ and
some subsector of $S$ lies entirely in $H$. -/
def IsPositiveHalfApartment {b : Building V}
    (S : Sector b) (eta : Wall b) (H : HalfApartment b) : Prop :=
  H.wall = eta ∧ ∃ S' : Sector b, Sector.Subsector b S' S ∧ ∀ v ∈ S'.vertices, v ∈ H.vertices

/-- For every sector $S$ and wall $\eta$ there is a positive half-apartment $H$. -/
theorem exists_positive_half_apartment
    (b : Building V) (S : Sector b) (eta : Wall b)
    (heta_apt : eta.apartment = S.apartment) :
    ∃ H : HalfApartment b, IsPositiveHalfApartment S eta H := by
  obtain ⟨H, S', hwall, hsubsec, hcontain⟩ :=
    sector_subsector_in_half_apartment b S eta heta_apt
  exact ⟨H, hwall, S', hsubsec, hcontain⟩

end AffineBuilding
