/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Reflection.HyperplaneChambers

set_option maxHeartbeats 0

open scoped InnerProductSpace
open Set

set_option maxHeartbeats 0

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HyperplaneArrangement

variable {arr : HyperplaneArrangement E}

/-- *Points off all hyperplanes lie in some open half-space of each*: if $x$ is in
`arr.complement` (i.e. on no hyperplane of `arr`), then for any hyperplane $η$, $x$ is in
either $η.positiveHalfSpace$ or $η.negativeHalfSpace$. -/
lemma complement_mem_halfSpace {x : E} (hx : x ∈ arr.complement)
    {η : AffineHyperplane E} (hη : η ∈ arr.hyperplanes) :
    x ∈ η.positiveHalfSpace ∨ x ∈ η.negativeHalfSpace := by
  simp only [HyperplaneArrangement.complement, Set.mem_diff, Set.mem_univ, true_and,
    HyperplaneArrangement.unionSet] at hx
  have hx' : x ∉ η.carrier := by
    intro habs
    exact hx (Set.mem_biUnion hη habs)
  simp only [AffineHyperplane.carrier, AffineHyperplane.positiveHalfSpace,
    AffineHyperplane.negativeHalfSpace, Set.mem_setOf_eq] at hx' ⊢
  exact lt_or_gt_of_ne (Ne.symm hx')

/-- *Positive half-space is open*: convenience alias for `HalfSpaceOpen η`. -/
lemma positiveHalfSpace_isOpen (η : AffineHyperplane E) : IsOpen η.positiveHalfSpace :=
  HalfSpaceOpen η

/-- *Negative half-space is open*: $\{x : \langle n, x\rangle < d\}$ is open as the preimage
of $(-\infty, d)$ under the continuous map $x \mapsto \langle n, x\rangle$. -/
lemma negativeHalfSpace_isOpen (η : AffineHyperplane E) : IsOpen η.negativeHalfSpace := by
  apply isOpen_lt
  exact continuous_const.inner continuous_id
  exact continuous_const

/-- *Open half-spaces are disjoint*: positive and negative open half-spaces of any hyperplane
are disjoint. -/
lemma halfSpaces_disjoint (η : AffineHyperplane E) :
    Disjoint η.positiveHalfSpace η.negativeHalfSpace := by
  rw [Set.disjoint_iff]
  intro z ⟨hz1, hz2⟩
  simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
    Set.mem_setOf_eq] at hz1 hz2
  linarith

/-- *Negative half-space is convex*: parallel to `HalfSpaceConvex` for the positive side;
direct verification with positive convex combinations preserving the strict inequality. -/
lemma negativeHalfSpace_convex (η : AffineHyperplane E) :
    Convex ℝ η.negativeHalfSpace := by
  intro x hx y hy a b ha hb hab
  simp only [AffineHyperplane.negativeHalfSpace, Set.mem_setOf_eq] at *
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp at hab; subst hab; simp; linarith
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · simp at hab; subst hab; simp; linarith
    · have h1 := mul_lt_mul_of_pos_left hx ha_pos
      have h2 := mul_lt_mul_of_pos_left hy hb_pos
      have h3 : a * η.offset + b * η.offset = η.offset := by
        have := congr_arg (· * η.offset) hab; simp [add_mul] at this; linarith
      linarith

/-- *A preconnected subset of the complement that contains a point in the positive half-space
of $η$ is entirely contained in that half-space*: since $S$ is covered by two disjoint open
sets $η.positive$ and $η.negative$, preconnectedness forces $S$ into the one that contains
the witness $x$. -/
lemma connected_subset_in_positive {S : Set E} (hS : IsPreconnected S)
    (hcomp : S ⊆ arr.complement) {η : AffineHyperplane E} (hη : η ∈ arr.hyperplanes)
    {x : E} (hx : x ∈ S) (hxp : x ∈ η.positiveHalfSpace) :
    S ⊆ η.positiveHalfSpace := by
  intro y hy
  by_contra hyp
  have hy_comp := hcomp hy
  rcases complement_mem_halfSpace hy_comp hη with h | h
  · exact hyp h
  · have hS_sub : S ⊆ η.positiveHalfSpace ∪ η.negativeHalfSpace := by
      intro z hz
      exact (complement_mem_halfSpace (hcomp hz) hη).elim Or.inl Or.inr
    have := hS.subset_left_of_subset_union (positiveHalfSpace_isOpen η)
      (negativeHalfSpace_isOpen η) (halfSpaces_disjoint η) hS_sub ⟨x, hx, hxp⟩
    exact hyp (this hy)

/-- *Dual of `connected_subset_in_positive`*: a preconnected subset of the complement that
contains a point in the negative half-space of $η$ is entirely contained in that half-space. -/
lemma connected_subset_in_negative {S : Set E} (hS : IsPreconnected S)
    (hcomp : S ⊆ arr.complement) {η : AffineHyperplane E} (hη : η ∈ arr.hyperplanes)
    {x : E} (hx : x ∈ S) (hxn : x ∈ η.negativeHalfSpace) :
    S ⊆ η.negativeHalfSpace := by
  intro y hy
  by_contra hyp
  have hy_comp := hcomp hy
  rcases complement_mem_halfSpace hy_comp hη with h | h
  · have hS_sub : S ⊆ η.positiveHalfSpace ∪ η.negativeHalfSpace := by
      intro z hz
      exact (complement_mem_halfSpace (hcomp hz) hη).elim Or.inl Or.inr
    have := hS.subset_right_of_subset_union (positiveHalfSpace_isOpen η)
      (negativeHalfSpace_isOpen η) (halfSpaces_disjoint η) hS_sub ⟨x, hx, hxn⟩
    exact hyp (this hy)
  · exact hyp h

/-- *A chamber lies entirely in one open half-space of every hyperplane*: a basic structural
fact about chambers; combines `complement_mem_halfSpace` at a witness point with
`connected_subset_in_positive`/`negative`. -/
theorem chamber_subset_halfSpace (C : arr.Chamber) {η : AffineHyperplane E}
    (hη : η ∈ arr.hyperplanes) :
    C.set ⊆ η.positiveHalfSpace ∨ C.set ⊆ η.negativeHalfSpace := by
  obtain ⟨⟨x, hx⟩, _⟩ := C.isConnected
  have hx_comp := C.subset_complement hx
  rcases complement_mem_halfSpace hx_comp hη with hxp | hxn
  · left
    exact connected_subset_in_positive C.isConnected.isPreconnected C.subset_complement hη hx hxp
  · right
    exact connected_subset_in_negative C.isConnected.isPreconnected C.subset_complement hη hx hxn

/-- *The hyperplane $η$ separates two chambers $C, D$*: each of the two open half-spaces of
$η$ contains exactly one of $C, D$. -/
def SeparatesChambers (η : AffineHyperplane E) (_hη : η ∈ arr.hyperplanes)
    (C D : arr.Chamber) : Prop :=
  (C.set ⊆ η.positiveHalfSpace ∧ D.set ⊆ η.negativeHalfSpace) ∨
  (C.set ⊆ η.negativeHalfSpace ∧ D.set ⊆ η.positiveHalfSpace)

/-- *The chambers $C$ and $D$ are on the same side of $η$*: both lie in the positive
half-space, or both lie in the negative half-space. -/
def SameSide (η : AffineHyperplane E) (_hη : η ∈ arr.hyperplanes)
    (C D : arr.Chamber) : Prop :=
  (C.set ⊆ η.positiveHalfSpace ∧ D.set ⊆ η.positiveHalfSpace) ∨
  (C.set ⊆ η.negativeHalfSpace ∧ D.set ⊆ η.negativeHalfSpace)

/-- *Trichotomy fails — only same-side or separated*: for any hyperplane $η$, two chambers
$C, D$ are either on the same side of $η$ or strictly separated by $η$. Immediate four-way
case split on `chamber_subset_halfSpace`. -/
lemma sameSide_or_separated (C D : arr.Chamber) {η : AffineHyperplane E}
    (hη : η ∈ arr.hyperplanes) :
    SameSide η hη C D ∨ SeparatesChambers η hη C D := by
  rcases chamber_subset_halfSpace C hη with hC | hC <;>
  rcases chamber_subset_halfSpace D hη with hD | hD
  · left; left; exact ⟨hC, hD⟩
  · right; left; exact ⟨hC, hD⟩
  · right; right; exact ⟨hC, hD⟩
  · left; right; exact ⟨hC, hD⟩

/-- *Two chambers are adjacent along $η$*: they are distinct, are separated by $η$, and lie on
the same side of every other hyperplane. This is the natural geometric notion of "differing
only by a single wall reflection". -/
def AdjacentAlong (C D : arr.Chamber) (η : AffineHyperplane E) (hη : η ∈ arr.hyperplanes) :
    Prop :=
  C.set ≠ D.set ∧
  SeparatesChambers η hη C D ∧
  ∀ ξ ∈ arr.hyperplanes, ξ ≠ η →
    ∀ hξ : ξ ∈ arr.hyperplanes, SameSide ξ hξ C D

/-- *Adjacency of chambers*: there exists some hyperplane $η$ of `arr` along which $C$ and $D$
are adjacent. -/
def Adjacent (C D : arr.Chamber) : Prop :=
  ∃ η ∈ arr.hyperplanes, ∃ hη : η ∈ arr.hyperplanes, AdjacentAlong C D η hη

/-- *A point of the complement lying on the correct side of every hyperplane belongs to $C$*:
if for each hyperplane $η$, $x$ shares $C$'s sign, then $x \in C.set$. Proof: take the segment
from some $y \in C$ to $x$; convexity of half-spaces shows the segment avoids every
hyperplane, so $C \cup \text{segment}$ is connected in the complement, and maximality of $C$
forces $x \in C$. -/
lemma mem_chamber_of_same_signs (C : arr.Chamber) {x : E} (_hx : x ∈ arr.complement)
    (hsigns : ∀ η ∈ arr.hyperplanes,
      (C.set ⊆ η.positiveHalfSpace → x ∈ η.positiveHalfSpace) ∧
      (C.set ⊆ η.negativeHalfSpace → x ∈ η.negativeHalfSpace)) :
    x ∈ C.set := by
  by_contra hxC
  obtain ⟨⟨y, hy⟩, hconn⟩ := C.isConnected

  have hy_comp := C.subset_complement hy
  have hseg_comp : segment ℝ y x ⊆ arr.complement := by
    intro z hz
    simp only [complement, Set.mem_diff, Set.mem_univ, true_and, unionSet]
    intro habs
    simp only [Set.mem_iUnion] at habs
    obtain ⟨η, hη_mem, hz_η⟩ := habs
    rcases chamber_subset_halfSpace C hη_mem with hC_pos | hC_neg
    · have hy_pos := hC_pos hy
      have hx_pos := (hsigns η hη_mem).1 hC_pos
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
      have hz_pos := HalfSpaceConvex η hy_pos hx_pos ha hb hab
      simp only [AffineHyperplane.positiveHalfSpace, Set.mem_setOf_eq] at hz_pos
      simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hz_η
      linarith
    · have hy_neg := hC_neg hy
      have hx_neg := (hsigns η hη_mem).2 hC_neg
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
      have hz_neg := negativeHalfSpace_convex η hy_neg hx_neg ha hb hab
      simp only [AffineHyperplane.negativeHalfSpace, Set.mem_setOf_eq] at hz_neg
      simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hz_η
      linarith

  have hseg_conn : IsConnected (segment ℝ y x) :=
    (convex_segment y x).isConnected ⟨y, left_mem_segment ℝ y x⟩

  have hy_in_seg : y ∈ segment ℝ y x := left_mem_segment ℝ y x
  have hunion_conn : IsConnected (C.set ∪ segment ℝ y x) := by
    constructor
    · exact ⟨y, Or.inl hy⟩
    · exact IsPreconnected.union y hy hy_in_seg hconn hseg_conn.isPreconnected

  have hunion_comp : C.set ∪ segment ℝ y x ⊆ arr.complement :=
    Set.union_subset C.subset_complement hseg_comp

  have := C.is_maximal (C.set ∪ segment ℝ y x) hunion_comp hunion_conn Set.subset_union_left

  have hx_in_union : x ∈ C.set ∪ segment ℝ y x :=
    Set.mem_union_right _ (right_mem_segment ℝ y x)
  exact hxC (this hx_in_union)

/-- *Two chambers on the same side of every hyperplane are equal*: a converse to the
trichotomy. Two `Subset.antisymm` applications, each using `mem_chamber_of_same_signs` to
deduce that a point of one chamber lies in the other. -/
lemma chambers_eq_of_sameSide (C D : arr.Chamber)
    (hsame : ∀ η ∈ arr.hyperplanes, ∀ hη : η ∈ arr.hyperplanes, SameSide η hη C D) :
    C.set = D.set := by
  apply Set.Subset.antisymm
  ·
    intro c hc
    have hc_comp := C.subset_complement hc
    apply mem_chamber_of_same_signs D hc_comp
    intro η hη_mem
    have hside := hsame η hη_mem hη_mem
    constructor
    · intro hD_pos
      rcases hside with ⟨hC_pos, _⟩ | ⟨hC_neg, hD_neg⟩
      · exact hC_pos hc
      ·
        obtain ⟨⟨d, hd⟩, _⟩ := D.isConnected
        have := hD_pos hd
        have := hD_neg hd
        simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
          Set.mem_setOf_eq] at *
        linarith
    · intro hD_neg
      rcases hside with ⟨hC_pos, hD_pos⟩ | ⟨hC_neg, _⟩
      · obtain ⟨⟨d, hd⟩, _⟩ := D.isConnected
        have := hD_pos hd
        have := hD_neg hd
        simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
          Set.mem_setOf_eq] at *
        linarith
      · exact hC_neg hc
  ·
    intro d hd
    have hd_comp := D.subset_complement hd
    apply mem_chamber_of_same_signs C hd_comp
    intro η hη_mem
    have hside := hsame η hη_mem hη_mem
    constructor
    · intro hC_pos
      rcases hside with ⟨_, hD_pos⟩ | ⟨hC_neg, _⟩
      · exact hD_pos hd
      · obtain ⟨⟨c, hc⟩, _⟩ := C.isConnected
        have := hC_pos hc
        have := hC_neg hc
        simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
          Set.mem_setOf_eq] at *
        linarith
    · intro hC_neg
      rcases hside with ⟨hC_pos, _⟩ | ⟨_, hD_neg⟩
      · obtain ⟨⟨c, hc⟩, _⟩ := C.isConnected
        have := hC_pos hc
        have := hC_neg hc
        simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
          Set.mem_setOf_eq] at *
        linarith
      · exact hD_neg hd

end HyperplaneArrangement


namespace HyperplaneArrangement

variable {arr : HyperplaneArrangement E}


/-- *No chamber is in both half-spaces simultaneously*: if $C$ were contained in both
$η.positive$ and $η.negative$, any witness point would have $\langle n, x\rangle > d$ and
$< d$ — contradiction. -/
lemma chamber_not_both_sides (C : arr.Chamber) {η : AffineHyperplane E}
    (hpos : C.set ⊆ η.positiveHalfSpace) (hneg : C.set ⊆ η.negativeHalfSpace) : False := by
  obtain ⟨⟨c, hc⟩, _⟩ := C.isConnected
  have := hpos hc
  have := hneg hc
  simp only [AffineHyperplane.positiveHalfSpace, AffineHyperplane.negativeHalfSpace,
    Set.mem_setOf_eq] at *
  linarith

/-- *Adjacent chambers are separated by exactly one wall*: if $C, D$ are adjacent along $η$,
then the only hyperplane separating them is $η$ itself. A four-way case split on the
half-space sides; in each case `chamber_not_both_sides` yields a contradiction. -/
theorem adjacent_separated_by_unique_wall (C D : arr.Chamber)
    {η : AffineHyperplane E} {hη : η ∈ arr.hyperplanes}
    (hadj : AdjacentAlong C D η hη)
    {ξ : AffineHyperplane E} {hξ : ξ ∈ arr.hyperplanes}
    (hsep : SeparatesChambers ξ hξ C D) : ξ = η := by
  by_contra hne
  obtain ⟨_, _, hsame⟩ := hadj
  have := hsame ξ hξ hne hξ

  rcases this with ⟨hC_pos, hD_pos⟩ | ⟨hC_neg, hD_neg⟩ <;>
  rcases hsep with ⟨hCp, hDn⟩ | ⟨hCn, hDp⟩
  · exact chamber_not_both_sides D hD_pos hDn
  · exact chamber_not_both_sides C hC_pos hCn
  · exact chamber_not_both_sides C hCp hC_neg
  · exact chamber_not_both_sides D hDp hD_neg

/-- *Converse to `adjacent_separated_by_unique_wall`*: if $η$ separates $C, D$ and is the
unique separating hyperplane, then $C$ and $D$ are adjacent along $η$. -/
theorem exactly_one_wall_adjacent (C D : arr.Chamber)
    {η : AffineHyperplane E} {hη : η ∈ arr.hyperplanes}
    (hne : C.set ≠ D.set)
    (hsep : SeparatesChambers η hη C D)
    (huniq : ∀ ξ ∈ arr.hyperplanes, ∀ hξ : ξ ∈ arr.hyperplanes,
      SeparatesChambers ξ hξ C D → ξ = η) :
    AdjacentAlong C D η hη := by
  refine ⟨hne, hsep, ?_⟩
  intro ξ hξ_mem hξ_ne hξ

  have hξ_not_sep : ¬ SeparatesChambers ξ hξ C D := by
    intro h
    exact hξ_ne (huniq ξ hξ_mem hξ h)

  rcases sameSide_or_separated C D hξ with hsame | hsep'
  · exact hsame
  · exact absurd hsep' hξ_not_sep

/-- *Hyperplane carrier is closed* (in-namespace alias): the carrier $\{x : \langle n, x\rangle
= d\}$ is closed as the preimage of $\{d\}$ under a continuous map. -/
lemma carrier_isClosed (η : AffineHyperplane E) : IsClosed η.carrier :=
  isClosed_eq (continuous_const.inner continuous_id) continuous_const

/-- *The complement of a locally finite arrangement is open*: for a locally finite arrangement
`arr`, the set $E \setminus arr.unionSet$ is open. Near each $x$, only finitely many
hyperplanes meet a small ball; intersecting the ball with the complements of those finitely
many closed carriers gives an open neighborhood of $x$ contained in the complement. -/
lemma complement_isOpen (hlf : arr.IsLocallyFinite) : IsOpen arr.complement := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx_not : x ∉ arr.unionSet := by
    simp only [complement, Set.mem_diff, Set.mem_univ, true_and] at hx; exact hx
  obtain ⟨ε, hε, hfin⟩ := hlf x

  set S := {h ∈ arr.hyperplanes | (Metric.ball x ε ∩ h.carrier).Nonempty} with hS_def

  have hS_compl_nhds : ∀ h ∈ S, (h.carrier)ᶜ ∈ nhds x := by
    intro h hh
    have hh_mem : h ∈ arr.hyperplanes := hh.1
    have hx_not_carrier : x ∉ h.carrier := by
      intro habs
      exact hx_not (Set.mem_biUnion hh_mem habs)
    exact (carrier_isClosed h).compl_mem_nhds hx_not_carrier

  have hinter_nhds : (⋂ h ∈ S, (h.carrier)ᶜ) ∈ nhds x :=
    (Filter.biInter_mem hfin).mpr hS_compl_nhds

  have hball_nhds : Metric.ball x ε ∈ nhds x := Metric.ball_mem_nhds x hε

  have hT_nhds : Metric.ball x ε ∩ (⋂ h ∈ S, (h.carrier)ᶜ) ∈ nhds x :=
    Filter.inter_mem hball_nhds hinter_nhds

  apply Filter.mem_of_superset hT_nhds
  intro y ⟨hy_ball, hy_inter⟩
  simp only [complement, Set.mem_diff, Set.mem_univ, true_and, unionSet]
  intro hy_union
  rw [Set.mem_iUnion₂] at hy_union
  obtain ⟨h, hh_mem, hy_carrier⟩ := hy_union
  by_cases hh_S : h ∈ S
  ·
    have := Set.mem_iInter₂.mp hy_inter h hh_S
    exact this hy_carrier
  ·
    have : ¬(Metric.ball x ε ∩ h.carrier).Nonempty := by
      intro hne
      exact hh_S ⟨hh_mem, hne⟩
    exact this ⟨y, hy_ball, hy_carrier⟩

/-- *Chambers are open* in a locally finite arrangement: take a ball around $x \in C$ inside
`arr.complement` (using `complement_isOpen`); then $C \cup \text{ball}$ is connected in the
complement, so by the maximality of $C$ the entire ball lies in $C$. -/
lemma chamber_isOpen (C : arr.Chamber) (hlf : arr.IsLocallyFinite) : IsOpen C.set := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hopen := complement_isOpen hlf
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x (C.subset_complement hx)
  have hball_conn : IsConnected (Metric.ball x r) :=
    (convex_ball x r).isConnected ⟨x, Metric.mem_ball_self hr⟩
  have hunion_conn : IsConnected (C.set ∪ Metric.ball x r) := by
    constructor
    · exact ⟨x, Or.inl hx⟩
    · exact IsPreconnected.union x hx (Metric.mem_ball_self hr)
        C.isConnected.isPreconnected hball_conn.isPreconnected
  have hunion_comp : C.set ∪ Metric.ball x r ⊆ arr.complement :=
    Set.union_subset C.subset_complement hball
  have hball_sub : Metric.ball x r ⊆ C.set := fun y hy =>
    C.is_maximal _ hunion_comp hunion_conn Set.subset_union_left (Or.inr hy)
  exact ⟨Metric.ball x r, hball_sub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩

end HyperplaneArrangement
