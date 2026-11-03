/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.FixedPointSubgroups

set_option maxHeartbeats 1600000

set_option linter.unusedSectionVars false

noncomputable section

open Set

namespace GoodMaximalBounded

/-- Every element of the Borel subgroup $B$ lies in the Bruhat cell
$B \cdot 1 \cdot B$ indexed by the identity. -/
theorem mem_bruhatCell_one_of_mem_B
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (b : G) (hb : b ∈ bp.B) :
    b ∈ bp.bruhatCell 1 := by
  refine ⟨⟨b, hb⟩, ⟨1, bp.N.one_mem⟩, ⟨1, bp.B.one_mem⟩, ?_, ?_⟩
  · exact bp.π.map_one
  · simp [mul_one]

/-- The identity belongs to every parabolic subgroup $W_{S'} \leq W$. -/
theorem one_mem_parabolicSubgroupW
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (S' : Set B_idx) :
    (1 : M.Group) ∈ bp.parabolicSubgroupW S' :=
  (bp.parabolicSubgroupW S').one_mem

/-- The Borel subgroup $B$ is contained in every standard parabolic
$P_{S'} = B W_{S'} B$. -/
theorem B_subset_standardParabolic
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (S' : Set B_idx) :
    (bp.B : Set G) ⊆ bp.standardParabolic S' := by
  intro b hb
  have h_cell := mem_bruhatCell_one_of_mem_B bp b hb
  have h_one := one_mem_parabolicSubgroupW bp S'
  exact Set.mem_biUnion h_one h_cell

/-- Subgroup-level statement: if $H \leq G$ has underlying set equal to the
standard parabolic $P_{S'}$, then $B \leq H$. -/
theorem B_le_standardParabolic_subgroup
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (S' : Set B_idx)
    (H : Subgroup G) (hH : (H : Set G) = bp.standardParabolic S') :
    bp.B ≤ H := by
  intro b hb
  have h1 : b ∈ bp.standardParabolic S' := B_subset_standardParabolic bp S' hb
  show b ∈ (H : Set G)
  rw [hH]
  exact h1

/-- Under the Bruhat properties, each standard parabolic $P_{S'}$ is the
underlying set of an honest subgroup of $G$. -/
theorem standardParabolic_is_subgroup
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp) (S' : Set B_idx) :
    ∃ H : Subgroup G, (H : Set G) = bp.standardParabolic S' := by
  refine ⟨{
    carrier := bp.standardParabolic S'
    mul_mem' := ?_
    one_mem' := ?_
    inv_mem' := ?_
  }, rfl⟩
  ·
    intro a b ha hb
    show a * b ∈ bp.standardParabolic S'
    unfold BNPair.standardParabolic at ha hb ⊢
    rw [Set.mem_iUnion₂] at ha hb ⊢
    obtain ⟨w, hw, ha_cell⟩ := ha
    obtain ⟨w', hw', hb_cell⟩ := hb
    obtain ⟨u, hu, hab_cell⟩ := bd.cell_mul_in_parabolic S' w w' hw hw' a b ha_cell hb_cell
    exact ⟨u, hu, hab_cell⟩
  ·
    show (1 : G) ∈ bp.standardParabolic S'
    exact B_subset_standardParabolic bp S' bp.B.one_mem
  ·
    intro a ha
    show a⁻¹ ∈ bp.standardParabolic S'
    unfold BNPair.standardParabolic at ha ⊢
    rw [Set.mem_iUnion₂] at ha ⊢
    obtain ⟨w, hw, ha_cell⟩ := ha
    exact ⟨w⁻¹, (bp.parabolicSubgroupW S').inv_mem hw, bd.cell_inv w a ha_cell⟩

/-- The set of generators fixing the chosen vertex $s_0$: everything in
$S \setminus \{s_0\}$. -/
def vertexFixingGenerators {B_idx : Type*} (_M : CoxeterMatrix B_idx)
    (s₀ : B_idx) : Set B_idx :=
  Set.univ \ {s₀}

/-- A permutation $\sigma$ of the generator index set stabilises the vertex
$s_0$ iff it maps the subset $S \setminus \{s_0\}$ to itself. -/
def PermStabilizesSx {B_idx : Type*} (M : CoxeterMatrix B_idx)
    (s₀ : B_idx) (σ : Equiv.Perm B_idx) : Prop :=
  ∀ s : B_idx, s ∈ vertexFixingGenerators M s₀ → σ s ∈ vertexFixingGenerators M s₀

/-- Lift a subgroup of $G \leq G^t$ to a subgroup of $G^t$ via the inclusion. -/
def liftK₀ {Gt : Type*} [Group Gt] {B_idx : Type*}
    {M : CoxeterMatrix B_idx}
    (gbnpair : GeneralizedBNPair Gt M)
    (K₀ : Subgroup (gbnpair.G : Set Gt).Elem) : Subgroup Gt :=
  K₀.map gbnpair.G.subtype

/-- The set product $\Omega' \cdot K_0$ inside $G^t$, where $K_0$ is lifted
from $G$ to $G^t$. -/
def productSetOmegaPrimeK₀ {Gt : Type*} [Group Gt] {B_idx : Type*}
    {M : CoxeterMatrix B_idx}
    (gbnpair : GeneralizedBNPair Gt M)
    (Ω' : Subgroup Gt)
    (K₀ : Subgroup (gbnpair.G : Set Gt).Elem) : Set Gt :=
  setMul (Ω' : Set Gt) ((liftK₀ gbnpair K₀ : Subgroup Gt) : Set Gt)

/-- Compatibility condition: the bornology on $G^t$ extends the one on $G$,
i.e. bounded subsets of $G$ have bounded image in $G^t$. -/
def BornologyLiftCompatible {Gt : Type*} [Group Gt] {B_idx : Type*}
    {M : CoxeterMatrix B_idx}
    (gbnpair : GeneralizedBNPair Gt M)
    (bornG : CompactSubgroups.GroupBornology (gbnpair.G : Set Gt).Elem)
    (bornGt : CompactSubgroups.GroupBornology Gt) : Prop :=
  ∀ (S : Set (gbnpair.G : Set Gt).Elem),
    bornG.isBounded S →
    bornGt.isBounded (gbnpair.G.subtype '' S)

/-- The data needed to construct good maximal bounded subgroups of $G^t$: a
generalised BN-pair, bornologies on $G$ and $G^t$, a linear-part homomorphism
on $W$, existence of a good maximal bounded subgroup $K_0$ in $G$, and
bornological compatibility between the two groups. -/
structure GoodBoundedSetup (Gt : Type*) [Group Gt] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) where
  gbnpair : GeneralizedBNPair Gt M
  bornG : CompactSubgroups.GroupBornology (gbnpair.G : Set Gt).Elem
  bornGt : CompactSubgroups.GroupBornology Gt
  linearPart : M.Group →* M.Group
  K₀_exists : Nonempty (CompactSubgroups.GoodMaximalBounded
    gbnpair.strictBNPair bornG linearPart)
  bornology_compatible : BornologyLiftCompatible gbnpair bornG bornGt




end GoodMaximalBounded
