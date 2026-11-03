/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.ApplicationsToGroups
import Mathlib.Topology.Bornology.Basic

set_option linter.unusedSectionVars false

open Set Filter Classical

/-- Set-theoretic product $EF = \{ ef : e \in E, f \in F \}$ in a multiplicative structure. -/
def GroupSetMul {G : Type*} [Mul G] (E F : Set G) : Set G :=
  {g | ∃ e ∈ E, ∃ f ∈ F, g = e * f}

/-- Set-theoretic inverse $E^{-1} = \{e^{-1} : e \in E\}$. -/
def GroupSetInv {G : Type*} [Inv G] (E : Set G) : Set G :=
  {g | ∃ e ∈ E, g = e⁻¹}

/-- Data of a bornology compatible with the group structure on $G$: a family of bounded sets
closed under singletons, subsets, finite unions, group products, and inversion. -/
structure BornologicalGroupData (G : Type*) [Group G] where
  bounded : Set (Set G)
  singleton_mem : ∀ x : G, {x} ∈ bounded
  subset_mem : ∀ E ∈ bounded, ∀ F ⊆ E, F ∈ bounded
  union_mem : ∀ E ∈ bounded, ∀ F ∈ bounded, E ∪ F ∈ bounded
  mul_mem : ∀ E ∈ bounded, ∀ F ∈ bounded, GroupSetMul E F ∈ bounded
  inv_mem : ∀ E ∈ bounded, GroupSetInv E ∈ bounded

namespace BornologicalGroupData

variable {G : Type*} [Group G]

/-- The empty set is bounded. -/
lemma empty_mem (bd : BornologicalGroupData G) : ∅ ∈ bd.bounded :=
  bd.subset_mem {1} (bd.singleton_mem 1) ∅ (empty_subset _)

/-- Underlying mathlib `Bornology` instance from `BornologicalGroupData`. -/
def toBornology (bd : BornologicalGroupData G) : Bornology G :=
  Bornology.ofBounded bd.bounded bd.empty_mem
    (fun s₁ hs₁ s₂ hs₂ => bd.subset_mem s₁ hs₁ s₂ hs₂)
    (fun s₁ hs₁ s₂ hs₂ => bd.union_mem s₁ hs₁ s₂ hs₂)
    bd.singleton_mem

end BornologicalGroupData

namespace BNPairBornology

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- $E \subseteq G$ is bounded relative to a BN-pair if it is covered by finitely many Bruhat cells. -/
def IsBounded (bp : BNPair G M) (E : Set G) : Prop :=
  ∃ (S : Finset M.Group), E ⊆ ⋃ w ∈ S, bp.bruhatCell w

/-- The collection of all sets bounded relative to a BN-pair. -/
def boundedSets (bp : BNPair G M) : Set (Set G) :=
  {E | IsBounded bp E}

/-- Each Bruhat cell is bounded. -/
lemma bruhatCell_isBounded (bp : BNPair G M) (w : M.Group) :
    IsBounded bp (bp.bruhatCell w) :=
  ⟨{w}, subset_biUnion_of_mem (Finset.mem_singleton.mpr rfl)⟩

/-- BN-pair boundedness is closed under taking subsets. -/
lemma isBounded_subset (bp : BNPair G M) {E F : Set G}
    (hE : IsBounded bp E) (hFE : F ⊆ E) : IsBounded bp F := by
  obtain ⟨S, hS⟩ := hE
  exact ⟨S, hFE.trans hS⟩

/-- BN-pair boundedness is closed under binary unions. -/
lemma isBounded_union (bp : BNPair G M) {E F : Set G}
    (hE : IsBounded bp E) (hF : IsBounded bp F) :
    IsBounded bp (E ∪ F) := by
  obtain ⟨S₁, hS₁⟩ := hE
  obtain ⟨S₂, hS₂⟩ := hF
  refine ⟨S₁ ∪ S₂, union_subset ?_ ?_⟩
  · exact hS₁.trans (biUnion_subset_biUnion_left (Finset.coe_subset.mpr Finset.subset_union_left))
  · exact hS₂.trans (biUnion_subset_biUnion_left (Finset.coe_subset.mpr Finset.subset_union_right))

/-- Singletons are bounded when the BN-pair Bruhat decomposition covers $G$. -/
lemma singleton_isBounded (bp : BNPair G M)
    (hcover : ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w)
    (g : G) : IsBounded bp {g} := by
  obtain ⟨w, hw⟩ := hcover g
  exact isBounded_subset bp (bruhatCell_isBounded bp w) (singleton_subset_iff.mpr hw)

/-- The empty set is BN-pair bounded. -/
lemma empty_isBounded (bp : BNPair G M) : IsBounded bp ∅ :=
  ⟨∅, empty_subset _⟩

/-- Promote a BN-pair with cover, product-closure, and inverse-closure to a `BornologicalGroupData`. -/
def toBornologicalGroupData (bp : BNPair G M)
    (hcover : ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w)
    (hmul : ∀ E ∈ boundedSets bp, ∀ F ∈ boundedSets bp,
      GroupSetMul E F ∈ boundedSets bp)
    (hinv : ∀ E ∈ boundedSets bp, GroupSetInv E ∈ boundedSets bp) :
    BornologicalGroupData G where
  bounded := boundedSets bp
  singleton_mem := singleton_isBounded bp hcover
  subset_mem := fun E hE F hFE => isBounded_subset bp hE hFE
  union_mem := fun E hE F hF => isBounded_union bp hE hF
  mul_mem := hmul
  inv_mem := hinv

/-- Bornology on $G$ induced by a BN-pair, given a Bruhat cover. -/
def toBornology (bp : BNPair G M)
    (hcover : ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w) :
    Bornology G :=
  Bornology.ofBounded (boundedSets bp)
    (empty_isBounded bp)
    (fun E hE F hFE => isBounded_subset bp hE hFE)
    (fun E hE F hF => isBounded_union bp hE hF)
    (singleton_isBounded bp hcover)

/-- A set is bounded in the induced bornology iff it is BN-pair bounded. -/
lemma isBounded_iff (bp : BNPair G M)
    (hcover : ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w)
    (E : Set G) :
    @Bornology.IsBounded G (toBornology bp hcover) E ↔ IsBounded bp E :=
  Bornology.isBounded_ofBounded_iff _

/-- Generalized BN-pair boundedness using extended cells parameterized by $\Omega \times M.\mathrm{Group}$. -/
def IsBoundedGeneralized {Ω : Type*} (bp : BNPair G M)
    (extendedCells : Ω × M.Group → Set G) (E : Set G) : Prop :=
  ∃ (S : Finset (Ω × M.Group)), E ⊆ ⋃ σw ∈ S, extendedCells σw

end BNPairBornology
