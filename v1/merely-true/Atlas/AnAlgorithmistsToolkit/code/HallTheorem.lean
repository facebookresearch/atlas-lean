/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Atlas.AnAlgorithmistsToolkit.code.Expanders

open Finset Function SimpleGraph

namespace HallTheorem

def BipartiteExpander {L R : Type*} [DecidableEq R] [Fintype L]
    (neighbors : L → Finset R) (α β : ℝ) : Prop :=
  ∀ (S : Finset L),
    (S.card : ℝ) ≤ α * (Fintype.card L : ℝ) →
    (β * S.card : ℝ) ≤ ((S.biUnion neighbors).card : ℝ)

theorem hall_marriage_theorem {L R : Type*} [Finite L] [DecidableEq R]
    (neighbors : L → Finset R) :
    (∀ (S : Finset L), S.card ≤ (S.biUnion neighbors).card) ↔
    ∃ f : L → R, Function.Injective f ∧ ∀ x, f x ∈ neighbors x :=
  Finset.all_card_le_biUnion_card_iff_existsInjective' neighbors

theorem bipartite_expander_matching
    {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]
    (neighbors : L → Finset R) (α β : ℝ)
    (hexp : BipartiteExpander neighbors α β)
    (hβ : 1 < β)
    (S : Finset L)
    (hS : (S.card : ℝ) ≤ α * (Fintype.card L : ℝ)) :
    ∃ f : S → R, Function.Injective f ∧ ∀ x : S, f x ∈ neighbors x := by
  classical
  rw [← Finset.all_card_le_biUnion_card_iff_existsInjective']
  intro S'

  let S'L : Finset L := S'.image (Subtype.val)
  have hS'L_card : S'L.card = S'.card :=
    Finset.card_image_of_injective S' Subtype.coe_injective

  have hS'L_sub : S'L ⊆ S := by
    intro x hx
    simp only [S'L, Finset.mem_image] at hx
    obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
    exact hy

  have hS'L_small : (S'L.card : ℝ) ≤ α * (Fintype.card L : ℝ) :=
    calc (S'L.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hS'L_sub
      _ ≤ α * (Fintype.card L : ℝ) := hS

  have hexp_S'L := hexp S'L hS'L_small

  have h_biUnion_eq : S'L.biUnion neighbors = S'.biUnion (fun x => neighbors x) := by
    ext r
    simp only [S'L, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨l, ⟨⟨s, hs, rfl⟩, hr⟩⟩
      exact ⟨s, hs, hr⟩
    · rintro ⟨⟨l, hl⟩, hs, hr⟩
      exact ⟨l, ⟨⟨⟨l, hl⟩, hs, rfl⟩, hr⟩⟩
  rw [← h_biUnion_eq, ← hS'L_card]

  by_cases hS'_empty : S'L.card = 0
  · simp [hS'_empty]
  ·
    have hS'_pos : (0 : ℝ) < S'L.card := by exact_mod_cast Nat.pos_of_ne_zero hS'_empty
    have : (S'L.card : ℝ) < ((S'L.biUnion neighbors).card : ℝ) :=
      calc (S'L.card : ℝ) = 1 * S'L.card := by ring
        _ < β * S'L.card := by nlinarith
        _ ≤ (S'L.biUnion neighbors).card := hexp_S'L
    exact_mod_cast le_of_lt this

structure MultibutterflyNetwork (N : ℕ) (numLayers : ℕ) where
  α : ℝ
  β : ℝ
  hβ : 1 < β
  upNeighbors : Fin numLayers → (Fin N → Finset (Fin N))
  downNeighbors : Fin numLayers → (Fin N → Finset (Fin N))
  upIsExpander : ∀ i, BipartiteExpander (upNeighbors i) α β
  downIsExpander : ∀ i, BipartiteExpander (downNeighbors i) α β

structure LayerAssignment (N : ℕ) (α : ℝ) where
  up : Finset (Fin N)
  down : Finset (Fin N)
  disjoint : Disjoint up down
  up_small : (up.card : ℝ) ≤ α * N
  down_small : (down.card : ℝ) ≤ α * N

def RoutingAssignment (N numLayers : ℕ) (α : ℝ) :=
  Fin numLayers → LayerAssignment N α

theorem multibutterfly_can_route
    {N numLayers : ℕ} (net : MultibutterflyNetwork N numLayers)
    (assignments : RoutingAssignment N numLayers net.α) :
    ∀ (i : Fin numLayers),
      (∃ fUp : (assignments i).up → Fin N,
        Function.Injective fUp ∧
        ∀ x : (assignments i).up, fUp x ∈ net.upNeighbors i (x : Fin N)) ∧
      (∃ fDown : (assignments i).down → Fin N,
        Function.Injective fDown ∧
        ∀ x : (assignments i).down, fDown x ∈ net.downNeighbors i (x : Fin N)) := by
  intro i
  refine ⟨?_, ?_⟩
  ·
    exact bipartite_expander_matching (net.upNeighbors i) net.α net.β
      (net.upIsExpander i) net.hβ (assignments i).up
      (by simp only [Fintype.card_fin]; exact (assignments i).up_small)
  ·
    exact bipartite_expander_matching (net.downNeighbors i) net.α net.β
      (net.downIsExpander i) net.hβ (assignments i).down
      (by simp only [Fintype.card_fin]; exact (assignments i).down_small)

def uniqueNeighbors {L R : Type*} [DecidableEq L] [DecidableEq R]
    (neighbors : L → Finset R) (S : Finset L) : Finset R :=
  (S.biUnion neighbors).filter fun r => (S.filter fun l => r ∈ neighbors l).card = 1

theorem unique_neighbors_lower_bound
    {L R : Type*} [DecidableEq R]
    (neighbors : L → Finset R) (d : ℕ) (β : ℝ)
    (S : Finset L)
    (hexp : (β * S.card : ℝ) ≤ ((S.biUnion neighbors).card : ℝ))
    (A B : Finset R)
    (hAB_union : A ∪ B = S.biUnion neighbors)
    (hAB_disj : Disjoint A B)
    (hedge : (A.card : ℝ) + 2 * (B.card : ℝ) ≤ (d : ℝ) * S.card) :
    ((2 * β - d) * S.card : ℝ) ≤ (A.card : ℝ) := by
  have hAB_card : (A.card : ℝ) + (B.card : ℝ) ≥ β * S.card := by
    have h1 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB_disj
    have h2 : ((S.biUnion neighbors).card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
      rw [← hAB_union]; exact_mod_cast h1
    linarith
  linarith

end HallTheorem

namespace SimpleGraph

section HallMatchingLemma

open Finset

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable (G : SimpleGraph (L ⊕ R)) [DecidableRel G.Adj]

def rightDegreeInS (S : Finset L) (r : R) : ℕ :=
  (S.filter fun l => G.Adj (Sum.inl l) (Sum.inr r)).card

def uniqueNeighbors (S : Finset L) : Finset R :=
  Finset.univ.filter fun r => G.rightDegreeInS S r = 1

def multiNeighbors (S : Finset L) : Finset R :=
  Finset.univ.filter fun r => G.rightDegreeInS S r ≥ 2

def IsBipartiteOn : Prop :=
  (∀ l₁ l₂ : L, ¬G.Adj (Sum.inl l₁) (Sum.inl l₂)) ∧
  (∀ r₁ r₂ : R, ¬G.Adj (Sum.inr r₁) (Sum.inr r₂))

omit [Fintype L] [DecidableEq L] [DecidableEq R] in
theorem bipartiteNeighborFinset_eq_filter_pos (S : Finset L) :
    G.bipartiteNeighborFinset S =
      Finset.univ.filter fun r => 0 < G.rightDegreeInS S r := by
  ext r
  simp only [bipartiteNeighborFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    rightDegreeInS]
  constructor
  · rintro ⟨l, hl, hadj⟩
    exact Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hadj⟩⟩
  · intro h
    obtain ⟨l, hl⟩ := Finset.card_pos.mp h
    rw [Finset.mem_filter] at hl
    exact ⟨l, hl.1, hl.2⟩

omit [Fintype L] [DecidableEq L] in
theorem bipartiteNeighborFinset_eq_unique_union_multi (S : Finset L) :
    G.bipartiteNeighborFinset S = G.uniqueNeighbors S ∪ G.multiNeighbors S := by
  rw [G.bipartiteNeighborFinset_eq_filter_pos S]
  ext r
  simp only [uniqueNeighbors, multiNeighbors, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  omega

omit [Fintype L] [DecidableEq L] [DecidableEq R] in
theorem uniqueNeighbors_disjoint_multiNeighbors (S : Finset L) :
    Disjoint (G.uniqueNeighbors S) (G.multiNeighbors S) := by
  simp only [uniqueNeighbors, multiNeighbors]
  rw [Finset.disjoint_filter]
  intro _ _ h1 h2; omega

omit [DecidableEq L] [DecidableEq R] in
theorem card_filter_adj_right_eq_of_regular_bipartite {d : ℕ}
    (hbip : G.IsBipartiteOn) (hreg : G.IsRegularOfDegree d) (l : L) :
    (Finset.univ.filter fun r => G.Adj (Sum.inl l) (Sum.inr r)).card = d := by
  have hdeg := hreg (Sum.inl l)
  suffices G.neighborFinset (Sum.inl l) =
    (Finset.univ.filter fun r => G.Adj (Sum.inl l) (Sum.inr r)).map
      ⟨Sum.inr, Sum.inr_injective⟩ by
    rw [degree, this, Finset.card_map] at hdeg
    exact hdeg
  ext x
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · intro hadj
    cases x with
    | inl l' => exact absurd hadj (hbip.1 l l')
    | inr r => exact ⟨r, hadj, rfl⟩
  · rintro ⟨r, hadj, rfl⟩
    exact hadj

omit [DecidableEq L] [DecidableEq R] in
theorem sum_leftRightDegree_eq_d_mul_card {d : ℕ}
    (hbip : G.IsBipartiteOn) (hreg : G.IsRegularOfDegree d) (S : Finset L) :
    (S.sum fun l => (Finset.univ.filter fun r => G.Adj (Sum.inl l) (Sum.inr r)).card) =
      d * S.card := by
  simp only [G.card_filter_adj_right_eq_of_regular_bipartite hbip hreg]
  simp [Finset.sum_const, mul_comm]

omit [Fintype L] [DecidableEq L] [DecidableEq R] in
theorem double_count_edges (S : Finset L) :
    (S.sum fun l => (Finset.univ.filter fun r => G.Adj (Sum.inl l) (Sum.inr r)).card) =
    (Finset.univ.sum fun r => G.rightDegreeInS S r) := by
  simp only [rightDegreeInS, Finset.card_filter]
  rw [Finset.sum_comm]

omit [Fintype L] [DecidableEq L] in
theorem sum_rightDegreeInS_ge (S : Finset L) :
    (Finset.univ.sum fun r => G.rightDegreeInS S r) ≥
      (G.uniqueNeighbors S).card + 2 * (G.multiNeighbors S).card := by
  have hd := G.uniqueNeighbors_disjoint_multiNeighbors S
  have hunion : Finset.univ.sum (fun r => G.rightDegreeInS S r) ≥
    (G.uniqueNeighbors S ∪ G.multiNeighbors S).sum (fun r => G.rightDegreeInS S r) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hsplit : (G.uniqueNeighbors S ∪ G.multiNeighbors S).sum (fun r => G.rightDegreeInS S r) =
    (G.uniqueNeighbors S).sum (fun r => G.rightDegreeInS S r) +
    (G.multiNeighbors S).sum (fun r => G.rightDegreeInS S r) :=
    Finset.sum_union hd

  have hunique : (G.uniqueNeighbors S).sum (fun r => G.rightDegreeInS S r) =
    (G.uniqueNeighbors S).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [uniqueNeighbors, Finset.mem_filter] at hr
    exact hr.2

  have hmulti : (G.multiNeighbors S).sum (fun r => G.rightDegreeInS S r) ≥
    2 * (G.multiNeighbors S).card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    simp only [multiNeighbors, Finset.mem_filter] at hr
    linarith [hr.2]
  linarith

omit [DecidableEq L] in
theorem unique_neighbors_lower_bound {d : ℕ} {α β : ℝ}
    (hbip : G.IsBipartiteOn)
    (hreg : G.IsRegularOfDegree d)
    (hexp : G.IsBipartiteExpander α β)
    (S : Finset L) (hS : (S.card : ℝ) ≤ α * (Fintype.card L : ℝ)) :
    ((G.uniqueNeighbors S).card : ℝ) ≥ (2 * β - ↑d) * (S.card : ℝ) := by
  set A := G.uniqueNeighbors S with hA_def
  set B := G.multiNeighbors S with hB_def

  have hexp_ineq : (A.card : ℝ) + (B.card : ℝ) ≥ β * (S.card : ℝ) := by
    have hNS := hexp S hS
    rw [G.bipartiteNeighborFinset_eq_unique_union_multi S,
      Finset.card_union_of_disjoint (G.uniqueNeighbors_disjoint_multiNeighbors S)] at hNS
    push_cast at hNS ⊢
    linarith

  have hedge : (d : ℝ) * (S.card : ℝ) ≥ (A.card : ℝ) + 2 * (B.card : ℝ) := by
    have h1 := G.sum_rightDegreeInS_ge S
    rw [← G.double_count_edges S,
      G.sum_leftRightDegree_eq_d_mul_card hbip hreg S] at h1

    exact_mod_cast h1

  nlinarith

end HallMatchingLemma

end SimpleGraph
