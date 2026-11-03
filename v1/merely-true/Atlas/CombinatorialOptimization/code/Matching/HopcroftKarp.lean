/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Matching.ShortestAugPathPhase

open SimpleGraph

namespace SimpleGraph

universe u w

structure HopcroftKarpExecution {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  numPhases : ℕ
  matching : Fin (numPhases + 1) → G.Subgraph
  isMatching : ∀ i, (matching i).IsMatching
  isFinalMaximum : ∀ M' : G.Subgraph, M'.IsMatching →
    M'.edgeSet.ncard ≤ (matching ⟨numPhases, Nat.lt_succ_of_le le_rfl⟩).edgeSet.ncard
  size_strictly_increases : ∀ i : Fin numPhases,
    (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).edgeSet.ncard <
    (matching ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩).edgeSet.ncard
  shortestLen : Fin numPhases → ℕ
  shortestLen_spec : ∀ i : Fin numPhases,
    shortestAugPathLength G (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
      ↑(shortestLen i)
  paths : (i : Fin numPhases) →
    VertexDisjointAugPaths.{u, w} G (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (shortestLen i)
  paths_maximal : ∀ i : Fin numPhases, (paths i).IsMaximal
  isAugmentation : ∀ i : Fin numPhases,
    IsAugmentationAlongPaths
      (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (matching ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (paths i)


lemma HopcroftKarpExecution.shortestLen_odd
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (exec : HopcroftKarpExecution.{u, w} G)
    (i : Fin exec.numPhases) :
    Odd (exec.shortestLen i) := by
  have hspec := exec.shortestLen_spec i


  have hne : (augPathLengths G (exec.matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    unfold shortestAugPathLength at hspec
    rw [hempty, sInf_empty] at hspec
    exact absurd hspec (by simp [ENat.top_ne_coe])
  have hmem := csInf_mem hne
  unfold shortestAugPathLength at hspec

  rw [hspec] at hmem

  obtain ⟨u, v, p, haug, hlen⟩ := hmem
  have hodd := augmenting_path_odd_length haug
  rw [p.length_edges] at hodd
  have hlen_eq : p.length = exec.shortestLen i := by
    have := ENat.coe_inj.mp hlen
    exact this
  rwa [hlen_eq] at hodd



lemma HopcroftKarpExecution.matching_size_growth
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (exec : HopcroftKarpExecution.{u, w} G)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ exec.numPhases) :
    (exec.matching ⟨i, Nat.lt_succ_of_le (hij.trans hj)⟩).edgeSet.ncard + (j - i) ≤
    (exec.matching ⟨j, Nat.lt_succ_of_le hj⟩).edgeSet.ncard := by

  induction hij with
  | refl => simp
  | @step m him ih =>

    have hm_le : m ≤ exec.numPhases := Nat.le_of_succ_le hj
    have ih_applied := ih hm_le
    have hm_lt : m < exec.numPhases := Nat.lt_of_succ_le hj
    have hstep := exec.size_strictly_increases ⟨m, hm_lt⟩

    have heq1 : (exec.matching ⟨m, Nat.lt_succ_of_lt hm_lt⟩).edgeSet.ncard =
                (exec.matching ⟨m, Nat.lt_succ_of_le hm_le⟩).edgeSet.ncard := by congr 2
    have heq2 : (exec.matching ⟨m + 1, Nat.succ_lt_succ hm_lt⟩).edgeSet.ncard =
                (exec.matching ⟨m + 1, Nat.lt_succ_of_le hj⟩).edgeSet.ncard := by congr 2
    have heq3 : (exec.matching ⟨i, Nat.lt_succ_of_le (Nat.le_trans him hm_le)⟩).edgeSet.ncard =
                (exec.matching ⟨i, Nat.lt_succ_of_le (Nat.le_trans (Nat.le_succ_of_le him) hj)⟩).edgeSet.ncard := by
      congr 2
    rw [heq1, heq2] at hstep
    rw [heq3] at ih_applied


    have hi_le_m : i ≤ m := him
    have hsub : m + 1 - i = (m - i) + 1 := Nat.succ_sub hi_le_m
    linarith [hsub]



end SimpleGraph
