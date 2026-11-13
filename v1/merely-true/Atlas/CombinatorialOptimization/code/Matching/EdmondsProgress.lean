/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Matching.BlossomShrinking

open SimpleGraph

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure AlternatingForest (G : SimpleGraph V) (M : G.Subgraph) where
  forestVerts : Finset V
  root : V → V
  level : V → ℕ
  roots_unmatched : ∀ v ∈ forestVerts, level v = 0 → v ∉ M.verts
  root_mem : ∀ v ∈ forestVerts, root v ∈ forestVerts
  root_level : ∀ v ∈ forestVerts, level (root v) = 0
  root_self : ∀ v ∈ forestVerts, root v = v ↔ level v = 0
  odd_level_matched : ∀ v ∈ forestVerts, Odd (level v) → v ∈ M.verts
  unmatched_are_roots : ∀ v, v ∉ M.verts → v ∈ forestVerts
  unmatched_level_zero : ∀ v ∈ forestVerts, v ∉ M.verts → level v = 0
  matched_partner_even : ∀ v ∈ forestVerts, Odd (level v) →
    ∀ w, M.Adj v w → w ∈ forestVerts ∧ Even (level w) ∧ root w = root v

def AlternatingForest.isEvenLevel (F : AlternatingForest G M) (v : V) : Prop :=
  v ∈ F.forestVerts ∧ Even (F.level v)

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
lemma walk_level_induction (M : G.Subgraph)
    (F : AlternatingForest G M)
    (hsat : ∀ u v, G.Adj u v → F.isEvenLevel u → v ∈ F.forestVerts ∧ Odd (F.level v))
    {s t : V} (p : G.Walk s t)
    (halt : Walk.IsAlternatingFrom p M)
    (hs_forest : s ∈ F.forestVerts)
    (hs_even : Even (F.level s)) :
    ∀ i, i ≤ p.length →
      p.getVert i ∈ F.forestVerts ∧
      (Even i → Even (F.level (p.getVert i))) ∧
      (Odd i → Odd (F.level (p.getVert i))) := by
  intro i hi
  induction i with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rwa [Walk.getVert_zero]
    · intro _; rwa [Walk.getVert_zero]
    · intro h; exact absurd h (by decide)
  | succ k ih =>
    have hk_le : k ≤ p.length := Nat.le_of_succ_le hi
    have hk_lt : k < p.length := Nat.lt_of_succ_le hi
    obtain ⟨hk_mem, hk_even_imp, hk_odd_imp⟩ := ih hk_le
    have hadj_k : G.Adj (p.getVert k) (p.getVert (k + 1)) :=
      Walk.adj_getVert_succ p hk_lt
    have hk_edge_len : k < p.edges.length := by rw [Walk.length_edges]; exact hk_lt
    have hedge := halt k hk_edge_len
    have hedge_eq := Walk.edges_getElem_eq p k hk_edge_len
    by_cases hk_parity : Even k
    ·
      have hk_even_level := hk_even_imp hk_parity
      have hk_isEven : F.isEvenLevel (p.getVert k) := ⟨hk_mem, hk_even_level⟩
      have hsat_app := hsat (p.getVert k) (p.getVert (k + 1)) hadj_k hk_isEven
      refine ⟨hsat_app.1, ?_, ?_⟩
      · intro h_succ_even
        exact absurd (hk_parity.add_one) (Nat.not_odd_iff_even.mpr h_succ_even)
      · intro _; exact hsat_app.2
    ·
      have hk_odd : Odd k := Nat.not_even_iff_odd.mp hk_parity
      have hk_odd_level := hk_odd_imp hk_odd
      have hedge_M := hedge.2 hk_odd
      rw [hedge_eq] at hedge_M
      have hM_adj : M.Adj (p.getVert k) (p.getVert (k + 1)) :=
        Subgraph.mem_edgeSet.mp hedge_M
      have hpartner := F.matched_partner_even (p.getVert k) hk_mem hk_odd_level
        (p.getVert (k + 1)) hM_adj
      refine ⟨hpartner.1, ?_, ?_⟩
      · intro _; exact hpartner.2.1
      · intro h_succ_odd
        exact absurd h_succ_odd (Nat.not_odd_iff_even.mpr (hk_odd.add_one))

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
theorem no_augmenting_path_of_saturated (M : G.Subgraph)
    (F : AlternatingForest G M)
    (hsat : ∀ u v, G.Adj u v → F.isEvenLevel u → v ∈ F.forestVerts ∧ Odd (F.level v)) :
    ¬ HasAugmentingPath G M := by
  intro ⟨s, t, p, hpath, hst, hs_unmatched, ht_unmatched, halt⟩
  have hs_forest : s ∈ F.forestVerts := F.unmatched_are_roots s hs_unmatched
  have hs_level_zero : F.level s = 0 := F.unmatched_level_zero s hs_forest hs_unmatched
  have hs_even : Even (F.level s) := hs_level_zero ▸ ⟨0, by omega⟩
  have ht_forest : t ∈ F.forestVerts := F.unmatched_are_roots t ht_unmatched
  have hlen_pos : 0 < p.length := by
    cases p with
    | nil => exact absurd rfl hst
    | cons _ _ => exact Nat.succ_pos _
  have ht_info := walk_level_induction M F hsat p halt hs_forest hs_even p.length (le_refl _)
  rw [Walk.getVert_length] at ht_info
  obtain ⟨_, ht_even_imp, ht_odd_imp⟩ := ht_info
  by_cases h_len_even : Even p.length
  ·
    have hlast_pos : p.length - 1 < p.length := Nat.sub_lt hlen_pos Nat.one_pos
    have hlast_edge_len : p.length - 1 < p.edges.length := by
      rw [Walk.length_edges]; exact hlast_pos
    have hlast_odd : Odd (p.length - 1) := by
      obtain ⟨k, hk⟩ := h_len_even
      exact ⟨k - 1, by omega⟩
    have hedge_last := (halt (p.length - 1) hlast_edge_len).2 hlast_odd
    have hedge_eq_last := Walk.edges_getElem_eq p (p.length - 1) hlast_edge_len
    rw [hedge_eq_last] at hedge_last
    have hlen_sub : p.length - 1 + 1 = p.length := Nat.succ_pred_eq_of_pos hlen_pos
    rw [hlen_sub, Walk.getVert_length] at hedge_last
    have hM_adj_t : M.Adj (p.getVert (p.length - 1)) t := Subgraph.mem_edgeSet.mp hedge_last
    exact ht_unmatched (M.edge_vert hM_adj_t.symm)
  ·
    have h_len_odd : Odd p.length := Nat.not_even_iff_odd.mp h_len_even
    exact ht_unmatched (F.odd_level_matched t ht_forest (ht_odd_imp h_len_odd))


end SimpleGraph
