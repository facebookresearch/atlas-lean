/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open SimpleGraph Set

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {A B : Set V}

theorem hall_marriage_theorem (hBip : G.IsBipartiteWith A B) :
    (∃ M : Subgraph G, A ⊆ M.verts ∧ M.IsMatching) ↔
    (∀ U ⊆ A, U.ncard ≤ (⋃ x ∈ U, G.neighborSet x).ncard) := by
  constructor
  ·
    rintro ⟨M, hAM, hM⟩ U hUA
    by_cases hUfin : U.Finite
    · classical
      have hUM : U ⊆ M.verts := hUA.trans hAM

      have match_exists : ∀ u ∈ U, ∃ w, M.Adj u w := fun u hu =>
        let ⟨w, hw, _⟩ := hM (hUM hu)
        ⟨w, hw⟩

      let f : V → V := fun u => if h : u ∈ U then (match_exists u h).choose else u

      have hf_mem : ∀ u ∈ U, f u ∈ (⋃ x ∈ U, G.neighborSet x) := by
        intro u hu
        simp only [f, dif_pos hu]
        have hadj : M.Adj u (match_exists u hu).choose := (match_exists u hu).choose_spec
        exact Set.mem_biUnion hu ((G.mem_neighborSet u _).mpr (M.adj_sub hadj))

      have hf_inj : InjOn f U := by
        intro u₁ hu₁ u₂ hu₂ hfeq
        simp only [f, dif_pos hu₁, dif_pos hu₂] at hfeq
        have hadj₁ : M.Adj u₁ (match_exists u₁ hu₁).choose := (match_exists u₁ hu₁).choose_spec
        have hadj₂ : M.Adj u₂ (match_exists u₂ hu₂).choose := (match_exists u₂ hu₂).choose_spec
        exact hM.eq_of_adj_right (hfeq ▸ hadj₁) hadj₂

      have hN_fin : (⋃ x ∈ U, G.neighborSet x).Finite :=
        hUfin.biUnion (fun v _ => Set.Finite.ofFinset (G.neighborFinset v)
          (fun x => by simp [SimpleGraph.neighborFinset_def]))
      exact Set.ncard_le_ncard_of_injOn f hf_mem hf_inj hN_fin
    ·
      rw [Set.Infinite.ncard (Set.not_finite.mp hUfin)]
      exact Nat.zero_le _
  ·

    exact exists_isMatching_of_forall_ncard_le hBip

end SimpleGraph
