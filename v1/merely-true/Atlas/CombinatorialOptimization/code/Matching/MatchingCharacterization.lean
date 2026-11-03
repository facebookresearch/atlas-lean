/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace MatchingPolytope

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def IsMatchingSet (M : Set (Sym2 V)) : Prop :=
  M ⊆ G.edgeSet ∧ ∀ e₁ ∈ M, ∀ e₂ ∈ M, ∀ v : V, v ∈ e₁ → v ∈ e₂ → e₁ = e₂

theorem indicator_is_matching (x : Sym2 V → ℕ)
    (_hx01 : ∀ e ∈ G.edgeFinset, x e = 0 ∨ x e = 1)
    (hdeg : ∀ v : V, ∑ e ∈ G.incidenceFinset v, x e ≤ 1) :
    IsMatchingSet G {e | e ∈ G.edgeFinset ∧ x e = 1} := by
  refine ⟨fun e he => ?_, fun e₁ he₁ e₂ he₂ v hv₁ hv₂ => ?_⟩
  ·
    simp only [Set.mem_setOf_eq] at he
    exact mem_edgeFinset.mp he.1
  ·
    simp only [Set.mem_setOf_eq] at he₁ he₂
    obtain ⟨he₁_mem, hxe₁⟩ := he₁
    obtain ⟨he₂_mem, hxe₂⟩ := he₂
    by_contra h
    have hv_inc₁ : e₁ ∈ G.incidenceFinset v := by
      rw [mem_incidenceFinset]
      exact ⟨mem_edgeFinset.mp he₁_mem, hv₁⟩
    have hv_inc₂ : e₂ ∈ G.incidenceFinset v := by
      rw [mem_incidenceFinset]
      exact ⟨mem_edgeFinset.mp he₂_mem, hv₂⟩
    have hle : 2 ≤ ∑ e ∈ G.incidenceFinset v, x e := by
      calc 2 = x e₁ + x e₂ := by omega
        _ = ∑ e ∈ ({e₁, e₂} : Finset _), x e := by
            rw [Finset.sum_pair h]
        _ ≤ ∑ e ∈ G.incidenceFinset v, x e :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun e he => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at he
                cases he with
                | inl h => subst h; exact hv_inc₁
                | inr h => subst h; exact hv_inc₂)
              (fun _ _ _ => Nat.zero_le _)
    linarith [hdeg v]

end MatchingPolytope
