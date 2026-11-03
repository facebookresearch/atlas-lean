/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerCombinatorial
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Finset

namespace TriangleIntersecting

/-- A family $F$ of graphs on a common vertex set is triangle-intersecting if every pair of
graphs in $F$ shares at least one triangle, i.e. $G_1 \cap G_2$ contains a 3-clique. -/
def IsTriangleIntersecting {n : ℕ} (F : Finset (SimpleGraph (Fin n))) : Prop :=
  ∀ G₁ ∈ F, ∀ G₂ ∈ F, ¬ (G₁ ⊓ G₂).CliqueFree 3

/-- Any graph on at most 2 vertices is triangle-free (3-clique-free). -/
lemma cliqueFree_three_of_card_le_two {n : ℕ} (hn : n ≤ 2)
    (G : SimpleGraph (Fin n)) : G.CliqueFree 3 := by
  intro s hs
  have hle := Finset.card_le_univ s
  simp only [Fintype.card_fin] at hle
  linarith [hs.card_eq]

/-- Base case of the triangle-intersecting bound for $n \le 2$: such a family must be empty. -/
lemma triangle_intersecting_bound_small {n : ℕ} (hn : n ≤ 2)
    (F : Finset (SimpleGraph (Fin n)))
    (hF : IsTriangleIntersecting F) :
    F.card < 2 ^ (Nat.choose n 2 - 2) := by
  suffices F.card = 0 by simp [this]
  rw [Finset.card_eq_zero]
  by_contra hne
  have hne' : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨G, hG⟩ := hne'
  have h := hF G hG G hG
  simp only [inf_idem] at h
  exact h (cliqueFree_three_of_card_le_two hn G)

/-- A graph on 3 vertices that contains a 3-clique must be the complete graph $K_3$. -/
lemma complete_of_not_cliqueFree_fin3 (G : SimpleGraph (Fin 3))
    (h : ¬ G.CliqueFree 3) : G = ⊤ := by
  rw [SimpleGraph.not_cliqueFree_iff] at h
  obtain ⟨f⟩ := h
  have hsurj : Function.Surjective f := Finite.surjective_of_injective f.injective
  ext a b
  simp only [SimpleGraph.top_adj]
  constructor
  · exact G.ne_of_adj
  · intro hne
    obtain ⟨a', ha'⟩ := hsurj a
    obtain ⟨b', hb'⟩ := hsurj b
    have hab' : a' ≠ b' := fun heq => hne (by rw [← ha', ← hb', heq])
    rw [← ha', ← hb']
    rw [f.map_rel_iff]
    simp [SimpleGraph.completeGraph, hab']

/-- The triangle-intersecting bound for $n = 3$: the family contains only $K_3$, so its cardinality
is at most $1 < 2$. -/
lemma triangle_intersecting_bound_three
    (F : Finset (SimpleGraph (Fin 3)))
    (hF : IsTriangleIntersecting F) :
    F.card < 2 ^ (Nat.choose 3 2 - 2) := by
  norm_num
  suffices h : F ⊆ ({⊤} : Finset (SimpleGraph (Fin 3))) by
    have := Finset.card_le_card h
    simp at this
    omega
  intro G hG
  simp only [Finset.mem_singleton]
  exact complete_of_not_cliqueFree_fin3 G (by have := hF G hG G hG; simpa using this)

/-- Arithmetic lemma extracting the exponent gain from the covering relation
$k m = r s$ together with $2r < m$: $(r-1) s < (m-2) k$. -/
theorem coverage_arithmetic {r s m k : ℕ} (hr : 1 ≤ r)
    (hcov : k * m = r * s) (hlt : 2 * r < m) (hk : 0 < k) :
    (r - 1) * s < (m - 2) * k := by
  have hm : 2 ≤ m := by omega
  zify [hr, hm] at *
  nlinarith

/-- From the Shearer-style power inequality $|F|^k \le (2^{r-1})^s$ combined with the arithmetic
gap $(r-1) s < (m-2) k$, deduce the desired bound $|F| < 2^{m-2}$. -/
theorem bound_from_pow_bound {F_card r s m k : ℕ}
    (hpow : F_card ^ k ≤ (2 ^ (r - 1)) ^ s)
    (harith : (r - 1) * s < (m - 2) * k) :
    F_card < 2 ^ (m - 2) := by
  have h1 : (2 ^ (r - 1)) ^ s < (2 ^ (m - 2)) ^ k := by
    rw [← pow_mul, ← pow_mul]
    exact Nat.pow_lt_pow_right (by omega) harith
  exact lt_of_pow_lt_pow_left' k (lt_of_le_of_lt hpow h1)



end TriangleIntersecting
