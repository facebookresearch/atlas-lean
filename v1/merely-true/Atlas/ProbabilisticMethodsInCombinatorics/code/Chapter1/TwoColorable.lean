/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
open Finset Fintype

namespace TwoColorableHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A hypergraph on vertex set `V` is a finite collection of subsets (edges). -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

/-- An edge `e` is monochromatic under a 2-coloring `c` if all its vertices share the
same color. -/
def IsMonochromatic (e : Finset V) (c : V → Bool) : Prop :=
  (∀ v ∈ e, c v = true) ∨ (∀ v ∈ e, c v = false)

/-- Decidability of `IsMonochromatic`. -/
instance (e : Finset V) (c : V → Bool) : Decidable (IsMonochromatic e c) := by
  unfold IsMonochromatic; exact instDecidableOr

/-- A hypergraph is 2-colorable (Property B) if there exists a 2-coloring of its vertices
under which no edge is monochromatic. -/
def IsTwoColorable (E : Hypergraph V) : Prop :=
  ∃ c : V → Bool, ∀ e ∈ E, ¬IsMonochromatic e c

/-- A hypergraph is $k$-uniform if every edge has size exactly $k$. -/
def IsKUniform (E : Hypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ E, e.card = k

/-- The number of Boolean colorings of `V` that take constant value `b` on a finite set
`e` is at most $2^{|V| - |e|}$. -/
lemma card_colorings_all_eq (e : Finset V) (b : Bool) :
    (Finset.univ.filter (fun c : V → Bool => ∀ v ∈ e, c v = b)).card
    ≤ 2 ^ (Fintype.card V - e.card) := by
  have hcard_codomain : Fintype.card ({v : V // v ∉ e} → Bool) =
      2 ^ (Fintype.card V - e.card) := by
    rw [Fintype.card_fun, Fintype.card_bool]
    congr 1
    rw [Fintype.card_subtype, Finset.filter_not, Finset.card_univ_diff,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc (Finset.univ.filter (fun c : V → Bool => ∀ v ∈ e, c v = b)).card
      ≤ Fintype.card ({v : V // v ∉ e} → Bool) := by
        rw [Fintype.card]
        apply Finset.card_le_card_of_injOn
          (fun c => fun (v : {v : V // v ∉ e}) => c v.val)
          (fun _ _ => Finset.mem_univ _)
        intro c₁ hc₁ c₂ hc₂ heq
        simp only [Finset.coe_filter, Finset.mem_univ, true_and,
                   Set.mem_setOf_eq] at hc₁ hc₂
        funext v
        by_cases hv : v ∈ e
        · rw [hc₁ v hv, hc₂ v hv]
        · exact congr_fun heq ⟨v, hv⟩
    _ = 2 ^ (Fintype.card V - e.card) := hcard_codomain

/-- The number of colorings making an edge `e` monochromatic is at most
$2^{|V| - k + 1}$ whenever $|e| \ge k$. -/
lemma card_mono_colorings_le (e : Finset V) (k : ℕ) (hk : k ≤ e.card) :
    (Finset.univ.filter (fun c : V → Bool => IsMonochromatic e c)).card
    ≤ 2 ^ (Fintype.card V - k + 1) := by
  have h_sub : Finset.univ.filter (fun c : V → Bool => IsMonochromatic e c) ⊆
      (Finset.univ.filter (fun c : V → Bool => ∀ v ∈ e, c v = true)) ∪
      (Finset.univ.filter (fun c : V → Bool => ∀ v ∈ e, c v = false)) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    cases hc.2 with
    | inl h => exact Or.inl ⟨Finset.mem_univ _, h⟩
    | inr h => exact Or.inr ⟨Finset.mem_univ _, h⟩
  calc (Finset.univ.filter (fun c : V → Bool => IsMonochromatic e c)).card
      ≤ ((Finset.univ.filter (fun c : V → Bool => ∀ v ∈ e, c v = true)) ∪
         (Finset.univ.filter (fun c : V → Bool => ∀ v ∈ e, c v = false))).card :=
        Finset.card_le_card h_sub
    _ ≤ (Finset.univ.filter (fun c : V → Bool => ∀ v ∈ e, c v = true)).card +
        (Finset.univ.filter (fun c : V → Bool => ∀ v ∈ e, c v = false)).card :=
        Finset.card_union_le _ _
    _ ≤ 2 ^ (Fintype.card V - e.card) + 2 ^ (Fintype.card V - e.card) := by
        gcongr
        · exact card_colorings_all_eq e true
        · exact card_colorings_all_eq e false
    _ = 2 ^ (Fintype.card V - e.card + 1) := by omega
    _ ≤ 2 ^ (Fintype.card V - k + 1) := by
        apply Nat.pow_le_pow_right (by omega : 0 < 2)
        omega

/-- (Theorem 1.3.1, $m(k) \ge 2^{k-1}$) Every $k$-uniform (or larger) hypergraph with
fewer than $2^{k-1}$ edges is 2-colorable. -/
theorem erdos_two_colorable
    (E : Hypergraph V) (k : ℕ) (hk : 1 ≤ k)
    (hsize : ∀ e ∈ E, k ≤ e.card)
    (hcard : E.card < 2 ^ (k - 1)) :
    IsTwoColorable E := by
  classical
  by_cases hE : E = ∅
  · exact ⟨fun _ => true, fun e he => absurd he (by simp [hE])⟩
  have hkn : k ≤ Fintype.card V := by
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hE
    exact (hsize e he).trans (Finset.card_le_univ e)
  suffices h_bound : (Finset.univ.filter (fun c : V → Bool =>
      ∃ e ∈ E, IsMonochromatic e c)).card < Fintype.card (V → Bool) by
    have hne : (Finset.univ \ (Finset.univ.filter (fun c : V → Bool =>
        ∃ e ∈ E, IsMonochromatic e c))).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
      intro hsub
      have heq : Finset.univ.filter (fun c : V → Bool =>
          ∃ e ∈ E, IsMonochromatic e c) = Finset.univ :=
        Finset.eq_univ_iff_forall.mpr (fun c => hsub (Finset.mem_univ c))
      rw [heq, Finset.card_univ] at h_bound
      exact lt_irrefl _ h_bound
    obtain ⟨c, hc⟩ := hne
    rw [Finset.mem_sdiff, Finset.mem_filter] at hc
    push Not at hc
    exact ⟨c, fun e he => hc.2 (Finset.mem_univ _) e he⟩
  let n := Fintype.card V
  calc (Finset.univ.filter (fun c : V → Bool => ∃ e ∈ E, IsMonochromatic e c)).card
      ≤ (E.biUnion (fun e => Finset.univ.filter
          (fun c : V → Bool => IsMonochromatic e c))).card := by
        apply Finset.card_le_card
        intro c hc
        rw [Finset.mem_filter] at hc
        rw [Finset.mem_biUnion]
        obtain ⟨e, he, hm⟩ := hc.2
        exact ⟨e, he, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
    _ ≤ E.card * 2 ^ (n - k + 1) := by
        apply Finset.card_biUnion_le_card_mul
        intro e he
        exact card_mono_colorings_le e k (hsize e he)
    _ < 2 ^ (k - 1) * 2 ^ (n - k + 1) := by
        apply Nat.mul_lt_mul_of_pos_right hcard
        exact Nat.pos_of_ne_zero (fun h => by simp at h)
    _ = 2 ^ n := by
        rw [← pow_add]; congr 1; omega
    _ = Fintype.card (V → Bool) := by
        rw [Fintype.card_fun, Fintype.card_bool]



end TwoColorableHypergraph
