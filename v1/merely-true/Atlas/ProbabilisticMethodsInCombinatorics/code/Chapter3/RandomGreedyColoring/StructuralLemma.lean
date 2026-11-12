/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable

open Finset Fintype

namespace TwoColorableHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `IsMaxIn σ v e` says that $v$ belongs to the edge $e$ and attains the maximum value of
the ordering $\sigma$ on $e$. -/
def IsMaxIn (σ : V → ℕ) (v : V) (e : Finset V) : Prop :=
  v ∈ e ∧ ∀ u ∈ e, σ u ≤ σ v

/-- `IsMinIn σ v e` says that $v$ belongs to the edge $e$ and attains the minimum value of
the ordering $\sigma$ on $e$. -/
def IsMinIn (σ : V → ℕ) (v : V) (e : Finset V) : Prop :=
  v ∈ e ∧ ∀ u ∈ e, σ v ≤ σ u

/-- A hypergraph $H$ has a *conflicting pair* under the ordering $\sigma$ if there are two
edges $e, f \in H$ and a vertex $v$ such that $v$ is the $\sigma$-maximum of $e$, the
$\sigma$-minimum of $f$, and $e \cap f = \{v\}$. -/
def HasConflictingPair (H : Hypergraph V) (σ : V → ℕ) : Prop :=
  ∃ e ∈ H, ∃ f ∈ H, ∃ v : V,
    IsMaxIn σ v e ∧ IsMinIn σ v f ∧ (e ∩ f = {v})

/-- The greedy 2-coloring induced by an injective ordering $\sigma$: process vertices in
increasing $\sigma$-order and color $v$ `false` if there is an edge $e \ni v$ whose other
vertices are smaller than $v$ and already colored `true`; otherwise color $v$ `true`. -/
noncomputable def greedyCol (σ : V → ℕ) (hσ : Function.Injective σ)
    (H : Hypergraph V) : V → Bool := by
  classical
  exact WellFounded.fix (InvImage.wf σ Nat.lt_wfRel.wf) fun v ih =>
    if ∃ e ∈ H, v ∈ e ∧ (∀ u ∈ e, σ u ≤ σ v) ∧
       (∀ u ∈ e, (hlt : σ u < σ v) → ih u hlt = true)
    then false
    else true

/-- Fixed-point unfolding of `greedyCol`: the color of $v$ is determined by whether some
edge containing $v$ has $v$ as $\sigma$-max and all strictly smaller vertices colored `true`. -/
lemma greedyCol_eq (σ : V → ℕ) (hσ : Function.Injective σ)
    (H : Hypergraph V) (v : V) :
    greedyCol σ hσ H v =
      if ∃ e ∈ H, v ∈ e ∧ (∀ u ∈ e, σ u ≤ σ v) ∧
         (∀ u ∈ e, σ u < σ v → greedyCol σ hσ H u = true)
      then false
      else true := by
  unfold greedyCol
  rw [WellFounded.fix_eq]

/-- Characterization of when `greedyCol σ hσ H v` equals `false`: there must exist an edge
$e \ni v$ on which $v$ is the $\sigma$-maximum and every strictly smaller vertex was colored
`true`. -/
lemma greedyCol_false_iff (σ : V → ℕ) (hσ : Function.Injective σ)
    (H : Hypergraph V) (v : V) :
    greedyCol σ hσ H v = false ↔
      ∃ e ∈ H, v ∈ e ∧ (∀ u ∈ e, σ u ≤ σ v) ∧
        (∀ u ∈ e, σ u < σ v → greedyCol σ hσ H u = true) := by
  constructor
  · intro h
    rw [greedyCol_eq] at h
    split_ifs at h with hcond
    · exact hcond
  · intro h
    rw [greedyCol_eq]
    simp only [h, ite_true]

/-- No edge of a $k$-uniform hypergraph ($k \geq 2$) is monochromatically colored `true`
by the greedy coloring: the $\sigma$-maximum vertex of any edge would have been recolored
`false`. -/
lemma greedyCol_no_all_true (σ : V → ℕ) (hσ : Function.Injective σ)
    (H : Hypergraph V) (k : ℕ) (hk : 2 ≤ k) (huni : IsKUniform H k)
    (e : Finset V) (he : e ∈ H) :
    ¬(∀ v ∈ e, greedyCol σ hσ H v = true) := by
  intro hall
  have hcard : e.card = k := huni e he
  have hne : e.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; rw [h, Finset.card_empty] at hcard; omega
  obtain ⟨v, hve, hvmax⟩ := e.exists_max_image σ hne
  have hpred : ∀ u ∈ e, σ u < σ v → greedyCol σ hσ H u = true :=
    fun u hu _ => hall u hu
  have hcond : ∃ e' ∈ H, v ∈ e' ∧ (∀ u ∈ e', σ u ≤ σ v) ∧
      (∀ u ∈ e', σ u < σ v → greedyCol σ hσ H u = true) :=
    ⟨e, he, hve, hvmax, hpred⟩
  have hfalse : greedyCol σ hσ H v = false := by
    rw [greedyCol_eq]; simp only [hcond, ite_true]
  exact absurd (hall v hve) (by rw [hfalse]; decide)

/-- **Structural lemma for random greedy coloring.** If an injective vertex ordering
$\sigma$ on a $k$-uniform hypergraph $H$ (with $k \geq 2$) has no conflicting pair, then
the greedy coloring induced by $\sigma$ witnesses that $H$ is 2-colorable. -/
theorem two_colorable_of_no_conflicting_pair
    (H : Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (huni : IsKUniform H k)
    (σ : V → ℕ) (hσ : Function.Injective σ)
    (hno_conflict : ¬HasConflictingPair H σ) :
    IsTwoColorable H := by
  classical
  use greedyCol σ hσ H
  intro e he hmono
  cases hmono with
  | inl hall_true =>
    exact greedyCol_no_all_true σ hσ H k hk huni e he hall_true
  | inr hall_false =>
    have hcard : e.card = k := huni e he
    have hne : e.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; rw [h, Finset.card_empty] at hcard; omega
    obtain ⟨w, hwe, hwmin⟩ := e.exists_min_image σ hne
    have hw_false : greedyCol σ hσ H w = false := hall_false w hwe
    rw [greedyCol_false_iff] at hw_false
    obtain ⟨e', he', hwe', hmax', hpred'⟩ := hw_false
    exfalso
    apply hno_conflict
    unfold HasConflictingPair
    refine ⟨e', he', e, he, w, ?_, ?_, ?_⟩
    · exact ⟨hwe', hmax'⟩
    · exact ⟨hwe, hwmin⟩
    · ext x
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · intro ⟨hxe', hxe⟩
        have h1 : σ x ≤ σ w := hmax' x hxe'
        have h2 : σ w ≤ σ x := hwmin x hxe
        exact hσ (le_antisymm h1 h2)
      · intro hxw
        subst hxw
        exact ⟨hwe', hwe⟩

end TwoColorableHypergraph
