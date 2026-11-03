/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Convex.Birkhoff

open Finset

namespace Matchings

structure BipartiteGraph (n : ℕ) where
  Adj : Fin n → Fin n → Prop
  [decAdj : DecidablePred (fun p : Fin n × Fin n => Adj p.1 p.2)]

attribute [instance] BipartiteGraph.decAdj

namespace BipartiteGraph

variable {n : ℕ} (G : BipartiteGraph n)

instance (u : Fin n) (v : Fin n) : Decidable (G.Adj u v) :=
  G.decAdj (u, v)

def leftNeighbors (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (G.Adj u)

def rightNeighbors (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => G.Adj u v)

def denseLeft : Prop :=
  ∀ u : Fin n, n ≤ 2 * (G.leftNeighbors u).card

def denseRight : Prop :=
  ∀ v : Fin n, n ≤ 2 * (G.rightNeighbors v).card

end BipartiteGraph

structure PartialMatching {n : ℕ} (G : BipartiteGraph n) where
  edges : Finset (Fin n × Fin n)
  edge_adj : ∀ p ∈ edges, G.Adj p.1 p.2
  left_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.1 = q.1 → p = q
  right_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.2 = q.2 → p = q

namespace PartialMatching

variable {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G)

def matchedLeft : Finset (Fin n) := M.edges.image Prod.fst

def matchedRight : Finset (Fin n) := M.edges.image Prod.snd

def unmatchedLeft : Finset (Fin n) := Finset.univ \ M.matchedLeft

def unmatchedRight : Finset (Fin n) := Finset.univ \ M.matchedRight

lemma fst_injOn_edges : Set.InjOn Prod.fst (↑M.edges : Set (Fin n × Fin n)) := by
  intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
  simp only [Finset.mem_coe] at h₁ h₂
  exact M.left_inj h₁ h₂ heq

lemma matchedLeft_card : M.matchedLeft.card = M.edges.card := by
  exact Finset.card_image_of_injOn M.fst_injOn_edges

end PartialMatching

def HasAugPath1 {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G) : Prop :=
  ∃ u v, u ∈ M.unmatchedLeft ∧ v ∈ M.unmatchedRight ∧ G.Adj u v

def HasAugPath3 {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G) : Prop :=
  ∃ u v u' v',
    u ∈ M.unmatchedLeft ∧ v ∈ M.unmatchedRight ∧
    (u', v') ∈ M.edges ∧ G.Adj u v' ∧ G.Adj u' v

def HasAugPathLE3 {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G) : Prop :=
  HasAugPath1 M ∨ HasAugPath3 M

theorem augmenting_path_of_min_degree {n : ℕ} {G : BipartiteGraph n}
    {M : PartialMatching G}
    (hLeft : G.denseLeft)
    (hRight : G.denseRight)
    (hu : M.unmatchedLeft.Nonempty)
    (hv : M.unmatchedRight.Nonempty) :
    HasAugPathLE3 M := by
  classical
  obtain ⟨u, hu_mem⟩ := hu
  obtain ⟨v, hv_mem⟩ := hv
  by_cases h1 : HasAugPath1 M
  · exact Or.inl h1
  · right
    simp only [HasAugPath1, not_exists, not_and] at h1

    let Nu : Finset (Fin n) := G.leftNeighbors u
    let Nv : Finset (Fin n) := G.rightNeighbors v

    have hNu_sub_matched : Nu ⊆ M.matchedRight := by
      intro w hw
      simp only [Nu, BipartiteGraph.leftNeighbors, Finset.mem_filter, Finset.mem_univ,
        true_and] at hw
      by_contra hc
      have hmem : w ∈ M.unmatchedRight := by
        simp only [PartialMatching.unmatchedRight, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact hc
      exact h1 u w hu_mem hmem hw

    have hNv_sub_matched : Nv ⊆ M.matchedLeft := by
      intro w hw
      simp only [Nv, BipartiteGraph.rightNeighbors, Finset.mem_filter, Finset.mem_univ,
        true_and] at hw
      by_contra hc
      have hmem : w ∈ M.unmatchedLeft := by
        simp only [PartialMatching.unmatchedLeft, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact hc
      exact h1 w v hmem hv_mem hw

    have hNu_card : n ≤ 2 * Nu.card := hLeft u
    have hNv_card : n ≤ 2 * Nv.card := hRight v

    have hM_lt : M.edges.card < n := by
      have hul : u ∈ Finset.univ \ M.matchedLeft := hu_mem
      rw [Finset.mem_sdiff] at hul
      have : M.matchedLeft ⊂ Finset.univ := by
        rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
        exact ⟨u, Finset.mem_univ u, hul.2⟩
      have hcard_lt : M.matchedLeft.card < (Finset.univ : Finset (Fin n)).card :=
        Finset.card_lt_card this
      simp only [Finset.card_univ, Fintype.card_fin] at hcard_lt
      linarith [M.matchedLeft_card]

    have matched_lt : M.matchedLeft.card < n := by
      rw [M.matchedLeft_card]; exact hM_lt

    let edgesNu := M.edges.filter (fun e => e.2 ∈ Nu)

    let leftOfNu := edgesNu.image Prod.fst

    have leftOfNu_sub : leftOfNu ⊆ M.matchedLeft := by
      intro x hx
      simp only [leftOfNu, Finset.mem_image] at hx
      obtain ⟨e, he, rfl⟩ := hx
      exact Finset.mem_image_of_mem _ (Finset.mem_of_mem_filter _ he)

    have edgesNu_snd_eq_Nu : edgesNu.image Prod.snd = Nu := by
      ext w
      simp only [edgesNu, Finset.mem_image, Finset.mem_filter, Prod.exists]
      constructor
      · rintro ⟨a, b, ⟨_, hb⟩, rfl⟩; exact hb
      · intro hw
        have : w ∈ M.matchedRight := hNu_sub_matched hw
        simp only [PartialMatching.matchedRight, Finset.mem_image, Prod.exists] at this
        obtain ⟨a, b, hmem, hbeq⟩ := this
        exact ⟨a, b, ⟨hbeq ▸ hmem, hbeq ▸ hw⟩, hbeq⟩
    have snd_inj_edgesNu : Set.InjOn Prod.snd (↑edgesNu : Set (Fin n × Fin n)) := by
      intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
      simp only [Finset.mem_coe, edgesNu, Finset.mem_filter] at h₁ h₂
      exact M.right_inj h₁.1 h₂.1 heq
    have fst_inj_edgesNu : Set.InjOn Prod.fst (↑edgesNu : Set (Fin n × Fin n)) := by
      intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
      simp only [Finset.mem_coe, edgesNu, Finset.mem_filter] at h₁ h₂
      exact M.left_inj h₁.1 h₂.1 heq
    have leftOfNu_card : leftOfNu.card = Nu.card := by
      have h1 : leftOfNu.card = edgesNu.card :=
        Finset.card_image_of_injOn fst_inj_edgesNu
      have h2 : Nu.card = edgesNu.card := by
        rw [← edgesNu_snd_eq_Nu]
        exact Finset.card_image_of_injOn snd_inj_edgesNu
      linarith


    have sum_ge : leftOfNu.card + Nv.card > M.matchedLeft.card := by
      have h1 : n ≤ 2 * leftOfNu.card := by rw [leftOfNu_card]; exact hNu_card
      have h2 : n ≤ 2 * Nv.card := hNv_card
      omega

    have inter_nonempty : (leftOfNu ∩ Nv).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have hdisj : Disjoint leftOfNu Nv := Finset.disjoint_iff_inter_eq_empty.mpr h
      have hunion_sub : leftOfNu ∪ Nv ⊆ M.matchedLeft :=
        Finset.union_subset leftOfNu_sub hNv_sub_matched
      have hcard_union : (leftOfNu ∪ Nv).card = leftOfNu.card + Nv.card :=
        Finset.card_union_of_disjoint hdisj
      have hle := Finset.card_le_card hunion_sub
      linarith

    obtain ⟨u_matched, hu_matched⟩ := inter_nonempty
    rw [Finset.mem_inter] at hu_matched
    obtain ⟨hu_left, hu_nv⟩ := hu_matched

    simp only [leftOfNu, Finset.mem_image] at hu_left
    obtain ⟨⟨u_m, v_m⟩, he_filter, hfst_eq⟩ := hu_left
    simp only [edgesNu, Finset.mem_filter] at he_filter
    obtain ⟨he_mem, hvm_Nu⟩ := he_filter

    simp only at hfst_eq
    subst hfst_eq

    simp only [Nu, BipartiteGraph.leftNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hvm_Nu

    simp only [Nv, BipartiteGraph.rightNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hu_nv

    exact ⟨u, v, u_m, v_m, hu_mem, hv_mem, he_mem, hvm_Nu, hu_nv⟩

open Real in
lemma geom_contraction_bound (r : ℝ) (hr_pos : 0 < r) (S : ℕ → ℕ)
    (hcontract : ∀ i, (S (i + 1) : ℝ) ≤ r * S i)
    (k : ℕ) : (S k : ℝ) ≤ r ^ k * S 0 := by
  induction k with
  | zero => simp
  | succ n ih =>
    calc (S (n + 1) : ℝ) ≤ r * S n := hcontract n
      _ ≤ r * (r ^ n * S 0) := mul_le_mul_of_nonneg_left ih (le_of_lt hr_pos)
      _ = r ^ (n + 1) * S 0 := by ring

open Real in
lemma pow_mul_lt_one_of_log_bound (N : ℕ) (hN : 0 < N) (r : ℝ) (hr_pos : 0 < r)
    (hr_lt : r < 1) (k : ℕ) (hk : (k : ℝ) > Real.log N / Real.log (1 / r)) :
    r ^ k * (N : ℝ) < 1 := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlog_inv_pos : 0 < Real.log (1 / r) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hr_pos), Real.log_one]
    linarith [Real.log_neg hr_pos hr_lt]
  have h1 : (k : ℝ) * Real.log (1 / r) > Real.log N := by
    have := mul_lt_mul_of_pos_right hk hlog_inv_pos
    rwa [div_mul_cancel₀ _ (ne_of_gt hlog_inv_pos)] at this
  have h2 : Real.log (r ^ k) < Real.log (1 / (N : ℝ)) := by
    rw [Real.log_pow, Real.log_div one_ne_zero (ne_of_gt hN_pos), Real.log_one]
    rw [Real.log_div one_ne_zero (ne_of_gt hr_pos), Real.log_one] at h1
    linarith
  have hrk_pos : (0 : ℝ) < r ^ k := pow_pos hr_pos k
  have h_inv_pos : (0 : ℝ) < 1 / (N : ℝ) := div_pos one_pos hN_pos
  have h3 : r ^ k < 1 / (N : ℝ) := (Real.log_lt_log_iff hrk_pos h_inv_pos).mp h2
  calc r ^ k * (N : ℝ) < 1 / (N : ℝ) * N := mul_lt_mul_of_pos_right h3 hN_pos
    _ = 1 := div_mul_cancel₀ 1 (ne_of_gt hN_pos)

open Real in
theorem matching_terminates_log_steps
    (N : ℕ) (d : ℕ) (β : ℝ)
    (hd_pos : 0 < d) (hβ_bound : β > d / 2) (hβ_lt_d : β < d)
    (S : ℕ → ℕ)
    (hS0 : S 0 ≤ N)
    (hcontract : ∀ i, (S (i + 1) : ℝ) ≤ 2 * (1 - β / d) * S i) :
    ∃ k : ℕ, k ≤ ⌈Real.log N / Real.log (1 / (2 * (1 - β / d)))⌉₊ + 1 ∧ S k = 0 := by
  set r := 2 * (1 - β / (↑d : ℝ)) with hr_def
  have hd_pos_real : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
  have hr_pos : 0 < r := by
    have hbd : β / (d : ℝ) < 1 := (div_lt_one hd_pos_real).mpr hβ_lt_d
    linarith
  have hr_lt : r < 1 := by
    have hbd : β / (d : ℝ) > 1 / 2 := by
      rw [gt_iff_lt, div_lt_div_iff₀ (by linarith : (0:ℝ) < 2) hd_pos_real]
      linarith
    linarith
  by_cases hN : N = 0
  · exact ⟨0, Nat.zero_le _, by omega⟩
  · have hN_pos : 0 < N := Nat.pos_of_ne_zero hN
    refine ⟨⌈Real.log N / Real.log (1 / r)⌉₊ + 1, le_refl _, ?_⟩
    have hk_gt : (↑(⌈Real.log ↑N / Real.log (1 / r)⌉₊ + 1) : ℝ) >
        Real.log ↑N / Real.log (1 / r) := by
      have h := Nat.le_ceil (Real.log ↑N / Real.log (1 / r))
      push_cast
      linarith
    have hpow_bound := pow_mul_lt_one_of_log_bound N hN_pos r hr_pos hr_lt _ hk_gt
    have hbound := geom_contraction_bound r hr_pos S hcontract
        (⌈Real.log ↑N / Real.log (1 / r)⌉₊ + 1)
    have hS0_le : (S 0 : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hS0
    have hSk_lt : (S (⌈Real.log ↑N / Real.log (1 / r)⌉₊ + 1) : ℝ) < 1 := by
      calc (S (⌈Real.log ↑N / Real.log (1 / r)⌉₊ + 1) : ℝ)
          ≤ r ^ (⌈Real.log ↑N / Real.log (1 / r)⌉₊ + 1) * S 0 := hbound
        _ ≤ r ^ (⌈Real.log ↑N / Real.log (1 / r)⌉₊ + 1) * N := by
            apply mul_le_mul_of_nonneg_left hS0_le
            exact le_of_lt (pow_pos hr_pos _)
        _ < 1 := hpow_bound
    have : S (⌈Real.log ↑N / Real.log (1 / r)⌉₊ + 1) < 1 := by exact_mod_cast hSk_lt
    omega

structure SizedMatching {n : ℕ} (G : BipartiteGraph n) (k : ℕ) where
  edges : Finset (Fin n × Fin n)
  edge_adj : ∀ p ∈ edges, G.Adj p.1 p.2
  left_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.1 = q.1 → p = q
  right_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.2 = q.2 → p = q
  card_eq : edges.card = k

instance sizedMatchingDecEq {n : ℕ} {G : BipartiteGraph n} {k : ℕ} :
    DecidableEq (SizedMatching G k) := by
  intro a b
  have h : a = b ↔ a.edges = b.edges := by
    constructor
    · intro h; subst h; rfl
    · intro h; cases a; cases b; simp only [SizedMatching.mk.injEq] at h ⊢; exact h
  rw [h]; exact inferInstance

noncomputable instance sizedMatchingFintype {n : ℕ} {G : BipartiteGraph n} {k : ℕ} :
    Fintype (SizedMatching G k) :=
  Fintype.ofInjective SizedMatching.edges (by
    intro a b h; cases a; cases b; simp only [SizedMatching.mk.injEq] at h ⊢; exact h)

def ChainVertex {n : ℕ} (G : BipartiteGraph n) : Type :=
  SizedMatching G n ⊕ SizedMatching G (n - 1)

noncomputable instance chainVertexFintype {n : ℕ} {G : BipartiteGraph n} :
    Fintype (ChainVertex G) :=
  inferInstanceAs (Fintype (SizedMatching G n ⊕ SizedMatching G (n - 1)))

instance chainVertexDecEq {n : ℕ} {G : BipartiteGraph n} :
    DecidableEq (ChainVertex G) :=
  inferInstanceAs (DecidableEq (SizedMatching G n ⊕ SizedMatching G (n - 1)))

abbrev PerfMatching {n : ℕ} (G : BipartiteGraph n) : Type := SizedMatching G n

structure Transition {n : ℕ} (G : BipartiteGraph n) where
  source : ChainVertex G
  target : ChainVertex G

def chainIsAdj {n : ℕ} {G : BipartiteGraph n} (v w : ChainVertex G) : Prop :=
  v = w ∨
  (match v, w with
   | Sum.inl M, Sum.inr M' => M'.edges ⊆ M.edges
   | Sum.inr M', Sum.inl M => M'.edges ⊆ M.edges
   | Sum.inr M₁, Sum.inr M₂ =>
       (M₁.edges \ M₂.edges).card = 1 ∧ (M₂.edges \ M₁.edges).card = 1
   | Sum.inl _, Sum.inl _ => False
  )

def matchingSymDiff {n : ℕ} {G : BipartiteGraph n}
    (s t : PerfMatching G) : Finset (Fin n × Fin n) :=
  (s.edges \ t.edges) ∪ (t.edges \ s.edges)

def chainVertexEdges {n : ℕ} {G : BipartiteGraph n} : ChainVertex G → Finset (Fin n × Fin n)
  | Sum.inl m => m.edges
  | Sum.inr m => m.edges

lemma encoding_source_recovery {α : Type*} [DecidableEq α] {s₁ s₂ P R : Finset α}
    (hP₁ : Disjoint P s₁) (hP₂ : Disjoint P s₂)
    (hR₁ : R ⊆ s₁) (hR₂ : R ⊆ s₂)
    (heq : (s₁ \ R) ∪ P = (s₂ \ R) ∪ P) :
    s₁ = s₂ := by
  ext x
  by_cases hxR : x ∈ R
  · exact ⟨fun _ => hR₂ hxR, fun _ => hR₁ hxR⟩
  · by_cases hxP : x ∈ P
    · exact ⟨fun hx => absurd hx (Finset.disjoint_left.mp hP₁ hxP),
             fun hx => absurd hx (Finset.disjoint_left.mp hP₂ hxP)⟩
    · constructor
      · intro hx
        have hmem : x ∈ (s₁ \ R) ∪ P :=
          Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxR⟩)
        rw [heq] at hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact (Finset.mem_sdiff.mp h).1
        · exact absurd h hxP
      · intro hx
        have hmem : x ∈ (s₂ \ R) ∪ P :=
          Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxR⟩)
        rw [← heq] at hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact (Finset.mem_sdiff.mp h).1
        · exact absurd h hxP

lemma symDiff_determines_target {n : ℕ} {G : BipartiteGraph n}
    {s t₁ t₂ : PerfMatching G}
    (hD : matchingSymDiff s t₁ = matchingSymDiff s t₂) :
    t₁ = t₂ := by
  have heq : t₁.edges = t₂.edges := by
    simp only [matchingSymDiff] at hD
    ext e
    by_cases hes : e ∈ s.edges
    · constructor
      · intro het₁
        by_contra het₂
        have : e ∈ (s.edges \ t₂.edges) ∪ (t₂.edges \ s.edges) :=
          Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hes, het₂⟩)
        rw [← hD] at this
        rcases Finset.mem_union.mp this with h | h
        · exact absurd het₁ (Finset.mem_sdiff.mp h).2
        · exact absurd hes (Finset.mem_sdiff.mp h).2
      · intro het₂
        by_contra het₁
        have : e ∈ (s.edges \ t₁.edges) ∪ (t₁.edges \ s.edges) :=
          Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hes, het₁⟩)
        rw [hD] at this
        rcases Finset.mem_union.mp this with h | h
        · exact absurd het₂ (Finset.mem_sdiff.mp h).2
        · exact absurd hes (Finset.mem_sdiff.mp h).2
    · constructor
      · intro het₁
        have : e ∈ (s.edges \ t₁.edges) ∪ (t₁.edges \ s.edges) :=
          Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨het₁, hes⟩)
        rw [hD] at this
        rcases Finset.mem_union.mp this with h | h
        · exact absurd (Finset.mem_sdiff.mp h).1 hes
        · exact (Finset.mem_sdiff.mp h).1
      · intro het₂
        have : e ∈ (s.edges \ t₂.edges) ∪ (t₂.edges \ s.edges) :=
          Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨het₂, hes⟩)
        rw [← hD] at this
        rcases Finset.mem_union.mp this with h | h
        · exact absurd (Finset.mem_sdiff.mp h).1 hes
        · exact (Finset.mem_sdiff.mp h).1
  cases t₁; cases t₂; simp only [SizedMatching.mk.injEq] at heq ⊢; exact heq

structure TypeBPathData {n : ℕ} {G : BipartiteGraph n} (T : Transition G)
    (s t : PerfMatching G) where
  removed : Finset (Fin n × Fin n)
  added : Finset (Fin n × Fin n)
  removed_sub : removed ⊆ s.edges
  added_disj : Disjoint added s.edges
  removed_sub_symDiff : removed ⊆ s.edges \ t.edges
  added_sub_symDiff : added ⊆ t.edges \ s.edges
  encodingVertex : ChainVertex G
  encoding_edges_eq : chainVertexEdges encodingVertex = (s.edges \ removed) ∪ added
  canonRemoved : Finset (Fin n × Fin n)
  removed_eq_canon : removed = canonRemoved
  canonAdded : Finset (Fin n × Fin n)
  added_eq_canon : added = canonAdded
  canon_removed_spec : canonRemoved = chainVertexEdges T.source \ chainVertexEdges encodingVertex
  canon_added_spec : canonAdded = chainVertexEdges encodingVertex \ chainVertexEdges T.source
  canonSymDiff : Finset (Fin n × Fin n)
  symDiff_eq_canon : matchingSymDiff s t = canonSymDiff
  canon_symDiff_spec : canonSymDiff =
    (s.edges \ chainVertexEdges encodingVertex) ∪ (chainVertexEdges encodingVertex \ s.edges)

def transitionEncoding {n : ℕ} {G : BipartiteGraph n} {T : Transition G}
    {s t : PerfMatching G} (data : TypeBPathData T s t) : ChainVertex G :=
  data.encodingVertex

def typeBUsesTransition {n : ℕ} {G : BipartiteGraph n}
    (T : Transition G) (s t : PerfMatching G) : Prop :=
  Nonempty (TypeBPathData T s t)

lemma encoding_determines_source_from_structure {n : ℕ} {G : BipartiteGraph n}
    {T : Transition G} {s₁ t₁ s₂ t₂ : PerfMatching G}
    (d₁ : TypeBPathData T s₁ t₁) (d₂ : TypeBPathData T s₂ t₂)
    (heq : d₁.encodingVertex = d₂.encodingVertex) :
    s₁ = s₂ := by

  have hR : d₁.removed = d₂.removed := by
    rw [d₁.removed_eq_canon, d₁.canon_removed_spec,
        d₂.removed_eq_canon, d₂.canon_removed_spec, heq]
  have hA : d₁.added = d₂.added := by
    rw [d₁.added_eq_canon, d₁.canon_added_spec,
        d₂.added_eq_canon, d₂.canon_added_spec, heq]

  have h₁ := d₁.encoding_edges_eq
  have h₂ := d₂.encoding_edges_eq
  rw [heq] at h₁


  rw [hR, hA] at h₁


  have heq_sets : (s₁.edges \ d₂.removed) ∪ d₂.added =
      (s₂.edges \ d₂.removed) ∪ d₂.added := by
    rw [← h₁, ← h₂]

  have hR_sub₁ : d₂.removed ⊆ s₁.edges := hR ▸ d₁.removed_sub
  have hA_disj₂ : Disjoint d₂.added s₂.edges := d₂.added_disj
  have hA_disj₁ : Disjoint d₂.added s₁.edges := hA ▸ d₁.added_disj
  have hedges : s₁.edges = s₂.edges :=
    encoding_source_recovery hA_disj₁ hA_disj₂ hR_sub₁ d₂.removed_sub heq_sets
  cases s₁; cases s₂; simp only [SizedMatching.mk.injEq] at hedges ⊢; exact hedges

lemma encoding_determines_symDiff_from_structure {n : ℕ} {G : BipartiteGraph n}
    {T : Transition G} {s₁ t₁ s₂ t₂ : PerfMatching G}
    (d₁ : TypeBPathData T s₁ t₁) (d₂ : TypeBPathData T s₂ t₂)
    (heq : d₁.encodingVertex = d₂.encodingVertex) :
    matchingSymDiff s₁ t₁ = matchingSymDiff s₂ t₂ := by

  have hs : s₁ = s₂ := encoding_determines_source_from_structure d₁ d₂ heq

  have hSD : d₁.canonSymDiff = d₂.canonSymDiff := by
    have hs_edges : s₁.edges = s₂.edges := by rw [hs]
    rw [d₁.canon_symDiff_spec, d₂.canon_symDiff_spec, hs_edges, heq]

  rw [d₁.symDiff_eq_canon, d₂.symDiff_eq_canon, hSD]

open Classical in
theorem transition_bound {n : ℕ} {G : BipartiteGraph n}
    (T : Transition G) (hT : chainIsAdj T.source T.target) :
    (Finset.univ.filter (fun p : PerfMatching G × PerfMatching G =>
      typeBUsesTransition T p.1 p.2)).card ≤ Fintype.card (ChainVertex G) := by
  classical

  let pathData : ∀ (s t : PerfMatching G), typeBUsesTransition T s t → TypeBPathData T s t :=
    fun s t h => Classical.choice h

  set pairs := Finset.univ.filter
    (fun p : PerfMatching G × PerfMatching G => typeBUsesTransition T p.1 p.2) with hpairs_def
  let σ : ↥pairs → ChainVertex G :=
    fun ⟨⟨s, t⟩, h⟩ =>
      transitionEncoding (pathData s t
        (by rw [hpairs_def] at h; exact (Finset.mem_filter.mp h).2))

  have hσ_inj : Function.Injective σ := by
    intro ⟨⟨s₁, t₁⟩, h₁⟩ ⟨⟨s₂, t₂⟩, h₂⟩ heq
    simp only [σ, transitionEncoding] at heq
    have h₁' : typeBUsesTransition T s₁ t₁ := by
      rw [hpairs_def] at h₁; exact (Finset.mem_filter.mp h₁).2
    have h₂' : typeBUsesTransition T s₂ t₂ := by
      rw [hpairs_def] at h₂; exact (Finset.mem_filter.mp h₂).2

    have hs : s₁ = s₂ := encoding_determines_source_from_structure
      (pathData s₁ t₁ h₁') (pathData s₂ t₂ h₂') heq

    have hD : matchingSymDiff s₁ t₁ = matchingSymDiff s₂ t₂ :=
      encoding_determines_symDiff_from_structure
        (pathData s₁ t₁ h₁') (pathData s₂ t₂ h₂') heq

    subst hs
    have ht : t₁ = t₂ := symDiff_determines_target hD
    subst ht
    rfl

  rw [← Fintype.card_coe]
  exact Fintype.card_le_of_injective σ hσ_inj

open Classical in

noncomputable def partner {n : ℕ} {G : BipartiteGraph n}
    (augment : SizedMatching G (n - 1) → PerfMatching G)
    (v : ChainVertex G) : PerfMatching G :=
  match v with
  | Sum.inl s => s
  | Sum.inr m => augment m

noncomputable def partnerPreimage {n : ℕ} {G : BipartiteGraph n}
    (augment : SizedMatching G (n - 1) → PerfMatching G)
    (s : PerfMatching G) : Finset (ChainVertex G) :=
  Finset.univ.filter (fun v => partner augment v = s)

inductive PartnerWitness (n : ℕ) where
  | self : PartnerWitness n
  | reduced : Fin n → PartnerWitness n
  | reducedRotated : Fin n → Fin n → PartnerWitness n

def partnerWitnessEquiv (n : ℕ) : PartnerWitness n ≃ (Unit ⊕ Fin n ⊕ (Fin n × Fin n)) where
  toFun := fun x => match x with
    | .self => Sum.inl ()
    | .reduced i => Sum.inr (Sum.inl i)
    | .reducedRotated i j => Sum.inr (Sum.inr (i, j))
  invFun := fun x => match x with
    | Sum.inl () => .self
    | Sum.inr (Sum.inl i) => .reduced i
    | Sum.inr (Sum.inr (i, j)) => .reducedRotated i j
  left_inv := fun x => by cases x <;> rfl
  right_inv := fun x => by
    rcases x with ⟨⟩ | (i | ⟨i, j⟩) <;> rfl

instance partnerWitnessFintype {n : ℕ} : Fintype (PartnerWitness n) :=
  Fintype.ofEquiv _ (partnerWitnessEquiv n).symm

theorem card_partnerWitness (n : ℕ) :
    Fintype.card (PartnerWitness n) = 1 + n + n * n := by
  rw [Fintype.card_congr (partnerWitnessEquiv n)]
  simp [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  omega

theorem partnerWitness_card_le (n : ℕ) :
    Fintype.card (PartnerWitness n) ≤ (n + 1) ^ 2 := by
  rw [card_partnerWitness]
  nlinarith





def HasConductanceLB {V : Type*} [Fintype V] [DecidableEq V]
    (cutEdges : Finset V → ℝ) (vol : Finset V → ℝ) (c : ℝ) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    cutEdges S / min (vol S) (vol (Finset.univ \ S)) ≥ c

def HasConductanceUB {V : Type*} [Fintype V] [DecidableEq V]
    (cutEdges : Finset V → ℝ) (vol : Finset V → ℝ) (c : ℝ) : Prop :=
  ∃ S : Finset V, S.Nonempty ∧ S ≠ Finset.univ ∧
    cutEdges S / min (vol S) (vol (Finset.univ \ S)) ≤ c

lemma canonical_paths_cut_bound (cutEdges_S vol_S S_card b d_max : ℝ)
    (hb_pos : 0 < b) (hd_pos : 0 < d_max)
    (hvol_pos : 0 < vol_S)
    (hcut : cutEdges_S ≥ S_card / (2 * b))
    (hvol : vol_S ≤ S_card * d_max) :
    cutEdges_S / vol_S ≥ 1 / (2 * b * d_max) := by
  rw [ge_iff_le, div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * b * d_max) hvol_pos]
  have h1 : S_card / (2 * b) * (2 * b * d_max) = S_card * d_max := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right hcut
    (le_of_lt (show (0:ℝ) < 2 * b * d_max from by positivity))]


noncomputable def chainDegree {n : ℕ} {G : BipartiteGraph n}
    (neighbors : ChainVertex G → Finset (ChainVertex G))
    (v : ChainVertex G) : ℕ :=
  (neighbors v).card

noncomputable def chainVol {n : ℕ} {G : BipartiteGraph n}
    (neighbors : ChainVertex G → Finset (ChainVertex G))
    (S : Finset (ChainVertex G)) : ℝ :=
  ∑ v ∈ S, (chainDegree neighbors v : ℝ)

noncomputable def chainCutEdges {n : ℕ} {G : BipartiteGraph n}
    (neighbors : ChainVertex G → Finset (ChainVertex G))
    (S : Finset (ChainVertex G)) : ℝ :=
  ∑ v ∈ S, ((neighbors v).filter (fun w => w ∉ S)).card

theorem matching_chain_conductance_bound {n : ℕ} (hn : 0 < n)
    {G : BipartiteGraph n}

    (cutEdges vol : Finset (ChainVertex G) → ℝ)

    (hvol_pos : ∀ S : Finset (ChainVertex G), S.Nonempty → 0 < vol S)


    (hmax_degree : ∀ S : Finset (ChainVertex G),
      vol S ≤ (S.card : ℝ) * (n : ℝ) ^ 2)


    (hcongestion : ∀ S : Finset (ChainVertex G), S.Nonempty → S ≠ Finset.univ →
      cutEdges S ≥ (S.card : ℝ) / (2 * ((n : ℝ) + 1) ^ 4)) :
    HasConductanceLB cutEdges vol (1 / (2 * ((n : ℝ) + 1) ^ 4 * (n : ℝ) ^ 2)) := by
  intro S hS_ne hS_univ
  have hvS_pos := hvol_pos S hS_ne
  have hSc_ne : (Finset.univ \ S).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro h
    exact hS_univ (Finset.eq_univ_iff_forall.mpr (fun x => h (Finset.mem_univ x)))
  have hvSc_pos := hvol_pos (Finset.univ \ S) hSc_ne
  have hmin_pos : (0 : ℝ) < min (vol S) (vol (Finset.univ \ S)) := lt_min hvS_pos hvSc_pos
  have hmin_bound : min (vol S) (vol (Finset.univ \ S)) ≤ (S.card : ℝ) * (n : ℝ) ^ 2 :=
    le_trans (min_le_left _ _) (hmax_degree S)
  exact canonical_paths_cut_bound (cutEdges S) (min (vol S) (vol (Finset.univ \ S)))
    (S.card : ℝ) (((n : ℝ) + 1) ^ 4) ((n : ℝ) ^ 2)
    (by positivity) (by positivity) hmin_pos (hcongestion S hS_ne hS_univ) hmin_bound

theorem matching_chain_conductance_concrete {n : ℕ} (hn : 0 < n)
    {G : BipartiteGraph n}

    (neighbors : ChainVertex G → Finset (ChainVertex G))


    (hmin_deg : ∀ v : ChainVertex G, 0 < (neighbors v).card)


    (hmax_deg : ∀ v : ChainVertex G, (neighbors v).card ≤ n ^ 2)


    (hcongestion : ∀ S : Finset (ChainVertex G), S.Nonempty → S ≠ Finset.univ →
      chainCutEdges neighbors S ≥ (S.card : ℝ) / (2 * ((n : ℝ) + 1) ^ 4)) :
    HasConductanceLB (chainCutEdges neighbors) (chainVol neighbors)
      (1 / (2 * ((n : ℝ) + 1) ^ 4 * (n : ℝ) ^ 2)) := by

  have hvol_bound : ∀ S : Finset (ChainVertex G),
      chainVol neighbors S ≤ (S.card : ℝ) * (n : ℝ) ^ 2 := by
    intro S
    simp only [chainVol, chainDegree]
    calc (∑ v ∈ S, ((neighbors v).card : ℝ))
        ≤ ∑ _ ∈ S, ((n : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro v _
          exact_mod_cast hmax_deg v
      _ = (S.card : ℝ) * (n : ℝ) ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]

  have hvol_pos : ∀ S : Finset (ChainVertex G), S.Nonempty → 0 < chainVol neighbors S := by
    intro S hS_ne
    simp only [chainVol, chainDegree]
    apply Finset.sum_pos
    · intro v _
      exact Nat.cast_pos.mpr (hmin_deg v)
    · exact hS_ne
  exact matching_chain_conductance_bound hn _ _ hvol_pos hvol_bound hcongestion

theorem matching_chain_conductance_theta {n : ℕ} (hn : 0 < n)
    {G : BipartiteGraph n}

    (neighbors : ChainVertex G → Finset (ChainVertex G))


    (hmin_deg : ∀ v : ChainVertex G, 0 < (neighbors v).card)


    (hmax_deg : ∀ v : ChainVertex G, (neighbors v).card ≤ n ^ 2)


    (hcongestion : ∀ S : Finset (ChainVertex G), S.Nonempty → S ≠ Finset.univ →
      chainCutEdges neighbors S ≥ (S.card : ℝ) / (2 * ((n : ℝ) + 1) ^ 4)) :
    HasConductanceLB (chainCutEdges neighbors) (chainVol neighbors)
      (1 / (2 * ((n : ℝ) + 1) ^ 6)) := by
  have hbase := matching_chain_conductance_concrete hn neighbors hmin_deg hmax_deg hcongestion
  intro S hS_ne hS_univ
  have hge := hbase S hS_ne hS_univ
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg' n
  have hn_le : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hle : 1 / (2 * ((n : ℝ) + 1) ^ 6) ≤ 1 / (2 * ((n : ℝ) + 1) ^ 4 * (n : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1) (by positivity)
    have h4pos : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hn_le h4pos]
  linarith


theorem chain_congestion_bound {n : ℕ} (_hn : 0 < n)
    {G : BipartiteGraph n}
    (neighbors : ChainVertex G → Finset (ChainVertex G))
    (_hmin_deg : ∀ v : ChainVertex G, 0 < (neighbors v).card)
    (_hmax_deg : ∀ v : ChainVertex G, (neighbors v).card ≤ n ^ 2)


    (hpaths : ∀ S : Finset (ChainVertex G), S.Nonempty → S ≠ Finset.univ →
      (S.card : ℝ) * ((Finset.univ \ S).card : ℝ) ≤
        chainCutEdges neighbors S * ((n : ℝ) + 1) ^ 4) :
    ∀ S : Finset (ChainVertex G), S.Nonempty → S ≠ Finset.univ →
      chainCutEdges neighbors S ≥ (S.card : ℝ) / (2 * ((n : ℝ) + 1) ^ 4) := by
  intro S hS_ne hS_univ
  have hn1_pos : (0 : ℝ) < ((n : ℝ) + 1) ^ 4 := by positivity
  have hSc_ne : (Finset.univ \ S).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro h
    exact hS_univ (Finset.eq_univ_iff_forall.mpr (fun x => h (Finset.mem_univ x)))
  have hSc_card_pos : 0 < (Finset.univ \ S).card := Finset.Nonempty.card_pos hSc_ne
  have hSc_ge_one : (1 : ℝ) ≤ ((Finset.univ \ S).card : ℝ) := by exact_mod_cast hSc_card_pos
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS_ne.card_pos
  have hpaths_S := hpaths S hS_ne hS_univ
  have h1 : (S.card : ℝ) * 1 ≤ (S.card : ℝ) * ((Finset.univ \ S).card : ℝ) :=
    mul_le_mul_of_nonneg_left hSc_ge_one (le_of_lt hS_pos)
  have h2 : (S.card : ℝ) ≤ chainCutEdges neighbors S * ((n : ℝ) + 1) ^ 4 := by linarith
  have h3 : (S.card : ℝ) / ((n : ℝ) + 1) ^ 4 ≤ chainCutEdges neighbors S := by
    rw [div_le_iff₀ hn1_pos]
    linarith
  have h4 : (S.card : ℝ) / (2 * ((n : ℝ) + 1) ^ 4) ≤
      (S.card : ℝ) / ((n : ℝ) + 1) ^ 4 := by
    apply div_le_div_of_nonneg_left (by linarith : (0 : ℝ) ≤ (S.card : ℝ)) (by positivity)
    linarith
  linarith


theorem chain_canonical_paths_crossing {n : ℕ} (hn : 0 < n)
    {G : BipartiteGraph n}
    (neighbors : ChainVertex G → Finset (ChainVertex G))
    (hmin_deg : ∀ v : ChainVertex G, 0 < (neighbors v).card)
    (hmax_deg : ∀ v : ChainVertex G, (neighbors v).card ≤ n ^ 2)


    (path_assign : Finset (ChainVertex G) →
      ChainVertex G → ChainVertex G → ChainVertex G × ChainVertex G)
    (hassign_valid : ∀ S : Finset (ChainVertex G), S.Nonempty → S ≠ Finset.univ →
      ∀ s ∈ S, ∀ t ∈ Finset.univ \ S,
        (path_assign S s t).1 ∈ S ∧
        (path_assign S s t).2 ∈ (neighbors (path_assign S s t).1).filter (· ∉ S))


    (hassign_bound : ∀ S : Finset (ChainVertex G), S.Nonempty → S ≠ Finset.univ →
      ∀ v ∈ S, ∀ w ∈ (neighbors v).filter (fun x => x ∉ S),
        ((S ×ˢ (Finset.univ \ S)).filter
          (fun p => path_assign S p.1 p.2 = (v, w))).card ≤ (n + 1) ^ 4) :
    ∀ S : Finset (ChainVertex G), S.Nonempty → S ≠ Finset.univ →
      (S.card : ℝ) * ((Finset.univ \ S).card : ℝ) ≤
        chainCutEdges neighbors S * ((n : ℝ) + 1) ^ 4 := by
  intro S hS_ne hS_univ

  suffices h : S.card * (Finset.univ \ S).card ≤
      (∑ v ∈ S, ((neighbors v).filter (fun w => w ∉ S)).card) * (n + 1) ^ 4 by
    simp only [chainCutEdges]
    exact_mod_cast h

  classical
  set pairs := S ×ˢ (Finset.univ \ S)
  set crossEdges := S.biUnion
    (fun v => ((neighbors v).filter (fun w => w ∉ S)).image (fun w => (v, w)))
  have hpairs_card : pairs.card = S.card * (Finset.univ \ S).card :=
    Finset.card_product S (Finset.univ \ S)

  have himage_sub : Set.MapsTo (fun p : ChainVertex G × ChainVertex G =>
      path_assign S p.1 p.2) ↑pairs ↑crossEdges := by
    intro ⟨s, t⟩ hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    have hv := hassign_valid S hS_ne hS_univ s hp.1 t hp.2
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨(path_assign S s t).1, hv.1,
      Finset.mem_image.mpr ⟨(path_assign S s t).2, hv.2, rfl⟩⟩

  have hfib : pairs.card =
      ∑ e ∈ crossEdges, (pairs.filter (fun p => path_assign S p.1 p.2 = e)).card :=
    Finset.card_eq_sum_card_fiberwise himage_sub

  have hfiber_bound : ∀ e ∈ crossEdges,
      (pairs.filter (fun p => path_assign S p.1 p.2 = e)).card ≤ (n + 1) ^ 4 := by
    intro ⟨v, w⟩ hevw
    rw [Finset.mem_biUnion] at hevw
    obtain ⟨v', hv'S, hvw_mem⟩ := hevw
    rw [Finset.mem_image] at hvw_mem
    obtain ⟨w', hw'mem, hvw_eq⟩ := hvw_mem
    have hveq : v = v' := (Prod.mk.inj hvw_eq).1.symm
    have hweq : w = w' := (Prod.mk.inj hvw_eq).2.symm
    subst hveq; subst hweq
    exact hassign_bound S hS_ne hS_univ v hv'S w hw'mem

  have hsum_le : ∑ e ∈ crossEdges,
      (pairs.filter (fun p => path_assign S p.1 p.2 = e)).card ≤
      crossEdges.card * (n + 1) ^ 4 :=
    calc ∑ e ∈ crossEdges, (pairs.filter (fun p => path_assign S p.1 p.2 = e)).card
        ≤ ∑ _e ∈ crossEdges, (n + 1) ^ 4 :=
          Finset.sum_le_sum (fun e he => hfiber_bound e he)
      _ = crossEdges.card * (n + 1) ^ 4 := by simp [Finset.sum_const]

  have hcross_card : crossEdges.card ≤
      ∑ v ∈ S, ((neighbors v).filter (fun w => w ∉ S)).card :=
    calc crossEdges.card
        ≤ ∑ v ∈ S, (((neighbors v).filter (fun w => w ∉ S)).image
            (fun w => (v, w))).card := Finset.card_biUnion_le
      _ ≤ ∑ v ∈ S, ((neighbors v).filter (fun w => w ∉ S)).card :=
          Finset.sum_le_sum (fun v _ => Finset.card_image_le)

  rw [← hpairs_card]
  calc pairs.card
      = ∑ e ∈ crossEdges,
          (pairs.filter (fun p => path_assign S p.1 p.2 = e)).card := hfib
    _ ≤ crossEdges.card * (n + 1) ^ 4 := hsum_le
    _ ≤ (∑ v ∈ S, ((neighbors v).filter (fun w => w ∉ S)).card) * (n + 1) ^ 4 :=
        Nat.mul_le_mul_right _ hcross_card



open Matrix in

open Matrix in

open Matrix in

def permanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, A i (σ i)

end Matchings
