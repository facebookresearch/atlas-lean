/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Finset Nat

set_option maxHeartbeats 400000

namespace TetrahedronFreeHypergraph

variable {n : ℕ}

/-- For a fixed $3$-element set $e \subseteq \mathrm{Fin}\,n$, the number of
$5$-element supersets of $e$ equals $\binom{n-3}{2}$, since one chooses the $2$
additional vertices from the remaining $n-3$. -/
lemma card_five_supersets (e : Finset (Fin n)) (he : e.card = 3) :
    ((powersetCard 5 (univ : Finset (Fin n))).filter (fun S => e ⊆ S)).card =
      (n - 3).choose 2 := by
  have he_sub : e ⊆ (univ : Finset (Fin n)) := subset_univ e
  have hcompl_card : (univ \ e : Finset (Fin n)).card = n - 3 := by
    rw [Finset.card_sdiff_of_subset he_sub, Finset.card_univ, Fintype.card_fin, he]
  rw [← hcompl_card, ← card_powersetCard]
  apply Finset.card_bij (fun S _hS => S \ e)
  · intro S hS
    rw [mem_filter, mem_powersetCard] at hS
    obtain ⟨⟨_, hScard⟩, heS⟩ := hS
    rw [mem_powersetCard]
    exact ⟨sdiff_subset_sdiff (subset_univ S) (Subset.refl e),
      by rw [card_sdiff_of_subset heS]; omega⟩
  · intro S₁ hS₁ S₂ hS₂ h
    rw [mem_filter, mem_powersetCard] at hS₁ hS₂
    ext x
    constructor
    · intro hx
      by_cases hxe : x ∈ e
      · exact hS₂.2 hxe
      · exact (mem_sdiff.mp (h ▸ (mem_sdiff.mpr ⟨hx, hxe⟩))).1
    · intro hx
      by_cases hxe : x ∈ e
      · exact hS₁.2 hxe
      · have hmem : x ∈ S₂ \ e := mem_sdiff.mpr ⟨hx, hxe⟩
        rw [← h] at hmem
        exact (mem_sdiff.mp hmem).1
  · intro T hT
    rw [mem_powersetCard] at hT
    have hTe : Disjoint T e := disjoint_of_subset_left hT.1 disjoint_sdiff_self_left
    refine ⟨T ∪ e, ?_, Finset.union_sdiff_cancel_right hTe⟩
    rw [mem_filter, mem_powersetCard]
    exact ⟨⟨union_subset (hT.1.trans (sdiff_subset.trans (subset_univ _))) (subset_univ e),
      by rw [card_union_of_disjoint hTe, hT.2, he]⟩, subset_union_right⟩

/-- Inside a $5$-element set $S$, a fixed $3$-element subset $e \subseteq S$ is contained
in exactly $2$ of the $4$-element subsets of $S$ (corresponding to the $2$ elements of
$S \setminus e$ one can adjoin to form a $4$-set). -/
lemma card_four_in_five (S : Finset (Fin n)) (hS : S.card = 5)
    (e : Finset (Fin n)) (he : e.card = 3) (heS : e ⊆ S) :
    ((S.powersetCard 4).filter (fun T => e ⊆ T)).card = 2 := by
  have h_sdiff : (S \ e).card = 2 := by rw [card_sdiff_of_subset heS, hS, he]
  rw [← h_sdiff]
  symm
  apply Finset.card_bij (fun v _hv => S \ {v})
  · intro v hv
    have hvS : v ∈ S := (mem_sdiff.mp hv).1
    have hve : v ∉ e := (mem_sdiff.mp hv).2
    rw [mem_filter, mem_powersetCard]
    refine ⟨⟨sdiff_subset, by rw [card_sdiff_of_subset (singleton_subset_iff.mpr hvS),
      hS, card_singleton]⟩, ?_⟩
    intro x hxe
    exact mem_sdiff.mpr ⟨heS hxe, fun h => hve (mem_singleton.mp h ▸ hxe)⟩
  · intro v₁ hv₁ _ _ h
    have hv₁_not : v₁ ∉ S \ {v₁} := by simp
    rw [h] at hv₁_not
    simp only [mem_sdiff, mem_singleton, not_and, not_not] at hv₁_not
    exact hv₁_not (mem_sdiff.mp hv₁).1
  · intro T hT
    rw [mem_filter, mem_powersetCard] at hT
    obtain ⟨⟨hTS, hTcard⟩, heT⟩ := hT
    have h1 : (S \ T).card = 1 := by rw [card_sdiff_of_subset hTS, hS, hTcard]
    obtain ⟨v, hv_eq⟩ := card_eq_one.mp h1
    have hv_mem : v ∈ S \ T := hv_eq ▸ mem_singleton_self v
    have hvS : v ∈ S := (mem_sdiff.mp hv_mem).1
    have hvT : v ∉ T := (mem_sdiff.mp hv_mem).2
    have hve : v ∉ e := fun hve => hvT (heT hve)
    refine ⟨v, mem_sdiff.mpr ⟨hvS, hve⟩, ?_⟩
    ext x
    simp only [mem_sdiff, mem_singleton]
    constructor
    · intro ⟨hxS, hxv⟩
      by_contra hxT
      have hmem : x ∈ S \ T := mem_sdiff.mpr ⟨hxS, hxT⟩
      rw [hv_eq] at hmem
      exact hxv (mem_singleton.mp hmem)
    · intro hxT
      exact ⟨hTS hxT, fun hxv => hvT (hxv ▸ hxT)⟩

/-- **Lemma 2.4.3.** Any $5$-vertex tetrahedron-free $3$-uniform hypergraph has at most
$7$ hyperedges. Equivalently, for every $5$-set $S$ at most $7$ hyperedges of $E$ lie
inside $S$. Proved by double counting pairs (hyperedge, $4$-superset). -/
lemma five_set_edges_le_seven
    (E : Finset (Finset (Fin n)))
    (hUnif : ∀ e ∈ E, e.card = 3)
    (hFree : ∀ S ∈ powersetCard 4 (univ : Finset (Fin n)),
      ((S.powersetCard 3).filter (· ∈ E)).card ≤ 3)
    (S : Finset (Fin n))
    (hS : S ∈ powersetCard 5 (univ : Finset (Fin n))) :
    (E.filter (· ⊆ S)).card ≤ 7 := by
  classical
  have hScard : S.card = 5 := (mem_powersetCard.mp hS).2
  have hSuniv : S ⊆ univ := (mem_powersetCard.mp hS).1
  set edgesInS := E.filter (· ⊆ S)
  set fourSetsOfS := S.powersetCard 4
  have dc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun (e : Finset (Fin n)) (T : Finset (Fin n)) => e ⊆ T)
    (s := edgesInS) (t := fourSetsOfS)
  have lhs_eq : ∑ e ∈ edgesInS, (fourSetsOfS.bipartiteAbove (· ⊆ ·) e).card =
      edgesInS.card * 2 := by
    apply Finset.sum_eq_card_nsmul
    intro e he
    simp only [Finset.bipartiteAbove, fourSetsOfS]
    exact card_four_in_five S hScard e (hUnif e (mem_filter.mp he).1) (mem_filter.mp he).2
  have rhs_le : ∑ T ∈ fourSetsOfS, (edgesInS.bipartiteBelow (· ⊆ ·) T).card ≤ 15 := by
    calc ∑ T ∈ fourSetsOfS, (edgesInS.bipartiteBelow (· ⊆ ·) T).card
        ≤ fourSetsOfS.card * 3 := by
          apply Finset.sum_le_card_nsmul
          intro T hT
          simp only [Finset.bipartiteBelow]
          have hsub : edgesInS.filter (· ⊆ T) ⊆ E.filter (· ⊆ T) := by
            intro e he
            rw [mem_filter] at he ⊢
            exact ⟨(mem_filter.mp he.1).1, he.2⟩
          have hTuniv : T ∈ powersetCard 4 (univ : Finset (Fin n)) :=
            mem_powersetCard.mpr ⟨(mem_powersetCard.mp hT).1.trans hSuniv,
              (mem_powersetCard.mp hT).2⟩
          have hTeq : E.filter (· ⊆ T) = (T.powersetCard 3).filter (· ∈ E) := by
            ext e
            simp only [mem_filter, mem_powersetCard]
            exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h2, hUnif e h1⟩, h1⟩,
              fun ⟨⟨h1, _⟩, h2⟩ => ⟨h2, h1⟩⟩
          calc (edgesInS.filter (· ⊆ T)).card
              ≤ (E.filter (· ⊆ T)).card := card_le_card hsub
            _ = ((T.powersetCard 3).filter (· ∈ E)).card := by rw [hTeq]
            _ ≤ 3 := hFree T hTuniv
      _ = 15 := by
          simp only [fourSetsOfS, card_powersetCard, hScard]
          norm_num
  have h2 : edgesInS.card * 2 ≤ 15 := by linarith [lhs_eq, dc, rhs_le]
  omega

/-- **Improved sampling bound (Proposition 2.4.4).** A tetrahedron-free $3$-uniform
hypergraph on $n \geq 5$ vertices has at most $\tfrac{7}{10}\binom{n}{3}$ hyperedges;
equivalently $10 |E| \leq 7 \binom{n}{3}$. The proof samples random $5$-sets and applies
Lemma 2.4.3. -/
theorem improved_sampling_bound (hn : 5 ≤ n) (E : Finset (Finset (Fin n)))
    (hUnif : ∀ e ∈ E, e.card = 3)
    (hFree : ∀ S ∈ powersetCard 4 (univ : Finset (Fin n)),
      ((S.powersetCard 3).filter (· ∈ E)).card ≤ 3) :
    10 * E.card ≤ 7 * n.choose 3 := by
  classical
  set fiveSets := powersetCard 5 (univ : Finset (Fin n))
  have dc_eq : (∑ e ∈ E, (fiveSets.bipartiteAbove (· ⊆ ·) e).card) =
      ∑ S ∈ fiveSets, (E.bipartiteBelow (· ⊆ ·) S).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (· ⊆ ·)
  have lhs_eq : ∑ e ∈ E, (fiveSets.bipartiteAbove (· ⊆ ·) e).card =
      E.card * (n - 3).choose 2 := by
    apply Finset.sum_eq_card_nsmul
    intro e he
    simp only [Finset.bipartiteAbove, fiveSets]
    exact card_five_supersets e (hUnif e he)
  have rhs_le : ∑ S ∈ fiveSets, (E.bipartiteBelow (· ⊆ ·) S).card ≤ fiveSets.card * 7 := by
    apply Finset.sum_le_card_nsmul
    intro S hS
    simp only [Finset.bipartiteBelow]
    exact five_set_edges_le_seven E hUnif hFree S hS
  have fiveSets_card : fiveSets.card = n.choose 5 := by
    simp only [fiveSets, card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have h1 : E.card * (n - 3).choose 2 ≤ n.choose 5 * 7 := by
    calc E.card * (n - 3).choose 2
        = ∑ e ∈ E, (fiveSets.bipartiteAbove (· ⊆ ·) e).card := lhs_eq.symm
      _ = ∑ S ∈ fiveSets, (E.bipartiteBelow (· ⊆ ·) S).card := dc_eq
      _ ≤ fiveSets.card * 7 := rhs_le
      _ = n.choose 5 * 7 := by rw [fiveSets_card]
  have hid : n.choose 5 * 10 = n.choose 3 * (n - 3).choose 2 := by
    have h45 : n.choose 5 * 5 = n.choose 4 * (n - 4) := by
      have := Nat.choose_succ_right_eq n 4
      linarith
    have h34 : n.choose 4 * 4 = n.choose 3 * (n - 3) := Nat.choose_succ_right_eq n 3
    have h_n3_2 : (n - 3).choose 2 * 2 = (n - 3) * (n - 4) := by
      have h1 := Nat.choose_succ_right_eq (n - 3) 1
      simp only [Nat.choose_one_right] at h1
      omega
    nlinarith
  have hpos : 0 < (n - 3).choose 2 := Nat.choose_pos (by omega : 2 ≤ n - 3)
  nlinarith

end TetrahedronFreeHypergraph
