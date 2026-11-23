/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14

open Finset Real

noncomputable section

namespace SparseVarshamovGilbert

/-- Support of a binary vector: the finset of coordinates where `x i = true`. -/
def boolSupport {d : ℕ} (x : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter (fun i => x i = true)

/-- Modify `x` by clearing the bits indexed by `J` and setting those indexed
by `K`, leaving the rest unchanged. Used to step between nearby sparse vectors. -/
def flipVec {d : ℕ} (x : Fin d → Bool) (J K : Finset (Fin d)) : Fin d → Bool :=
  fun i => if i ∈ J then false else if i ∈ K then true else x i

/-- A `SparseVec d k` has exactly `k` set bits, i.e. its support has size `k`. -/
lemma boolSupport_card {d k : ℕ} (x : SparseVec d k) :
    (boolSupport x.val).card = k := x.property

/-- The complement of a `k`-support inside `Fin d` has size `d - k`. -/
lemma compl_boolSupport_card {d k : ℕ} (hkd : k ≤ d) (x : SparseVec d k) :
    (Finset.univ \ boolSupport x.val).card = d - k := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (boolSupport x.val))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [boolSupport_card] at h; omega

/-- If `J ⊆ supp(x)` and `K ⊆ supp(x)ᶜ`, then `J` and `K` are disjoint. -/
lemma disjoint_of_support_subsets {d : ℕ} {x : Fin d → Bool}
    {J K : Finset (Fin d)}
    (hJ : J ⊆ boolSupport x) (hK : K ⊆ Finset.univ \ boolSupport x) :
    Disjoint J K :=
  Finset.disjoint_of_subset_left hJ
    (Finset.disjoint_of_subset_right hK disjoint_sdiff_self_right)

/-- Support formula for `flipVec`: `supp(flip(x, J, K)) = (supp(x) \ J) ∪ K`
when `J` and `K` are disjoint. -/
lemma boolSupport_flipVec {d : ℕ} (x : Fin d → Bool) (J K : Finset (Fin d))
    (hDisj : Disjoint J K) :
    boolSupport (flipVec x J K) = (boolSupport x \ J) ∪ K := by
  ext i
  simp only [boolSupport, Finset.mem_filter, Finset.mem_univ, true_and, flipVec,
             Finset.mem_union, Finset.mem_sdiff]
  split_ifs with h1 h2
  · constructor
    · simp
    · exact fun h => h.elim (fun ⟨_, a⟩ => absurd h1 a)
        (fun hk => absurd hk (Finset.disjoint_left.mp hDisj h1))
  · exact ⟨fun _ => Or.inr h2, fun _ => rfl⟩
  · exact ⟨fun hxt => Or.inl ⟨hxt, h1⟩, fun h => h.elim (·.1) (absurd · h2)⟩

/-- Flipping the same number of bits on and off preserves the `ℓ⁰` weight. -/
lemma flipVec_preserves_l0norm {d : ℕ} (x : Fin d → Bool) (J K : Finset (Fin d))
    (hJ : J ⊆ boolSupport x) (hK : K ⊆ Finset.univ \ boolSupport x)
    (hJK : J.card = K.card) :
    l0norm (flipVec x J K) = l0norm x := by
  unfold l0norm
  show (boolSupport (flipVec x J K)).card = (boolSupport x).card
  rw [boolSupport_flipVec x J K (disjoint_of_support_subsets hJ hK)]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left Finset.sdiff_subset
    (Finset.disjoint_of_subset_right hK disjoint_sdiff_self_right))]
  have := Finset.card_sdiff_add_card_eq_card hJ; omega

/-- Disagreement set between `x` and `flipVec x J K` equals `J ∪ K`. -/
lemma disagree_eq_union {d : ℕ} (x : Fin d → Bool) (J K : Finset (Fin d))
    (hJ : J ⊆ boolSupport x) (hK : K ⊆ Finset.univ \ boolSupport x) :
    (Finset.univ.filter fun i => x i ≠ flipVec x J K i) = J ∪ K := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, flipVec, Finset.mem_union]
  split_ifs with h1 h2
  ·
    have hxi : x i = true := by
      have := hJ h1; simp only [boolSupport, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    simp [hxi, h1]
  ·
    have hxi : x i = false := by
      have h := hK h2
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, boolSupport,
                  Finset.mem_filter] at h
      exact Bool.eq_false_iff.mpr h
    simp [hxi, h1, h2]
  · simp [h1, h2]

/-- Hamming distance between `x` and `flipVec x J K` equals `|J| + |K|`. -/
lemma hammingDist_of_flipVec {d : ℕ} (x : Fin d → Bool) (J K : Finset (Fin d))
    (hJ : J ⊆ boolSupport x) (hK : K ⊆ Finset.univ \ boolSupport x)
    (hDisj : Disjoint J K) :
    hammingDist x (flipVec x J K) = J.card + K.card := by
  unfold hammingDist
  rw [disagree_eq_union x J K hJ hK, Finset.card_union_of_disjoint hDisj]

/-- Reconstruction: applying `flipVec` with the right choice of `J` and `K`
recovers any `y` from `x`. -/
lemma flipVec_reconstructs {d : ℕ} (x y : Fin d → Bool) :
    flipVec x (boolSupport x \ boolSupport y) (boolSupport y \ boolSupport x) = y := by
  ext i
  simp only [flipVec, boolSupport, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hxi : x i = true <;> by_cases hyi : y i = true <;> simp [hxi, hyi]

/-- Two equal-weight binary vectors have equal-size symmetric difference
components: `|supp(x) \ supp(y)| = |supp(y) \ supp(x)|`. -/
lemma sdiff_boolSupport_card_eq {d k : ℕ} (x y : Fin d → Bool)
    (hx : l0norm x = k) (hy : l0norm y = k) :
    (boolSupport x \ boolSupport y).card = (boolSupport y \ boolSupport x).card :=
  Finset.card_sdiff_eq_card_sdiff_iff.mpr (by unfold boolSupport l0norm at *; omega)

/-- For binary vectors of equal weight `k`, the Hamming distance equals
`2 · |supp(x) \ supp(y)|`. -/
lemma hammingDist_eq_two_mul_sdiff {d k : ℕ} (x y : Fin d → Bool)
    (hx : l0norm x = k) (hy : l0norm y = k) :
    hammingDist x y = 2 * (boolSupport x \ boolSupport y).card := by
  unfold hammingDist
  have hdis : (Finset.univ.filter fun i => x i ≠ y i) =
      (boolSupport x \ boolSupport y) ∪ (boolSupport y \ boolSupport x) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff,
               boolSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    cases (x i) <;> cases (y i) <;> simp
  rw [hdis, Finset.card_union_of_disjoint disjoint_sdiff_sdiff,
      sdiff_boolSupport_card_eq x y hx hy]
  omega

end SparseVarshamovGilbert

end
