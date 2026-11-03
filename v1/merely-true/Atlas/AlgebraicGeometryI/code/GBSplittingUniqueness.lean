/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.GBSplittingExistence
import Mathlib.Data.Multiset.Basic

open BigOperators

namespace GBUniqueness

/-- Sum of `h^0` dimensions across a multiset of twist degrees: for a multiset `s` of integers,
returns `∑_{d ∈ s} max(d + m + 1, 0)`, modeling the dimension of `H^0` of `⊕ O(d_i)(m)` on `P^1`. -/
def h0_multiset (s : Multiset ℤ) (m : ℤ) : ℕ :=
  (s.map (fun d => (d + m + 1).toNat)).sum

/-- Integer-valued variant of `h0_multiset`, summing `(d + m + 1).toNat` viewed as integers. -/
def h0z (s : Multiset ℤ) (m : ℤ) : ℤ :=
  (s.map (fun d => ((d + m + 1).toNat : ℤ))).sum

/-- The integer version `h0z` equals the natural-number `h0_multiset` cast to `ℤ`. -/
lemma h0z_eq_cast (s : Multiset ℤ) (m : ℤ) :
    h0z s m = (h0_multiset s m : ℤ) := by
  unfold h0z h0_multiset
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih]; push_cast; ring

/-- Cons-recurrence for `h0z`: adding a degree `a` to the multiset adds `(a + m + 1).toNat`. -/
lemma h0z_cons (a : ℤ) (s : Multiset ℤ) (m : ℤ) :
    h0z (a ::ₘ s) m = ((a + m + 1).toNat : ℤ) + h0z s m := by
  unfold h0z; simp [Multiset.map_cons, Multiset.sum_cons]

/-- Cons-recurrence for `h0_multiset` matching `h0z_cons`. -/
lemma h0_multiset_cons (a : ℤ) (s : Multiset ℤ) (m : ℤ) :
    h0_multiset (a ::ₘ s) m = (a + m + 1).toNat + h0_multiset s m := by
  unfold h0_multiset; simp [Multiset.map_cons, Multiset.sum_cons]

/-- Pointwise discrete second difference: `(d' - d + 1).toNat - 2 (d' - d).toNat + (d' - d - 1).toNat`
equals `1` iff `d' = d`, otherwise `0`. -/
lemma single_second_diff (d' d : ℤ) :
    ((d' - d + 1).toNat : ℤ) - 2 * (d' - d).toNat + (d' - d - 1).toNat =
    if d' = d then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · by_cases h1 : d < d'
    ·
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ d' - d - 1),
          Int.toNat_of_nonneg (by omega : 0 ≤ d' - d),
          Int.toNat_of_nonneg (by omega : 0 ≤ d' - d + 1)]
      ring
    ·
      simp [Int.toNat_eq_zero.mpr (by omega : d' - d + 1 ≤ 0),
            Int.toNat_eq_zero.mpr (by omega : d' - d ≤ 0),
            Int.toNat_eq_zero.mpr (by omega : d' - d - 1 ≤ 0)]

/-- Key recovery lemma: the discrete second difference of `h0z s` at `-d` equals the multiplicity
of `d` in `s`. This lets us reconstruct a multiset of splitting degrees from its `h^0` data. -/
theorem second_diff_eq_count (s : Multiset ℤ) (d : ℤ) :
    h0z s (-d) - 2 * h0z s (-d - 1) + h0z s (-d - 2) = s.count d := by
  induction s using Multiset.induction with
  | empty => simp [h0z]
  | cons a s ih =>
    rw [h0z_cons, h0z_cons, h0z_cons, Multiset.count_cons]
    have eq1 : a + (-d) + 1 = a - d + 1 := by ring
    have eq2 : a + (-d - 1) + 1 = a - d := by ring
    have eq3 : a + (-d - 2) + 1 = a - d - 1 := by ring
    rw [eq1, eq2, eq3]
    push_cast
    linarith [single_second_diff a d,
              show (if a = d then (1 : ℤ) else 0) = if d = a then 1 else 0 from
                by split_ifs <;> omega]

/-- Uniqueness: two multisets of integers with identical `h0z` data are equal. -/
theorem h0z_determines_multiset (s t : Multiset ℤ)
    (h : ∀ m : ℤ, h0z s m = h0z t m) : s = t := by
  ext d
  have hs := second_diff_eq_count s d
  have ht := second_diff_eq_count t d
  rw [h (-d), h (-d - 1), h (-d - 2)] at hs
  exact_mod_cast hs.symm.trans ht

/-- Natural-number version: two multisets with identical `h0_multiset` data are equal. -/
theorem h0_multiset_determines_multiset (s t : Multiset ℤ)
    (h : ∀ m : ℤ, h0_multiset s m = h0_multiset t m) : s = t := by
  apply h0z_determines_multiset
  intro m
  rw [h0z_eq_cast, h0z_eq_cast]
  exact_mod_cast h m

/-- Turn a tuple of degrees `degrees : Fin n → ℤ` into the corresponding multiset of values. -/
def degreesToMultiset {n : ℕ} (degrees : Fin n → ℤ) : Multiset ℤ :=
  Finset.univ.val.map degrees

/-- Bridge between the splitting-type `h0_twisted` formula and the multiset-level `h0_multiset`. -/
lemma h0_twisted_eq_h0_multiset {n : ℕ} (s : GBExistence.SplittingType n) (t : ℤ) :
    s.h0_twisted t =
    h0_multiset (degreesToMultiset s.degrees) t := by
  unfold GBExistence.SplittingType.h0_twisted GBExistence.h0_dim
  unfold h0_multiset degreesToMultiset
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  rfl

/-- Grothendieck-Birkhoff uniqueness at the multiset level: two splitting types that yield
the same twisted `h^0` data must define the same multiset of summand degrees. -/
theorem splitting_uniqueness_multiset {n : ℕ}
    (s₁ s₂ : GBExistence.SplittingType n)
    (h : ∀ t : ℤ, s₁.h0_twisted t = s₂.h0_twisted t) :
    degreesToMultiset s₁.degrees = degreesToMultiset s₂.degrees := by
  apply h0_multiset_determines_multiset
  intro m
  rw [← h0_twisted_eq_h0_multiset, ← h0_twisted_eq_h0_multiset]
  exact h m

/-- Two decreasing tuples `Fin n → ℤ` that determine the same multiset are equal pointwise. -/
lemma sorted_eq_of_multiset_eq {n : ℕ}
    (f g : Fin n → ℤ)
    (hf : ∀ i j : Fin n, i ≤ j → g j ≤ g i)
    (hg : ∀ i j : Fin n, i ≤ j → f j ≤ f i)
    (hmulti : degreesToMultiset f = degreesToMultiset g) :
    f = g := by

  have hperm : (List.ofFn f).Perm (List.ofFn g) := by
    rw [← Multiset.coe_eq_coe]
    show (List.ofFn f : Multiset ℤ) = (List.ofFn g : Multiset ℤ)
    unfold degreesToMultiset at hmulti
    rwa [Fin.univ_val_map, Fin.univ_val_map] at hmulti
  have hsorted_f : (List.ofFn f).Pairwise (· ≥ ·) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hg i j (le_of_lt hij)
  have hsorted_g : (List.ofFn g).Pairwise (· ≥ ·) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hf i j (le_of_lt hij)
  have hlist_eq : List.ofFn f = List.ofFn g :=
    hperm.eq_of_pairwise
      (fun a b _ _ (h1 : a ≥ b) (h2 : b ≥ a) => le_antisymm h2 h1)
      hsorted_f hsorted_g
  exact List.ofFn_injective hlist_eq

/-- Grothendieck-Birkhoff uniqueness in sorted form (Thm 24.1): the decreasing splitting tuple is
uniquely determined by the twisted `h^0` data. -/
theorem splitting_uniqueness_sorted {n : ℕ}
    (s₁ s₂ : GBExistence.SplittingType n)
    (h : ∀ t : ℤ, s₁.h0_twisted t = s₂.h0_twisted t) :
    s₁.degrees = s₂.degrees := by
  exact sorted_eq_of_multiset_eq s₁.degrees s₂.degrees
    s₂.sorted s₁.sorted
    (splitting_uniqueness_multiset s₁ s₂ h)

/-- `H^0` direct-sum formula: summing `h^0` of summands `O(d_i)(m)` agrees with the multiset
formula `h0_multiset` applied to the multiset of degrees. -/
theorem h0_directsum_formula {n : ℕ} (degrees : Fin n → ℤ) (m : ℤ) :
    ∑ i, GBExistence.h0_dim (degrees i + m) = h0_multiset (degreesToMultiset degrees) m := by
  unfold GBExistence.h0_dim h0_multiset degreesToMultiset
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  rfl

/-- Multiset-level `h^1` formula: for splitting degrees `d_i`, the dimension of `H^1` of
`⊕ O(d_i)(m)` on `P^1` is `∑ max(-d_i - m - 1, 0)`. -/
def h1_multiset (s : Multiset ℤ) (m : ℤ) : ℕ :=
  (s.map (fun d => (-d - m - 1).toNat)).sum

/-- `H^1` direct-sum formula matching `h0_directsum_formula`. -/
theorem h1_directsum_formula {n : ℕ} (degrees : Fin n → ℤ) (m : ℤ) :
    ∑ i, GBExistence.h1_dim (degrees i + m) = h1_multiset (degreesToMultiset degrees) m := by
  unfold GBExistence.h1_dim h1_multiset degreesToMultiset
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  congr 1; ext d; simp [Function.comp]; ring_nf

/-- Natural-number version of `second_diff_eq_count`: the discrete second difference of
`h0_multiset` at `-d` returns the multiplicity of `d`. -/
theorem second_diff_eq_count_nat (s : Multiset ℤ) (d : ℤ) :
    h0_multiset s (-d) + h0_multiset s (-d - 2) - 2 * h0_multiset s (-d - 1) = s.count d := by
  have hz := second_diff_eq_count s d
  rw [h0z_eq_cast, h0z_eq_cast, h0z_eq_cast] at hz
  omega

end GBUniqueness
