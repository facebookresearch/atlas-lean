/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.CoxeterSystemFromDeletion
import Mathlib.GroupTheory.Coxeter.Basic

open CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- Erasing two distinct indices reduces the list length by exactly $2$:
$|(l.\mathtt{eraseIdx}\,j).\mathtt{eraseIdx}\,i| + 2 = |l|$. -/
lemma eraseIdx_eraseIdx_length {α : Type*} {l : List α} {i j : ℕ}
    (hij : i < j) (hj : j < l.length) :
    ((l.eraseIdx j).eraseIdx i).length + 2 = l.length := by
  have hi_bound : i < (l.eraseIdx j).length := by
    rw [List.length_eraseIdx_of_lt hj]
    omega
  rw [List.length_eraseIdx_of_lt hi_bound, List.length_eraseIdx_of_lt hj]
  omega

/-- If the family $\mathtt{gen}$ satisfies the deletion condition, any word
mapping to $1$ under $\mathtt{gen}$ has even length. (One can repeatedly delete
pairs of letters by the deletion condition.) -/
theorem deletion_relation_even_length
    {B : Type*} {W : Type*} [Group W]
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hDel : SatisfiesDeletionConditionGen gen)
    (word : List B) (hw : (word.map gen).prod = 1) :
    Even word.length := by

  suffices ∀ (n : ℕ), ∀ (w : List B), w.length = n →
      (w.map gen).prod = 1 → Even w.length from this _ word rfl hw
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro w hlen hw'

  by_cases hpos : n = 0
  · subst hpos; simp [hlen]
  ·
    have hnonred : ∃ (shorter : List B), shorter.length < w.length ∧
        (shorter.map gen).prod = (w.map gen).prod :=
      ⟨[], by simp [hlen]; omega, by simp [hw']⟩

    obtain ⟨i, j, hij, hj, hprod⟩ := hDel w hnonred

    set w' := (w.eraseIdx j).eraseIdx i with hw'_def

    have hlen' : w'.length + 2 = w.length := eraseIdx_eraseIdx_length hij hj

    have hw'_prod : (w'.map gen).prod = 1 := by rw [hw'_def, hprod, hw']

    have hlt : w'.length < n := by omega
    have heven' := ih w'.length hlt w' rfl hw'_prod

    obtain ⟨k, hk⟩ := heven'
    exact ⟨k + 1, by omega⟩

/-- An involution is self-inverse: if $g \cdot g = 1$ then $g^{-1} = g$. -/
lemma inv_eq_self_of_involution {G : Type*} [Group G] {g : G} (h : g * g = 1) : g⁻¹ = g := by
  rw [mul_eq_one_iff_eq_inv] at h; exact h.symm

/-- Mapping inversion over a list of involutions yields the same list. -/
lemma map_inv_eq_self_of_involutions (gen : B → W)
    (hgen_inv : ∀ s, gen s * gen s = 1) (l : List B) :
    (l.map gen).map (·⁻¹) = l.map gen := by
  simp only [List.map_map]; congr 1; ext s
  exact inv_eq_self_of_involution (hgen_inv s)

/-- For a list of involutions, the product of the reversed list equals the
inverse of the original product. -/
lemma reverse_map_prod_inv_of_involutions (gen : B → W)
    (hgen_inv : ∀ s, gen s * gen s = 1) (l : List B) :
    ((l.reverse).map gen).prod = ((l.map gen).prod)⁻¹ := by
  rw [List.map_reverse, List.prod_reverse_noncomm,
      map_inv_eq_self_of_involutions gen hgen_inv l]

/-- If a word of length $2m$ with $m > 1$ maps to $1$, then its initial segment
of length $m + 1$ admits a strictly shorter word with the same product: namely,
the reverse of the second half. -/
lemma first_half_nonreduced (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (word : List B) (m : ℕ) (hlen : word.length = 2 * m) (hm : m > 1)
    (hw : (word.map gen).prod = 1) :
    ∃ (shorter : List B), shorter.length < (word.take (m + 1)).length ∧
      (shorter.map gen).prod = ((word.take (m + 1)).map gen).prod := by
  refine ⟨(word.drop (m + 1)).reverse, ?_, ?_⟩
  ·
    rw [List.length_reverse, List.length_drop, List.length_take]; omega
  ·
    have hsplit : ((word.take (m + 1)).map gen).prod *
        ((word.drop (m + 1)).map gen).prod = 1 := by
      rw [← List.prod_append, ← List.map_append, List.take_append_drop]; exact hw
    rw [mul_eq_one_iff_eq_inv] at hsplit
    rw [reverse_map_prod_inv_of_involutions gen hgen_inv, hsplit]

/-- Transport of the braid relation: if $(\mathtt{gen}\,s \cdot
\mathtt{gen}\,t)^m = 1$ in $W$, then the same braid relation
$(\mathtt{simple}\,s \cdot \mathtt{simple}\,t)^m = 1$ holds in the abstract
Coxeter group associated to $\mathtt{gen}$. -/
lemma alternating_word_maps_to_one
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (s t : B) (m : ℕ)
    (h_prod : (gen s * gen t) ^ m = 1) :
    let M := deletionCoxeterMatrix gen hgen_inv hgen_ne
    (M.simple s * M.simple t) ^ m = 1 := by
  intro M

  have h_dvd : orderOf (gen s * gen t) ∣ m := orderOf_dvd_of_pow_eq_one h_prod

  have h_M_eq : M s t = orderOf (gen s * gen t) := by
    simp only [M, deletionCoxeterMatrix, Matrix.of_apply]

  have h_M_dvd : M s t ∣ m := h_M_eq ▸ h_dvd

  have h_rel : (M.simple s * M.simple t) ^ (M s t) = 1 :=
    M.toCoxeterSystem.simple_mul_simple_pow s t

  obtain ⟨k, hk⟩ := h_M_dvd
  rw [hk, pow_mul, h_rel, one_pow]

/-- The product $g(k) \cdot g(k+1) \cdots g(k + m - 1)$ of $m$ consecutive
values of a sequence $g : \mathbb{N} \to W$ starting at index $k$. -/
def consecProd {W : Type*} [Monoid W] (g : ℕ → W) (k m : ℕ) : W :=
  ((List.range m).map (fun i => g (k + i))).prod

/-- Peeling off the first factor: $\mathtt{consecProd}\,g\,k\,(m+1) = g(k)
\cdot \mathtt{consecProd}\,g\,(k+1)\,m$. -/
lemma consecProd_succ {W' : Type*} [Monoid W'] (g : ℕ → W') (k m : ℕ) :
    consecProd g k (m + 1) = g k * consecProd g (k + 1) m := by
  simp only [consecProd]
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.prod_cons, List.map_map]
  have : (fun i => g (k + i)) ∘ Nat.succ = fun i => g (k + 1 + i) := by
    ext i; show g (k + (i + 1)) = g (k + 1 + i); ring_nf
  rw [this]; simp

/-- Peeling off two factors: $\mathtt{consecProd}\,g\,k\,(m+2) = g(k)\,g(k+1)
\cdot \mathtt{consecProd}\,g\,(k+2)\,m$. -/
lemma consecProd_succ_succ {W' : Type*} [Monoid W'] (g : ℕ → W') (k m : ℕ) :
    consecProd g k (m + 2) = g k * g (k + 1) * consecProd g (k + 2) m := by
  rw [consecProd_succ, consecProd_succ, mul_assoc]

/-- If for every $k$ the $m$-fold product starting at $k$ equals the same
product but with the first factor replaced by $g(k+2)$, then $g$ is two-step
periodic: $g(k) = g(k+2)$ for all $k$. -/
lemma cycling_alternating_of_L_type (g : ℕ → W)
    (m : ℕ) (hm : m ≥ 2)
    (h_L : ∀ k, consecProd g k m =
      g (k + 2) * g (k + 1) * consecProd g (k + 2) (m - 2)) :
    ∀ k, g k = g (k + 2) := by
  intro k
  have hpeel : consecProd g k m =
      g k * g (k + 1) * consecProd g (k + 2) (m - 2) := by
    conv_lhs => rw [show m = (m - 2) + 2 from by omega]
    exact consecProd_succ_succ g k (m - 2)
  have hLk := h_L k
  rw [hpeel] at hLk
  exact mul_right_cancel (mul_right_cancel hLk)

/-- Cyclic extension of $\mathtt{gen}\circ\mathtt{word}$ to all of
$\mathbb{N}$: at index $k$ it returns the generator at position $k \bmod n$. -/
def wordCyclicGen (gen : B → W) (word : List B) (n : ℕ)
    (hn : word.length = n) (hn0 : n > 0) (k : ℕ) : W :=
  gen (word.get ⟨k % n, by rw [hn]; exact Nat.mod_lt k hn0⟩)

/-- For a word of length $2m$ ($m \ge 2$), if the cyclic generator satisfies
the $L$-type identity, then the word is two-step periodic at the level of
generator values: $\mathtt{gen}(\mathtt{word}[k]) =
\mathtt{gen}(\mathtt{word}[k+2])$ whenever both indices fit. -/
lemma cycling_forces_alternating
    {B : Type*} {W : Type*} [Group W]
    (gen : B → W)
    (word : List B)
    (m : ℕ) (hlen : word.length = 2 * m) (hm : m ≥ 2)
    (h_L_type : ∀ k,
      consecProd (wordCyclicGen gen word (2 * m) hlen (by omega)) k m =
      wordCyclicGen gen word (2 * m) hlen (by omega) (k + 2) *
      wordCyclicGen gen word (2 * m) hlen (by omega) (k + 1) *
      consecProd (wordCyclicGen gen word (2 * m) hlen (by omega)) (k + 2) (m - 2)) :
    ∀ (k : ℕ) (hk : k + 2 < word.length),
      gen (word.get ⟨k, by omega⟩) = gen (word.get ⟨k + 2, by omega⟩) := by
  intro k hk
  have h := cycling_alternating_of_L_type
    (wordCyclicGen gen word (2 * m) hlen (by omega)) m hm h_L_type k
  simp only [wordCyclicGen, Nat.mod_eq_of_lt (show k < 2 * m by omega),
    Nat.mod_eq_of_lt (show k + 2 < 2 * m by omega)] at h
  exact h

end CoxeterSystemFromDeletion
