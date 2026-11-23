/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.DihedralPositivityFinite

open Finset BigOperators

namespace CoxeterGroup

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- If $v$ is supported on $\{s, t\}$, then $\sigma_w(v) = v_s \cdot \sigma_w \alpha_s + v_t \cdot \sigma_w \alpha_t$. -/
theorem wordSigma_linear_combination (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (word : List B) (v : B → ℝ) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
    wordSigma M word v =
      v s • wordSigma M word (e s) + v t • wordSigma M word (e t) := by
  have hv_decomp : v = v s • e s + v t • e t := by
    ext u
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
    by_cases hus : u = s
    · subst hus; simp [hst]
    · by_cases hut : u = t
      · subst hut; simp [Ne.symm hst]
      · simp [hus, hut, hsupp u hus hut]
  conv_lhs => rw [hv_decomp]
  rw [wordSigma_add, wordSigma_smul, wordSigma_smul]

/-- A word on $\{s, t\}$ with consecutive entries distinct and last letter $t$ is
canonical: of the form $stst\cdots$ of even length or $tsts\cdots t$ of odd length. -/
theorem alternating_word_canonical (s t : B) (hst : s ≠ t)
    (word : List B)
    (halt : ∀ b ∈ word, b = s ∨ b = t)
    (hchain : List.Chain' (· ≠ ·) word)
    (hlast : word = [] ∨ (∃ h : word ≠ [], word.getLast h = t)) :
    (∃ k, word = altWordEven s t k) ∨ (∃ k, word = t :: altWordEven s t k) := by
  induction word with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons a tail ih =>
    have hlast_t : (a :: tail).getLast (List.cons_ne_nil a tail) = t := by
      rcases hlast with h | ⟨_, h⟩
      · exact absurd h (List.cons_ne_nil a tail)
      · exact h
    have ha : a = s ∨ a = t := halt a List.mem_cons_self
    have halt_tail : ∀ b ∈ tail, b = s ∨ b = t := fun b hb => halt b (List.mem_cons_of_mem a hb)
    have hchain_tail : List.Chain' (· ≠ ·) tail := List.IsChain.tail hchain
    have hlast_tail : tail = [] ∨ (∃ h : tail ≠ [], tail.getLast h = t) := by
      cases tail with
      | nil => exact Or.inl rfl
      | cons b rest =>
        right; refine ⟨List.cons_ne_nil b rest, ?_⟩
        have : (a :: b :: rest).getLast (List.cons_ne_nil a (b :: rest)) = t := hlast_t
        simp [List.getLast_cons] at this
        exact this
    have ih_result := ih halt_tail hchain_tail hlast_tail
    rcases ha with ha_s | ha_t
    ·
      rcases ih_result with ⟨k, hk⟩ | ⟨k, hk⟩
      ·
        cases k with
        | zero =>

          simp [altWordEven] at hk; subst hk
          simp at hlast_t; exact absurd hlast_t (ha_s ▸ hst)
        | succ m =>


          exfalso
          have hk' : tail = s :: t :: altWordEven s t m := hk
          have : a ≠ s := by
            have hc := hchain
            rw [show a :: tail = a :: (s :: t :: altWordEven s t m) from by rw [hk']] at hc
            exact List.IsChain.rel_head hc
          exact this ha_s
      ·

        exact Or.inl ⟨k + 1, by simp [altWordEven, ha_s, hk]⟩
    ·
      rcases ih_result with ⟨k, hk⟩ | ⟨k, hk⟩
      ·

        exact Or.inr ⟨k, by simp [ha_t, hk]⟩
      ·
        exfalso
        have : a ≠ t := by
          have hc := hchain
          rw [show a :: tail = a :: (t :: altWordEven s t k) from by rw [hk]] at hc
          exact List.IsChain.rel_head hc
        exact this ha_t

/-- Positivity for canonical alternating words on $\{s, t\}$: dispatches to the dihedral
even/odd cases. -/
theorem parabolic_pos_of_canon (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (word : List B) (hlen : word.length < M s t ∨ M s t = 0)
    (hcanon : (∃ k, word = altWordEven s t k) ∨ (∃ k, word = t :: altWordEven s t k)) :
    IsPositive (wordSigma M word (e s)) := by
  rcases hcanon with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : 2 * k < M s t ∨ M s t = 0 := by
      rcases hlen with hlt | hm0
      · left; rw [altWordEven_length] at hlt; exact hlt
      · right; exact hm0
    exact dihedral_pos_even M s t hst k hk
  · have hk : 2 * k + 1 < M s t ∨ M s t = 0 := by
      rcases hlen with hlt | hm0
      · left
        have : (t :: altWordEven s t k).length = 2 * k + 1 := by
          simp [altWordEven_length]
        omega
      · right; exact hm0
    exact dihedral_pos_odd M s t hst k hk

/-- Positivity in the rank-2 parabolic $W_{\{s,t\}}$: any alternating word $w$ of length
$< m(s,t)$ (or any length if $m(s,t) = 0$) gives $\sigma_w(\alpha_s) \geq 0$. -/
theorem parabolic_pos (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (word : List B) (halt : ∀ b ∈ word, b = s ∨ b = t)
    (hlen : word.length < M s t ∨ M s t = 0)
    (hchain : List.Chain' (· ≠ ·) word)
    (hlast : word = [] ∨ (∃ h : word ≠ [], word.getLast h = t)) :
    IsPositive (wordSigma M word (e s)) :=
  parabolic_pos_of_canon M s t hst word hlen
    (alternating_word_canonical s t hst word halt hchain hlast)

/-- If $\sigma_w(\alpha_s)$ and $\sigma_w(\alpha_t)$ are positive vectors and $v \geq 0$
is supported on $\{s, t\}$, then $\sigma_w(v) \geq 0$. -/
theorem parabolic_pos_vector_of_both_positive (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (word : List B)
    (hpos_s : IsPositive (wordSigma M word (e s)))
    (hpos_t : IsPositive (wordSigma M word (e t)))
    (v : B → ℝ) (hpos : IsPositive v) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
    IsPositive (wordSigma M word v) := by
  rw [wordSigma_linear_combination M s t hst word v hsupp]
  exact (hpos_s.smul_nonneg (hpos s)).add (hpos_t.smul_nonneg (hpos t))

end CoxeterGroup
