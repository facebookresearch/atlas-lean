/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.SignChangeExchangeFinal
import Atlas.Buildings.code.CoxeterGroup.InversionMultiplication
import Atlas.Buildings.code.CoxeterGroup.SimpleReflectionInversions
import Atlas.Buildings.code.CoxeterGroup.StrongExchangeBridge

open CoxeterGroup CoxeterSignChangeExchangeFinal

set_option maxHeartbeats 800000

namespace DescentInversionBridge

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- If two words have the same product in $W$, they induce the same action on
the geometric representation. -/
theorem wordSigma_eq_of_wordProd_eq {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word₁ word₂ : List B)
    (h : cs.wordProd word₁ = cs.wordProd word₂) (v : B → ℝ) :
    wordSigma M word₁ v = wordSigma M word₂ v := by
  have h1 := coxeterRepresentation_wordProd_apply M cs word₁ v
  have h2 := coxeterRepresentation_wordProd_apply M cs word₂ v
  rw [h] at h1
  rw [← h1, ← h2]


/-- Right-descent implies negative root: if a reduced word ends with a right
descent at $i$, then its action on $e_i$ is a negative root. -/
theorem descent_implies_isNegative {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (i : B)
    (hred : cs.IsReduced word)
    (hdesc : cs.IsRightDescent (cs.wordProd word) i) :
    IsNegative (wordSigma M word (e i)) := by
  have hlt : cs.length (cs.wordProd word * cs.simple i) <
             cs.length (cs.wordProd word) := by
    rw [CoxeterSystem.isRightDescent_iff] at hdesc; omega
  exact neg_of_descent M cs word i hred hlt

/-- Converse: if a reduced word's action on $e_i$ is a negative root, then $i$
is a right descent of the corresponding group element. -/
theorem isNegative_implies_descent' {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (i : B)
    (hred : cs.IsReduced word)
    (hneg : IsNegative (wordSigma M word (e i))) :
    cs.IsRightDescent (cs.wordProd word) i := by
  have hlt := isNegative_implies_descent M cs word i hred hneg
  rw [CoxeterSystem.isRightDescent_iff]
  rcases cs.length_mul_simple (cs.wordProd word) i with h | h <;> omega

/-- Descent-negativity equivalence for reduced words: $i$ is a right descent
iff the word's action on $e_i$ gives a negative root. -/
theorem descent_iff_isNegative {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (i : B)
    (hred : cs.IsReduced word) :
    cs.IsRightDescent (cs.wordProd word) i ↔
    IsNegative (wordSigma M word (e i)) :=
  ⟨descent_implies_isNegative M cs word i hred,
   isNegative_implies_descent' M cs word i hred⟩


/-- Ascent implies positive root: if $i$ is not a right descent, the word's
action on $e_i$ is a positive root. -/
theorem ascent_implies_isPositive {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (i : B)
    (hred : cs.IsReduced word)
    (hasc : ¬cs.IsRightDescent (cs.wordProd word) i) :
    IsPositive (wordSigma M word (e i)) := by
  have hgt : cs.length (cs.wordProd word * cs.simple i) >
             cs.length (cs.wordProd word) := by
    rw [CoxeterSystem.not_isRightDescent_iff] at hasc
    omega
  exact pos_of_ascent M cs word i hred hgt

/-- Converse: if a reduced word's action on $e_i$ is a positive root, then $i$
is not a right descent. -/
theorem isPositive_implies_ascent {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (i : B)
    (hred : cs.IsReduced word)
    (hpos : IsPositive (wordSigma M word (e i))) :
    ¬cs.IsRightDescent (cs.wordProd word) i := by
  intro hdesc
  have hneg := descent_implies_isNegative M cs word i hred hdesc
  have hzero := isPositive_isNegative_eq_zero hpos hneg
  have hform := wordSigma_preserves_form M word (e i) (e i)
  rw [hzero] at hform
  simp [bilinForm_zero_left] at hform
  linarith [show bilinForm M (e i) (e i) = 1 from by rw [bilinForm_e_e, formVal_diag]]

/-- Ascent-positivity equivalence for reduced words. -/
theorem ascent_iff_isPositive {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (i : B)
    (hred : cs.IsReduced word) :
    ¬cs.IsRightDescent (cs.wordProd word) i ↔
    IsPositive (wordSigma M word (e i)) :=
  ⟨ascent_implies_isPositive M cs word i hred,
   isPositive_implies_ascent M cs word i hred⟩


/-- Appending $s$ to a word toggles negativity at $e_s$: the result is a
negative root iff the original was a positive root. -/
theorem wordSigma_append_isNegative_toggle (M : CoxeterMatrix B) (word : List B) (s : B) :
    IsNegative (wordSigma M (word ++ [s]) (e s)) ↔
    IsPositive (wordSigma M word (e s)) := by
  have hflip := wordSigma_append_s_neg M word s
  constructor
  · intro hneg t
    have := hneg t
    rw [hflip] at this
    simp at this
    linarith
  · intro hpos t
    rw [hflip]
    simp
    exact hpos t

/-- The other direction: appending $s$ to a word toggles positivity at
$e_s$. -/
theorem wordSigma_append_isPositive_toggle (M : CoxeterMatrix B) (word : List B) (s : B) :
    IsPositive (wordSigma M (word ++ [s]) (e s)) ↔
    IsNegative (wordSigma M word (e s)) := by
  have hflip := wordSigma_append_s_neg M word s
  constructor
  · intro hpos t
    have := hpos t
    rw [hflip] at this
    simp at this
    linarith
  · intro hneg t
    rw [hflip]
    simp
    have := hneg t
    linarith


/-- Right-descent toggle for an append: when both $\omega$ and $\omega \cdot
s$ are reduced, $s$ is a right descent of $\omega s$ iff it is not a right
descent of $\omega$. -/
theorem descent_toggle_append {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (s : B)
    (hred_word : cs.IsReduced word)
    (hred_app : cs.IsReduced (word ++ [s])) :
    cs.IsRightDescent (cs.wordProd (word ++ [s])) s ↔
    ¬cs.IsRightDescent (cs.wordProd word) s := by
  rw [descent_iff_isNegative M cs (word ++ [s]) s hred_app,
      wordSigma_append_isNegative_toggle,
      ← ascent_iff_isPositive M cs word s hred_word]


/-- For any right descent $s$ of $w$, there exists a reduced word for $w$
ending in $s$. -/
theorem exists_reduced_word_ending_in_descent' {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (w : W) (s : B)
    (hdesc : cs.IsRightDescent w s) :
    ∃ prefix_word, cs.IsReduced (prefix_word ++ [s]) ∧
      cs.wordProd (prefix_word ++ [s]) = w := by
  have hlt : cs.length (w * cs.simple s) < cs.length w := by
    rw [CoxeterSystem.isRightDescent_iff] at hdesc; omega
  exact StrongExchangeBridge.exists_reduced_word_ending_in_descent w s hlt


/-- The descent-negativity equivalence stated in terms of a general
representative reduced word. -/
theorem descent_iff_isNegative_any_word {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (w : W) (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hprod : cs.wordProd word = w) :
    cs.IsRightDescent w s ↔ IsNegative (wordSigma M word (e s)) := by
  rw [← hprod]
  exact descent_iff_isNegative M cs word s hred


/-- Membership in the bilinear-inversion set implies a right descent. -/
theorem mem_bilinInversions_implies_isRightDescent {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hmem : s ∈ bilinInversions M word) :
    cs.IsRightDescent (cs.wordProd word) s := by
  rw [CoxeterGroup.mem_bilinInversions_iff] at hmem
  by_contra hasc
  have hasc' : ¬cs.IsRightDescent (cs.wordProd word) s := hasc
  have hpos := ascent_implies_isPositive M cs word s hred hasc'
  linarith [hpos s]


/-- The action of any word on a basis vector $e_s$ is nonzero. -/
theorem wordSigma_ne_zero (M : CoxeterMatrix B) (word : List B) (s : B) :
    wordSigma M word (e s) ≠ 0 := by
  intro h
  have hform := wordSigma_preserves_form M word (e s) (e s)
  rw [h] at hform
  simp [bilinForm_zero_left] at hform
  linarith [show bilinForm M (e s) (e s) = 1 from by rw [bilinForm_e_e, formVal_diag]]


/-- A negative root has a strictly negative component. -/
theorem isNegative_exists_neg_component
    (M : CoxeterMatrix B) (word : List B) (s : B)
    (hneg : IsNegative (wordSigma M word (e s))) :
    ∃ t, wordSigma M word (e s) t < 0 := by
  by_contra h
  push_neg at h
  have hzero : wordSigma M word (e s) = 0 := by
    ext t; simp only [Pi.zero_apply]; linarith [h t, hneg t]
  exact wordSigma_ne_zero M word s hzero

/-- For a reduced word and a right descent $s$, the action on $e_s$ has a
strictly negative component. -/
theorem descent_exists_neg_component {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hdesc : cs.IsRightDescent (cs.wordProd word) s) :
    ∃ t, wordSigma M word (e s) t < 0 :=
  isNegative_exists_neg_component M word s
    (descent_implies_isNegative M cs word s hred hdesc)

/-- For a reduced word and a right ascent at $s$, the action on $e_s$ has a
strictly positive component. -/
theorem ascent_exists_pos_component {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hasc : ¬cs.IsRightDescent (cs.wordProd word) s) :
    ∃ t, wordSigma M word (e s) t > 0 := by
  have hpos := ascent_implies_isPositive M cs word s hred hasc
  by_contra h
  push_neg at h
  have hzero : wordSigma M word (e s) = 0 := by
    ext t; simp only [Pi.zero_apply]; linarith [h t, hpos t]
  exact wordSigma_ne_zero M word s hzero


/-- The bilinear-inversion set depends only on the group element, not on the
chosen reduced expression. -/
theorem bilinInversions_eq_of_wordProd_eq {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word₁ word₂ : List B)
    (h : cs.wordProd word₁ = cs.wordProd word₂) :
    bilinInversions M word₁ = bilinInversions M word₂ := by
  ext s
  simp only [CoxeterGroup.mem_bilinInversions_iff]
  have := wordSigma_eq_of_wordProd_eq M cs word₁ word₂ h (e s)
  constructor
  · intro h1; rw [← this]; exact h1
  · intro h2; rw [this]; exact h2

/-- Self-toggle for bilinear inversions: when the $s$-component is nonzero,
membership of $s$ in $\mathtt{bilinInversions}(\omega s)$ is the negation of
membership in $\mathtt{bilinInversions}(\omega)$. -/
theorem bilinInversions_self_toggle_of_ne_zero
    (M : CoxeterMatrix B) (word : List B) (s : B)
    (hne : wordSigma M word (e s) s ≠ 0) :
    s ∈ bilinInversions M (word ++ [s]) ↔ s ∉ bilinInversions M word :=
  bilinInversions_append_toggle M word s hne


/-- The bilinear-inversion set of the empty word is empty. -/
theorem bilinInversions_nil' (M : CoxeterMatrix B) :
    bilinInversions M ([] : List B) = ∅ :=
  bilinInversions_nil M

/-- The bilinear-inversion set of a singleton word $[s]$ is $\{s\}$. -/
theorem bilinInversions_singleton' (M : CoxeterMatrix B) (s : B) :
    bilinInversions M [s] = {s} :=
  bilinInversions_singleton M s


omit [DecidableEq B] [Fintype B] in
/-- If $\omega \cdot s$ is reduced, then $s$ is a right descent of
$\omega \cdot s$. -/
theorem isRightDescent_of_reduced_append {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (s : B)
    (hred : cs.IsReduced (word ++ [s])) :
    cs.IsRightDescent (cs.wordProd (word ++ [s])) s := by
  rw [CoxeterSystem.isRightDescent_iff]
  have hlen : cs.length (cs.wordProd (word ++ [s])) = word.length + 1 := by
    rw [CoxeterSystem.IsReduced] at hred
    rw [hred, List.length_append, List.length_singleton]
  have hle : cs.length (cs.wordProd word) ≤ word.length := cs.length_wordProd_le word
  rw [cs.wordProd_append, cs.wordProd_singleton, mul_assoc,
      cs.simple_mul_simple_self, mul_one]
  rw [cs.wordProd_append, cs.wordProd_singleton] at hlen
  rcases cs.length_mul_simple (cs.wordProd word) s with h | h <;> omega

omit [DecidableEq B] [Fintype B] in
/-- If $\omega \cdot s$ is reduced, then $s$ is not a right descent of
$\omega$ (otherwise $\omega \cdot s$ would have length $< |\omega| + 1$). -/
theorem not_isRightDescent_of_reduced_prefix {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (s : B)
    (hred : cs.IsReduced (word ++ [s])) :
    ¬cs.IsRightDescent (cs.wordProd word) s := by
  rw [CoxeterSystem.not_isRightDescent_iff]
  have hred_word : cs.IsReduced word := by
    have := hred.take word.length
    rwa [List.take_left] at this
  have hlen_word : cs.length (cs.wordProd word) = word.length := by
    rw [CoxeterSystem.IsReduced] at hred_word; exact hred_word
  have hlen_app : cs.length (cs.wordProd (word ++ [s])) = word.length + 1 := by
    rw [CoxeterSystem.IsReduced] at hred
    rw [hred, List.length_append, List.length_singleton]
  rw [cs.wordProd_append, cs.wordProd_singleton] at hlen_app
  omega

end DescentInversionBridge
