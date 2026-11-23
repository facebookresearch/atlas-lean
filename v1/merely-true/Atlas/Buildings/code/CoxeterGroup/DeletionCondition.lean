/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length

variable {B : Type*}

namespace Garrett.ExchangeDeletion

/-- The exchange condition for a Coxeter system: if right multiplying a
reduced word $\omega$ by $s_i$ decreases length, there is some index $i$ such
that erasing the $i$-th letter from $\omega$ produces a word with product
$\omega \cdot s$. -/
def SatisfiesExchangeCondition {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) : Prop :=
  ∀ (word : List B) (s : B),
    cs.IsReduced word →
    cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word) →
    ∃ (i : Fin word.length),
      cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s

/-- The deletion condition: if a word is non-reduced, two letters can be erased
without changing its product. Formally, if $\mathtt{word.length} >
\ell(\mathtt{wordProd}\,\mathtt{word})$ then there exist $i < j$ such that
erasing positions $i$ and $j$ leaves the product unchanged. -/
def SatisfiesDeletionCondition {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) : Prop :=
  ∀ (word : List B),
    word.length > cs.length (cs.wordProd word) →
    ∃ (i j : Fin word.length), i < j ∧
      cs.wordProd ((word.eraseIdx j).eraseIdx i) = cs.wordProd word

/-- Corollary of the exchange condition used in subexpression arguments: if both
$\ell(sw) = \ell(w) + 1$ and $\ell(wt) = \ell(w) + 1$ hold, then either
$\ell(swt) = \ell(w) + 2$ or $swt = w$. -/
def ExchangeCorollary {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) : Prop :=
  ∀ (w : W) (s t : B),
    cs.length (cs.simple s * w) = cs.length w + 1 →
    cs.length (w * cs.simple t) = cs.length w + 1 →
    cs.length (cs.simple s * w * cs.simple t) = cs.length w + 2 ∨
    cs.simple s * w * cs.simple t = w

/-- Given a sequence $f : \mathbb{N} \to \mathbb{N}$ that starts at $0$ and at
each step either increases or decreases by $1$, if $f(n) < n$ then there is a
first index $j < n$ where $f$ decreases (i.e. $f(j+1) + 1 = f(j)$ and $f$ is
strictly increasing on $[0, j]$). -/
lemma exists_first_decreasing (f : ℕ → ℕ) (n : ℕ) (h0 : f 0 = 0)
    (hstep : ∀ j, j < n → (f (j + 1) = f j + 1 ∨ f (j + 1) + 1 = f j))
    (hlt : n > f n) :
    ∃ j, j < n ∧ f (j + 1) + 1 = f j ∧ (∀ k, k < j → f (k + 1) = f k + 1) := by
  have hex : ∃ j, j < n ∧ f (j + 1) + 1 = f j := by
    induction n with
    | zero => omega
    | succ m ihm =>
      rcases hstep m (by omega) with hup | hdown
      · obtain ⟨j, hj, hjd⟩ := ihm (fun j hj => hstep j (by omega)) (by omega)
        exact ⟨j, by omega, hjd⟩
      · exact ⟨m, by omega, hdown⟩
  let j₀ := Nat.find hex
  have hj₀ := Nat.find_spec hex
  refine ⟨j₀, hj₀.1, hj₀.2, ?_⟩
  intro k hk
  by_contra hk_not_up
  have hk_lt_n : k < n := by have := hj₀.1; omega
  rcases hstep k hk_lt_n with hup | hdown
  · exact hk_not_up hup
  · exact absurd ⟨hk_lt_n, hdown⟩ (Nat.find_min hex hk)

/-- The exchange condition implies the deletion condition: any non-reduced word
admits a pair of letters whose removal preserves its product. -/
theorem deletion_of_exchange {B : Type*} {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (hex : SatisfiesExchangeCondition M cs) :
    SatisfiesDeletionCondition M cs := by
  intro word hlong

  set f := fun k => cs.length (cs.wordProd (word.take k)) with hf_def
  have hf0 : f 0 = 0 := by simp [hf_def, cs.wordProd_nil, cs.length_one]
  have hfstep : ∀ k, k < word.length → (f (k + 1) = f k + 1 ∨ f (k + 1) + 1 = f k) := by
    intro k hk; simp only [hf_def]
    rw [List.take_succ_eq_append_getElem hk, cs.wordProd_append, cs.wordProd_singleton]
    exact cs.length_mul_simple _ _
  have hfn : word.length > f word.length := by
    simp [hf_def, List.take_length]; exact hlong

  obtain ⟨j, hj_lt, hj_down, hj_first⟩ := exists_first_decreasing f word.length hf0 hfstep hfn

  have htake_red : cs.IsReduced (word.take j) := by
    unfold CoxeterSystem.IsReduced
    rw [List.length_take, Nat.min_eq_left (by omega : j ≤ word.length)]
    suffices h : ∀ m, m ≤ j → f m = m from h j le_rfl
    intro m hm
    induction m with
    | zero => exact hf0
    | succ n ih => rw [hj_first n (by omega), ih (by omega)]
  have htake_len : (word.take j).length = j := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  have hprod_succ : cs.wordProd (word.take (j + 1)) =
      cs.wordProd (word.take j) * cs.simple word[j] := by
    rw [List.take_succ_eq_append_getElem hj_lt, cs.wordProd_append, cs.wordProd_singleton]

  have hlen_drop : cs.length (cs.wordProd (word.take j) * cs.simple word[j]) <
      cs.length (cs.wordProd (word.take j)) := by
    rw [← hprod_succ]; simp only [hf_def] at hj_down; omega
  obtain ⟨⟨i_val, hi_bound⟩, hi_eq⟩ :=
    hex (word.take j) word[j] htake_red hlen_drop
  rw [← hprod_succ] at hi_eq
  rw [htake_len] at hi_bound

  refine ⟨⟨i_val, by omega⟩, ⟨j, hj_lt⟩, by simpa using hi_bound, ?_⟩

  have hlist : (word.eraseIdx j).eraseIdx i_val =
      (word.take j).eraseIdx i_val ++ word.drop (j + 1) := by
    conv_lhs => rw [List.eraseIdx_eq_take_drop_succ word j]
    exact List.eraseIdx_append_of_lt_length (by rw [htake_len]; exact hi_bound) _
  rw [hlist, cs.wordProd_append, hi_eq, ← cs.wordProd_append, List.take_append_drop]

/-- The exchange condition implies the exchange corollary: given an element $w$
with $\ell(sw) = \ell(wt) = \ell(w) + 1$, either $\ell(swt) = \ell(w) + 2$ or
$swt = w$. -/
theorem corollary_of_exchange {B : Type*} {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (hex : SatisfiesExchangeCondition M cs) :
    ExchangeCorollary M cs := by
  intro w s t hsw hwt
  obtain ⟨ω, hωred, hωprod⟩ := cs.exists_isReduced w
  have hωlen : cs.length w = ω.length := hωprod ▸ hωred

  have hsω_reduced : cs.IsReduced (s :: ω) := by
    unfold CoxeterSystem.IsReduced
    rw [cs.wordProd_cons, List.length_cons, ← hωprod, hsw, hωlen]
  have hsω_prod : cs.wordProd (s :: ω) = cs.simple s * w := by
    rw [cs.wordProd_cons, hωprod]
  have hassoc : cs.simple s * w * cs.simple t = cs.simple s * (w * cs.simple t) :=
    mul_assoc _ _ _
  rcases cs.length_mul_simple (cs.simple s * w) t with hup | hdown
  ·
    left; rw [hassoc] at hup ⊢; omega
  ·
    rw [hassoc] at hdown
    have hlt : cs.length (cs.wordProd (s :: ω) * cs.simple t) <
        cs.length (cs.wordProd (s :: ω)) := by
      rw [hsω_prod, hassoc]; omega
    obtain ⟨i, hi⟩ := hex (s :: ω) t hsω_reduced hlt
    rw [hsω_prod, hassoc] at hi
    by_cases hi0 : i.val = 0
    ·
      right
      have herase : (s :: ω).eraseIdx i = ω := by simp [hi0]
      rw [herase] at hi
      rw [← hassoc, ← hωprod] at hi
      exact hi.symm
    ·
      exfalso
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi0
      obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 :=
        ⟨i.val - 1, (Nat.succ_pred_eq_of_pos hi_pos).symm⟩
      have herase : (s :: ω).eraseIdx i.val = s :: (ω.eraseIdx j) := by
        rw [hj, List.eraseIdx_cons_succ]
      change cs.wordProd ((s :: ω).eraseIdx i.val) = _ at hi
      rw [herase, cs.wordProd_cons] at hi
      have hprod_erased : cs.wordProd (ω.eraseIdx j) = w * cs.simple t :=
        mul_left_cancel hi
      have hj_lt : j < ω.length := by
        have := i.isLt; simp [List.length_cons] at this; omega
      have hlen_erased : (ω.eraseIdx j).length = ω.length - 1 :=
        List.length_eraseIdx_of_lt hj_lt
      have := cs.length_wordProd_le (ω.eraseIdx j)
      rw [hprod_erased, hwt, hlen_erased, hωlen] at this
      omega

end Garrett.ExchangeDeletion
