/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation
import Atlas.Buildings.code.CoxeterGroup.ExchangeDeletion
import Atlas.Buildings.code.CoxeterGroup.Roots

open Finset BigOperators

namespace CoxeterExchangeGenuine

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The root sequence read off from a word $\omega$ and a simple root $e_s$:
the $k$-th term is the geometric image of $e_s$ under the suffix of $\omega$
of length $k$. Used to detect sign changes along the word. -/
noncomputable def rootSequence (M : CoxeterMatrix B) (word : List B) (s : B) (k : ℕ) :
    B → ℝ :=
  CoxeterGroup.wordSigma M (word.drop (word.length - k)) (CoxeterGroup.e s)

/-- Geometric bridge hypothesis: bundles the two implications connecting the
abstract length function and the geometric representation. Field
$\mathtt{length\_decrease\_negative}$ says length-decrease on right
multiplication implies negativity of the resulting root, and field
$\mathtt{sign\_change\_exchange}$ says negativity implies the exchange
relation $\omega = \omega' \cdot s$ for some deletion of $\omega$. -/
structure GeometricBridgeHyp {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) where
  length_decrease_negative : ∀ (word : List B) (s : B),
    cs.IsReduced word →
    cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word) →
    CoxeterGroup.IsNegative (CoxeterGroup.wordSigma M word (CoxeterGroup.e s))
  sign_change_exchange : ∀ (word : List B) (s : B),
    cs.IsReduced word →
    CoxeterGroup.IsNegative (CoxeterGroup.wordSigma M word (CoxeterGroup.e s)) →
    ∃ (i : Fin word.length),
      cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s

/-- Given the geometric bridge hypothesis, the abstract exchange condition
follows by composing length-decrease implies negativity with negativity
implies exchange. -/
theorem exchange_from_bridge {W : Type*} [Group W]
    {M : CoxeterMatrix B} {cs : CoxeterSystem M W}
    (bridge : GeometricBridgeHyp M cs) :
    CoxeterExchange.SatisfiesExchangeCondition M cs := by
  intro word s hred hlen
  exact bridge.sign_change_exchange word s hred
    (bridge.length_decrease_negative word s hred hlen)


/-- The bilinear form is anti-linear under negation in its first slot:
$B(-v, w) = -B(v, w)$. -/
theorem bilinForm_neg_left (M : CoxeterMatrix B) (v w : B → ℝ) :
    CoxeterGroup.bilinForm M (-v) w = -CoxeterGroup.bilinForm M v w := by
  have : -v = (-1 : ℝ) • v := by ext x; simp
  rw [this, CoxeterGroup.bilinForm_smul_left]
  ring

omit [Fintype B] in
/-- The simple root $e_s$ has strictly positive $s$-coordinate, namely $1$. -/
theorem e_self_coord_positive (s : B) :
    CoxeterGroup.e s s > 0 := by
  simp [CoxeterGroup.e]

/-- Sign-change lemma: a sequence $f : \mathbb{N} \to \mathbb{R}$ with
$f(0) > 0$ and $f(n) < 0$ has some index $k < n$ where $f(k) \ge 0$ but
$f(k+1) < 0$. -/
theorem exists_sign_change (f : ℕ → ℝ) (n : ℕ) (_hn : 0 < n)
    (hf0 : f 0 > 0) (hfn : f n < 0) :
    ∃ k, k < n ∧ f k ≥ 0 ∧ f (k + 1) < 0 := by

  by_contra h
  push_neg at h

  have : ∀ k, k ≤ n → f k ≥ 0 := by
    intro k hk
    induction k with
    | zero => linarith
    | succ m ih =>
      have hm_le : m ≤ n := by omega
      have hm_lt : m < n := by omega
      exact h m hm_lt (ih hm_le)
  linarith [this n le_rfl]

/-- Strict-to-non-strict variant of $\mathtt{exists\_sign\_change}$:
$f(0) > 0$ and $f(n) \le 0$ give an index $k$ with $f(k) > 0$ and
$f(k+1) \le 0$. -/
theorem exists_sign_change' (f : ℕ → ℝ) (n : ℕ) (_hn : 0 < n)
    (hf0 : f 0 > 0) (hfn : f n ≤ 0) :
    ∃ k, k < n ∧ f k > 0 ∧ f (k + 1) ≤ 0 := by
  by_contra h
  push_neg at h

  have : ∀ k, k ≤ n → f k > 0 := by
    intro k hk
    induction k with
    | zero => exact hf0
    | succ m ih =>
      have hm_le : m ≤ n := by omega
      have hm_lt : m < n := by omega
      exact h m hm_lt (ih hm_le)
  linarith [this n le_rfl]


/-- A more granular bridge hypothesis: for any reduced word $\omega$ and
simple root $e_s$ whose total geometric image is negative, an index $k$
witnessing the sign change of the $s$-coordinate yields an exchange
$\omega = \omega' \cdot s$ for some deletion of $\omega$. -/
structure RootSignChangeHyp {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) where
  sign_change_at_index : ∀ (word : List B) (s : B) (k : ℕ),
    cs.IsReduced word →
    k < word.length →

    CoxeterGroup.IsNegative (CoxeterGroup.wordSigma M word (CoxeterGroup.e s)) →

    (CoxeterGroup.wordSigma M (word.drop (word.length - k)) (CoxeterGroup.e s) s > 0) →
    (CoxeterGroup.wordSigma M (word.drop (word.length - (k + 1))) (CoxeterGroup.e s) s ≤ 0) →
    ∃ (i : Fin word.length),
      cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s

end CoxeterExchangeGenuine
