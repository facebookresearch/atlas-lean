/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.ExchangeConditionWiring
import Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation
import Atlas.Buildings.code.CoxeterGroup.RootSignChangeProof
import Mathlib.GroupTheory.Coxeter.Length

open CoxeterGroup CoxeterExchangeGenuine

set_option maxHeartbeats 3200000

namespace CoxeterSignChangeExchangeFinal

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- A vector that is both positive and negative everywhere is zero. -/
lemma isPositive_isNegative_eq_zero
    {v : B → ℝ} (hpos : IsPositive v) (hneg : IsNegative v) :
    v = 0 := by
  ext t; have h1 := hpos t; have h2 := hneg t
  simp; linarith

/-- The bilinear form vanishes when its left argument is zero. -/
lemma bilinForm_zero_left (M : CoxeterMatrix B) (w : B → ℝ) :
    bilinForm M 0 w = 0 := by
  unfold bilinForm; simp

/-- Convenience wrapper: dropping a prefix of a reduced word leaves a reduced word. -/
lemma isReduced_drop' {W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) {word : List B} (hred : cs.IsReduced word) (j : ℕ) :
    cs.IsReduced (word.drop j) :=
  CoxeterRootSignChange.isReduced_drop cs hred j

/-- The simple root $e_s$ is not negative (its $s$-coordinate is $1 > 0$). -/
lemma e_not_isNegative (s : B) : ¬ IsNegative (e (B := B) s) := by
  intro h; have := h s; simp [e] at this; linarith


/-- If $w \cdot e_s$ is negative for a reduced word $w$, then $s$ is a right descent:
$\ell(ws) < \ell(w)$. -/
lemma isNegative_implies_descent {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hneg : IsNegative (wordSigma M word (e s))) :
    cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word) := by
  by_contra h
  push_neg at h
  have hasc : cs.length (cs.wordProd word * cs.simple s) >
              cs.length (cs.wordProd word) := by
    rcases cs.length_mul_simple (cs.wordProd word) s with h1 | h1 <;> omega
  have hpos := pos_of_ascent M cs word s hred hasc
  have hzero := isPositive_isNegative_eq_zero hpos hneg
  have hform := wordSigma_preserves_form M word (e s) (e s)
  rw [hzero, bilinForm_zero_left] at hform
  linarith [show bilinForm M (e s) (e s) = 1 from by rw [bilinForm_e_e, formVal_diag]]


/-- Faithfulness of the geometric (Tits) representation:
the homomorphism $W \to \operatorname{GL}(\mathbb{R}^B)$ given by simple reflections is injective. -/
theorem coxeterRepresentation_injective (M : CoxeterMatrix B) {W : Type*} [Group W]
    (cs : CoxeterSystem M W) :
    Function.Injective (coxeterRepresentation M cs) := by
  intro g₁ g₂ hρ
  suffices h : g₁ * g₂⁻¹ = 1 by
    calc g₁ = g₁ * g₂⁻¹ * g₂ := by group
      _ = 1 * g₂ := by rw [h]
      _ = g₂ := one_mul _
  by_contra hw_ne
  have hρw : coxeterRepresentation M cs (g₁ * g₂⁻¹) = 1 := by
    rw [map_mul, map_inv, hρ, mul_inv_cancel]
  have hlen_pos : 0 < cs.length (g₁ * g₂⁻¹) := by
    rwa [Nat.pos_iff_ne_zero, ne_eq, cs.length_eq_zero_iff]

  obtain ⟨word, hred_word, hprod_word⟩ := cs.exists_reduced_word (g₁ * g₂⁻¹)


  have hred : cs.IsReduced word := hred_word

  have hword_ne : word ≠ [] := by
    intro h; subst h; simp [CoxeterSystem.wordProd_nil] at hprod_word
    exact hw_ne hprod_word
  have hword_len : 0 < word.length := by
    rw [← hred]; rw [← hprod_word]; exact hlen_pos
  set sₙ := word.getLast hword_ne

  have hid : ∀ v, wordSigma M word v = v := by
    intro v
    have h1 := coxeterRepresentation_wordProd_apply M cs word v
    have h2 : coxeterRepresentation M cs (cs.wordProd word) = 1 := by
      rw [← hprod_word]; exact hρw
    rw [h2] at h1
    simp [LinearEquiv.coe_one] at h1; exact h1.symm

  have hdesc_sn : cs.length (cs.wordProd word * cs.simple sₙ) <
                  cs.length (cs.wordProd word) := by


    have hprod' : cs.wordProd word = cs.wordProd word.dropLast * cs.simple sₙ := by
      conv_lhs => rw [← List.dropLast_append_getLast hword_ne]
      rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton]
    have : cs.wordProd word * cs.simple sₙ = cs.wordProd word.dropLast := by
      rw [hprod', mul_assoc, cs.simple_mul_simple_self, mul_one]
    rw [this]
    calc cs.length (cs.wordProd word.dropLast)
        ≤ word.dropLast.length := cs.length_wordProd_le _
      _ < word.length := by
          rw [List.length_dropLast]; exact Nat.sub_one_lt_of_le hword_len le_rfl
      _ = cs.length (cs.wordProd word) := hred.symm


  have hneg_sn : IsNegative (wordSigma M word (e sₙ)) :=
    neg_of_descent M cs word sₙ hred hdesc_sn
  rw [hid (e sₙ)] at hneg_sn
  exact e_not_isNegative sₙ hneg_sn


/-- If $v$ is positive, $\sigma_t v$ is negative, and $\langle v, v\rangle = 1$, then $v = e_t$.
This is the geometric "unique root" step that powers the sign-change exchange. -/
lemma isPositive_sigma_isNegative_eq_e (M : CoxeterMatrix B) (t : B)
    (v : B → ℝ) (hpos : IsPositive v)
    (hneg_sigma : IsNegative (sigma M t v))
    (hform : bilinForm M v v = 1) :
    v = e t := by
  have hvu : ∀ u, u ≠ t → v u = 0 := by
    intro u hu
    have h1 := hpos u; have h2 := hneg_sigma u
    simp only [sigma] at h2
    have he : e t u = 0 := by simp [e, hu]
    rw [he, mul_zero, sub_zero] at h2; linarith
  have hv_eq : v = v t • e t := by
    ext u; by_cases hu : u = t
    · subst hu; simp [e, Pi.smul_apply]
    · rw [hvu u hu]; simp [e, hu, Pi.smul_apply]
  rw [hv_eq, bilinForm_smul_left, bilinForm_smul_right, bilinForm_e_e, formVal_diag] at hform
  have hvt_pos := hpos t
  have hvt_eq : v t = 1 := by nlinarith [mul_self_nonneg (v t)]
  rw [hv_eq, hvt_eq, one_smul]


/-- If $w \cdot e_s = e_t$ geometrically, then $s_t \cdot w = w \cdot s_s$ in the Coxeter group. -/
lemma wordProd_cons_eq_append_of_wordSigma_eq_e {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (tail : List B) (s t : B)
    (hsigma : wordSigma M tail (e s) = e t) :
    cs.simple t * cs.wordProd tail = cs.wordProd tail * cs.simple s := by
  have hinj := coxeterRepresentation_injective M cs
  apply hinj

  ext v

  have lhs_eq : (coxeterRepresentation M cs (cs.simple t * cs.wordProd tail)) v =
      sigma M t (wordSigma M tail v) := by
    simp only [map_mul, LinearEquiv.mul_apply, coxeterRepresentation_simple,
               sigmaLinearEquiv_apply, coxeterRepresentation_wordProd_apply]

  have rhs_eq : (coxeterRepresentation M cs (cs.wordProd tail * cs.simple s)) v =
      wordSigma M tail (sigma M s v) := by
    simp only [map_mul, LinearEquiv.mul_apply, coxeterRepresentation_simple,
               sigmaLinearEquiv_apply, coxeterRepresentation_wordProd_apply]
  rw [lhs_eq, rhs_eq]


  have hB : bilinForm M (wordSigma M tail v) (e t) = bilinForm M v (e s) := by
    rw [← hsigma, wordSigma_preserves_form]


  suffices key : sigma M t (wordSigma M tail v) = wordSigma M tail (sigma M s v) by
    exact congr_fun key _

  have hlin_add : ∀ (w : List B) (a b : B → ℝ),
      wordSigma M w (a + b) = wordSigma M w a + wordSigma M w b := by
    intro w a b
    have h1 := coxeterRepresentation_wordProd_apply M cs w (a + b)
    have h2 := coxeterRepresentation_wordProd_apply M cs w a
    have h3 := coxeterRepresentation_wordProd_apply M cs w b
    rw [← h1, ← h2, ← h3]
    simp [map_add]
  have hlin_smul : ∀ (w : List B) (c : ℝ) (a : B → ℝ),
      wordSigma M w (c • a) = c • wordSigma M w a := by
    intro w c a
    have h1 := coxeterRepresentation_wordProd_apply M cs w (c • a)
    have h2 := coxeterRepresentation_wordProd_apply M cs w a
    rw [← h1, ← h2]
    simp [map_smul]

  have hsigma_eq : sigma M s v = v + (-2 * bilinForm M v (e s)) • e s := by
    ext u; simp [sigma, Pi.add_apply, Pi.smul_apply]; ring

  have hrhs : wordSigma M tail (sigma M s v) =
      wordSigma M tail v + (-2 * bilinForm M v (e s)) • e t := by
    rw [hsigma_eq, hlin_add, hlin_smul, hsigma]

  have hlhs : sigma M t (wordSigma M tail v) =
      wordSigma M tail v + (-2 * bilinForm M (wordSigma M tail v) (e t)) • e t := by
    ext u; simp [sigma, Pi.add_apply, Pi.smul_apply]; ring

  rw [hlhs, hrhs, hB]

/-- Exchange at the leading position: if $\mathrm{tail} \cdot e_s = e_t$, deleting the head $t$
realizes the exchange $w_{\text{tail}} = (t :: \mathrm{tail}) \cdot s$. -/
lemma exchange_at_zero {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (t : B) (tail : List B) (s : B)
    (hsigma : wordSigma M tail (e s) = e t) :
    cs.wordProd tail = cs.wordProd (t :: tail) * cs.simple s := by
  rw [CoxeterSystem.wordProd_cons,
      wordProd_cons_eq_append_of_wordSigma_eq_e cs tail s t hsigma,
      mul_assoc, cs.simple_mul_simple_self, mul_one]


/-- **Sign change exchange theorem** (unconditional): if a reduced word $w$ satisfies
$w \cdot e_s$ is negative, then there is an index $i$ such that $w' \cdot s = w$ where $w'$ is $w$
with its $i$-th letter removed. This is the geometric form of the exchange condition. -/
theorem signChangeExchangeHyp_unconditional {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) :
    CoxeterExchange.SignChangeExchangeHyp M cs := by
  suffices ∀ n, ∀ word : List B, ∀ s : B,
      word.length = n →
      cs.IsReduced word →
      IsNegative (wordSigma M word (e s)) →
      ∃ (i : Fin word.length),
        cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s by
    intro word s hred hneg
    exact this word.length word s rfl hred hneg
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro word s hlen hred hneg

    by_cases hlen0 : n = 0
    · subst hlen0
      have : word = [] := by simpa using hlen
      subst this
      simp [wordSigma_nil] at hneg
      exact absurd hneg (e_not_isNegative s)
    ·
      have hword_ne : word ≠ [] := by
        intro h; subst h; simp at hlen; omega

      set t := word.head hword_ne with ht_def
      set tail := word.tail with htail_def
      have hword_eq : word = t :: tail := (List.cons_head_tail hword_ne).symm
      have htail_red : cs.IsReduced tail := by
        have : tail = (t :: tail).drop 1 := by simp
        rw [this, ← hword_eq]
        exact isReduced_drop' cs hred 1
      have htail_len : tail.length < n := by
        have : (t :: tail).length = n := by rwa [← hword_eq]
        simp at this; omega

      by_cases hneg_tail : IsNegative (wordSigma M tail (e s))
      ·
        obtain ⟨⟨i, hi⟩, hexch⟩ := ih tail.length htail_len tail s rfl htail_red hneg_tail
        have hi' : i + 1 < word.length := by rw [hword_eq]; simp; omega
        refine ⟨⟨i + 1, hi'⟩, ?_⟩


        have h1 : word.eraseIdx (i + 1) = t :: (tail.eraseIdx i) := by
          rw [hword_eq]; exact List.eraseIdx_cons_succ
        rw [h1, CoxeterSystem.wordProd_cons, hword_eq, CoxeterSystem.wordProd_cons, hexch, mul_assoc]

      ·
        have hpos_tail : IsPositive (wordSigma M tail (e s)) := by
          rcases cs.length_mul_simple (cs.wordProd tail) s with hasc | hdesc
          ·
            exact pos_of_ascent M cs tail s htail_red (by omega)
          ·
            exfalso; apply hneg_tail
            exact neg_of_descent M cs tail s htail_red (by omega)

        have hneg_sigma : IsNegative (sigma M t (wordSigma M tail (e s))) := by
          rwa [← wordSigma_cons, ← hword_eq]

        have hform : bilinForm M (wordSigma M tail (e s)) (wordSigma M tail (e s)) = 1 := by
          rw [wordSigma_preserves_form, bilinForm_e_e, formVal_diag]

        have heq : wordSigma M tail (e s) = e t :=
          isPositive_sigma_isNegative_eq_e M t _ hpos_tail hneg_sigma hform

        have h0 : 0 < word.length := by rw [hword_eq]; simp
        refine ⟨⟨0, h0⟩, ?_⟩
        have h1 : word.eraseIdx 0 = tail := by
          rw [hword_eq]; exact List.eraseIdx_cons_zero
        rw [h1]


        rw [hword_eq]
        exact exchange_at_zero cs t tail s heq

end CoxeterSignChangeExchangeFinal
