/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.BruhatOrder

set_option maxHeartbeats 400000

variable {B : Type*}

namespace CoxeterBruhat

section SEC
variable {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- The Strong Exchange Condition: if $\omega$ is a reduced word for $w$ and
$t$ is a reflection such that $\ell(wt) < \ell(w)$, then $wt$ is obtained from
$\omega$ by deleting one letter. -/
def StrongExchangeCondition
    {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) : Prop :=
  ∀ (ω : List B) (t : W),
    cs.IsReduced ω →
    t ∈ reflections M cs →
    cs.length (cs.wordProd ω * t) < cs.length (cs.wordProd ω) →
    ∃ i : Fin ω.length, cs.wordProd (ω.eraseIdx i) = cs.wordProd ω * t

/-- The reduced sublist property: every word $\omega$ admits a reduced sublist
$\tau$ with the same product. This is equivalent to the deletion condition. -/
def ReducedSublistProperty
    {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) : Prop :=
  ∀ (ω : List B), ∃ τ : List B,
    τ.Sublist ω ∧ cs.IsReduced τ ∧ cs.wordProd τ = cs.wordProd ω

end SEC

/-- Case analysis for a sublist of $l ++ [s]$: it is either a sublist of $l$
or has the form $\sigma' ++ [s]$ for some sublist $\sigma'$ of $l$. -/
theorem sublist_concat_cases {α : Type*} :
    ∀ (σ l : List α) (s : α), σ.Sublist (l ++ [s]) →
    σ.Sublist l ∨ ∃ σ', σ = σ' ++ [s] ∧ σ'.Sublist l := by
  intro σ l
  induction l generalizing σ with
  | nil =>
    intro s h; simp only [List.nil_append] at h
    cases h with
    | cons _ h' => left; exact h'
    | cons₂ _ h' =>
      right; cases h' with | slnil => exact ⟨[], by simp, List.nil_sublist []⟩
  | cons a l' ih =>
    intro s h; cases h with
    | cons _ h' =>
      rcases ih σ s h' with h1 | ⟨σ', hσ', hσ'_sub⟩
      · left; exact h1.cons a
      · right; exact ⟨σ', hσ', hσ'_sub.cons a⟩
    | @cons₂ l₁ _ _ h' =>
      rcases ih l₁ s h' with h1 | ⟨σ', hσ', hσ'_sub⟩
      · left; exact h1.cons₂ a
      · right; exact ⟨a :: σ', by rw [hσ']; simp, hσ'_sub.cons₂ a⟩

section SubexpressionTheorem
variable {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Tits' subexpression theorem (forward direction): if $v \le w$ in the
Bruhat order and $\omega$ is a reduced word for $w$, then $v$ is the product
of some sublist of $\omega$. -/
theorem bruhatLE_subexpression_forward
    (hSEC : StrongExchangeCondition cs)
    (hRSP : ReducedSublistProperty cs)
    {v w : W} (hvw : BruhatLE cs v w)
    {ω : List B} (hred : cs.IsReduced ω) (hprod : w = cs.wordProd ω) :
    ∃ σ : List B, σ.Sublist ω ∧ v = cs.wordProd σ := by
  suffices h : ∀ (n : ℕ) {v w : W}, BruhatLE cs v w →
      ∀ {ω : List B}, cs.IsReduced ω → w = cs.wordProd ω → ω.length ≤ n →
      ∃ σ : List B, σ.Sublist ω ∧ v = cs.wordProd σ from
    h ω.length hvw hred hprod le_rfl
  intro n
  induction n with
  | zero =>
    intro v w hvw ω hred hprod hlen
    have hω : ω = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hω; subst hprod
    have hv : v = 1 := by
      have hle := bruhatLE_length_le cs hvw
      rw [cs.wordProd_nil, cs.length_one] at hle
      exact cs.length_eq_zero_iff.mp (Nat.le_zero.mp hle)
    exact ⟨[], List.nil_sublist [], by simp [hv, cs.wordProd_nil]⟩
  | succ n ih =>
    intro v w hvw ω hred hprod hlen
    by_cases hve : v = w
    · exact ⟨ω, List.Sublist.refl ω, by rw [hve, hprod]⟩
    · have ⟨w', hw'_le, hw'_step⟩ : ∃ w', BruhatLE cs v w' ∧ BruhatStep cs w' w := by
        induction hvw with
        | refl => exact absurd rfl hve
        | @tail b c hab hbc _ => exact ⟨b, hab, hbc⟩
      obtain ⟨t, ht_refl, hw't, hlen_step⟩ := hw'_step
      have hrev : w * t = w' := mul_reflection_reverse cs ht_refl hw't
      subst hprod
      have hlt : cs.length (cs.wordProd ω * t) < cs.length (cs.wordProd ω) := by
        rw [hrev]; exact hlen_step
      obtain ⟨k, hk⟩ := hSEC ω t hred ht_refl hlt
      have hw'_eq : w' = cs.wordProd (ω.eraseIdx k) := by rw [hk, hrev]
      have hlen_erase : (ω.eraseIdx ↑k).length ≤ n := by
        have := List.length_eraseIdx_of_lt k.isLt; omega
      obtain ⟨τ, hτ_sub, hτ_red, hτ_prod⟩ := hRSP (ω.eraseIdx ↑k)
      have hτ_prod' : w' = cs.wordProd τ := by rw [hw'_eq, ← hτ_prod]
      have hτ_len : τ.length ≤ n := le_trans hτ_sub.length_le hlen_erase
      obtain ⟨σ, hσ_sub, hσ_eq⟩ := ih hw'_le hτ_red hτ_prod' hτ_len
      exact ⟨σ, hσ_sub.trans (hτ_sub.trans (List.eraseIdx_sublist ω ↑k)), hσ_eq⟩

/-- Tits' subexpression theorem (backward direction): if $\omega$ is a reduced
word for $w$ and $v$ is the product of some sublist of $\omega$, then
$v \le w$ in the Bruhat order. -/
theorem subexpression_bruhatLE_backward
    (hSEC : StrongExchangeForBruhat cs)
    {v w : W} {ω : List B} (hred : cs.IsReduced ω) (hprod : w = cs.wordProd ω)
    {σ : List B} (hσ_sub : σ.Sublist ω) (hσ_eq : v = cs.wordProd σ) :
    BruhatLE cs v w := by
  suffices h : ∀ (n : ℕ) {v w : W} {ω : List B},
      cs.IsReduced ω → w = cs.wordProd ω → ω.length ≤ n →
      ∀ {σ : List B}, σ.Sublist ω → v = cs.wordProd σ → BruhatLE cs v w from
    h ω.length hred hprod le_rfl hσ_sub hσ_eq
  intro n
  induction n with
  | zero =>
    intro v w ω hred hprod hlen σ hσ_sub hσ_eq
    have hω : ω = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hω
    have hσ : σ = [] := List.eq_nil_of_length_eq_zero
      (Nat.le_zero.mp (le_trans hσ_sub.length_le (by simp)))
    subst hσ; subst hσ_eq; subst hprod
    exact bruhatLE_refl cs _
  | succ n ih =>
    intro v w ω hred hprod hlen σ hσ_sub hσ_eq
    by_cases hω_empty : ω = []
    · subst hω_empty
      have hσ : σ = [] := List.eq_nil_of_length_eq_zero
        (Nat.le_zero.mp (le_trans hσ_sub.length_le (by simp)))
      subst hσ; subst hσ_eq; subst hprod
      exact bruhatLE_refl cs _
    · obtain ⟨ω', sn, hω_split⟩ : ∃ (ω' : List B) (sn : B), ω = ω' ++ [sn] :=
        ⟨ω.dropLast, ω.getLast hω_empty, (List.dropLast_append_getLast hω_empty).symm⟩
      subst hω_split
      have hω'_red : cs.IsReduced ω' := by
        have : ω' = (ω' ++ [sn]).take ω'.length := by simp
        rw [this]; exact hred.take _
      have hprod_split : cs.wordProd (ω' ++ [sn]) = cs.wordProd ω' * cs.simple sn := by
        rw [← List.concat_eq_append, cs.wordProd_concat]
      set w' := cs.wordProd ω' with hw'_def
      have hw_eq : w = w' * cs.simple sn := by rw [hprod, hprod_split]
      have hlen_w' : cs.length w' < cs.length w := by
        rw [CoxeterSystem.IsReduced] at hred
        have h1 : cs.length (cs.wordProd (ω' ++ [sn])) = (ω' ++ [sn]).length := hred
        rw [hprod_split, List.length_append, List.length_singleton] at h1
        have h2 : cs.length w' = ω'.length := hω'_red
        rw [hw_eq]; omega
      have hw'_le_w : BruhatLE cs w' w := by
        rw [hw_eq]
        exact bruhatLE_of_step cs ⟨cs.simple sn, simple_mem_reflections cs sn, rfl, by
          rw [← hw_eq]; exact hlen_w'⟩
      rcases sublist_concat_cases σ ω' sn hσ_sub with hcase1 | ⟨σ', hσ'_split, hσ'_sub⟩
      · have hlen_ω' : ω'.length ≤ n := by simp at hlen; omega
        exact bruhatLE_trans cs (ih hω'_red hw'_def.symm hlen_ω' hcase1 hσ_eq) hw'_le_w
      · have hv_split : v = cs.wordProd σ' * cs.simple sn := by
          rw [hσ_eq, hσ'_split, ← List.concat_eq_append, cs.wordProd_concat]
        set v' := cs.wordProd σ' with hv'_def
        have hlen_ω' : ω'.length ≤ n := by simp at hlen; omega
        have hv'_le_w' : BruhatLE cs v' w' :=
          ih hω'_red hw'_def.symm hlen_ω' hσ'_sub hv'_def.symm
        rcases bruhat_right_mul cs hSEC hv'_le_w' sn with hcase_a | hcase_b
        · rw [hv_split]
          exact bruhatLE_trans cs hcase_a hw'_le_w
        · rw [hv_split, hw_eq]; exact hcase_b

/-- Tits' subexpression theorem: $v \le w$ in the Bruhat order if and only if
$v$ is the product of some sublist of a (any) reduced word $\omega$ for $w$. -/
theorem subexpression_theorem
    (hSEC_full : StrongExchangeCondition cs)
    (hRSP : ReducedSublistProperty cs)
    (hSEC : StrongExchangeForBruhat cs)
    {v w : W} {ω : List B} (hred : cs.IsReduced ω) (hprod : w = cs.wordProd ω) :
    BruhatLE cs v w ↔ ∃ σ : List B, σ.Sublist ω ∧ v = cs.wordProd σ :=
  ⟨fun hvw => bruhatLE_subexpression_forward cs hSEC_full hRSP hvw hred hprod,
   fun ⟨_, hσ_sub, hσ_eq⟩ => subexpression_bruhatLE_backward cs hSEC hred hprod hσ_sub hσ_eq⟩

end SubexpressionTheorem

section CoveringLemma
variable {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- The strict Bruhat order: $v < w$ iff $v \le w$ and $v \ne w$. -/
def BruhatLT (v w : W) : Prop := BruhatLE cs v w ∧ v ≠ w

/-- Bruhat covering lemma: given a Bruhat cover $v < w$ with $i$ not a right
descent of $v$ and $v s_i \ne w$, both $w < w s_i$ and $v s_i < w s_i$ hold in
the Bruhat order. -/
theorem bruhat_covering_lemma
    (hSEC : StrongExchangeForBruhat cs)
    {v w : W} (hvw : BruhatLT cs v w)
    (hcover : cs.length v + 1 = cs.length w)
    (i : B) (hv_up : ¬cs.IsRightDescent v i) (hne : v * cs.simple i ≠ w) :
    BruhatLT cs w (w * cs.simple i) ∧ BruhatLT cs (v * cs.simple i) (w * cs.simple i) := by
  obtain ⟨hvw_le, hvw_ne⟩ := hvw
  have hv_up' : cs.length (v * cs.simple i) = cs.length v + 1 :=
    cs.not_isRightDescent_iff.mp hv_up
  rcases bruhat_right_mul cs hSEC hvw_le i with hcase1 | hcase2
  · exfalso; exact hne (bruhatLE_eq_of_length_eq cs hcase1 (by omega))
  · have hvs_ne_ws : v * cs.simple i ≠ w * cs.simple i :=
      fun h => hvw_ne (mul_right_cancel h)
    have hvs_lt_ws : BruhatLT cs (v * cs.simple i) (w * cs.simple i) :=
      ⟨hcase2, hvs_ne_ws⟩
    have hle_ws : cs.length w ≤ cs.length (w * cs.simple i) := by
      have hle := bruhatLE_length_le cs hcase2; omega
    have hws_len : cs.length w < cs.length (w * cs.simple i) := by
      rcases Nat.lt_or_eq_of_le hle_ws with hlt | heq
      · exact hlt
      · exfalso; exact hvs_ne_ws (bruhatLE_eq_of_length_eq cs hcase2 (by omega))
    constructor
    · constructor
      · exact bruhatLE_of_step cs ⟨cs.simple i, simple_mem_reflections cs i, rfl, hws_len⟩
      · intro heq; have := congr_arg cs.length heq; omega
    · exact hvs_lt_ws

end CoveringLemma

section ChainProperty
variable {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Existence of an immediate Bruhat predecessor: for any $v < w$ there exists
$u$ with $v \le u < w$ and $\ell(u) + 1 = \ell(w)$. -/
theorem bruhat_predecessor
    (hSEC_full : StrongExchangeCondition cs)
    (hRSP : ReducedSublistProperty cs)
    (hSEC : StrongExchangeForBruhat cs)
    {v w : W} (hvw : BruhatLT cs v w) :
    ∃ u, BruhatLE cs v u ∧ BruhatLT cs u w ∧ cs.length u + 1 = cs.length w := by
  suffices hsuff : ∀ (N : ℕ) {v w : W}, BruhatLT cs v w →
      cs.length v + cs.length w ≤ N →
      ∃ u, BruhatLE cs v u ∧ BruhatLT cs u w ∧ cs.length u + 1 = cs.length w from
    hsuff _ hvw le_rfl
  intro N
  induction N with
  | zero =>
    intro v w hvw hN; exfalso
    have hlt : cs.length v < cs.length w := by
      rcases Nat.lt_or_eq_of_le (bruhatLE_length_le cs hvw.1) with h | h
      · exact h
      · exact absurd (bruhatLE_eq_of_length_eq cs hvw.1 h) hvw.2
    omega
  | succ N ih =>
    intro v w hvw hN
    have hw_ne_one : w ≠ 1 := by
      intro h; rw [h] at hvw
      have := bruhatLE_length_le cs hvw.1
      rw [cs.length_one] at this
      exact hvw.2 (cs.length_eq_zero_iff.mp (Nat.le_zero.mp this))
    obtain ⟨ω, hω_red, hω_prod⟩ := cs.exists_isReduced w
    have hω_ne : ω ≠ [] := by
      intro h; subst h; simp [cs.wordProd_nil] at hω_prod; exact hw_ne_one hω_prod
    obtain ⟨ω', sn, hω_split⟩ : ∃ (ω' : List B) (sn : B), ω = ω' ++ [sn] :=
      ⟨ω.dropLast, ω.getLast hω_ne, (List.dropLast_append_getLast hω_ne).symm⟩
    set w' := cs.wordProd ω' with hw'_def
    have hω_red' : cs.IsReduced (ω' ++ [sn]) := hω_split ▸ hω_red
    have hω'_red : cs.IsReduced ω' := by
      have : ω' = (ω' ++ [sn]).take ω'.length := by simp
      rw [this]; exact hω_red'.take _
    have hprod_split : cs.wordProd (ω' ++ [sn]) = w' * cs.simple sn := by
      rw [← List.concat_eq_append, cs.wordProd_concat]
    have hw_eq : w = w' * cs.simple sn := by rw [hω_prod, hω_split, hprod_split]
    have hw'_len : cs.length w' + 1 = cs.length w := by
      have h1 : cs.length w = (ω' ++ [sn]).length := by
        rw [hω_prod, hω_split]; exact hω_red'
      rw [List.length_append, List.length_singleton] at h1
      have h2 : cs.length w' = ω'.length := hω'_red
      omega
    have hw'_lt_w : BruhatLT cs w' w := by
      constructor
      · rw [hw_eq]
        exact bruhatLE_of_step cs ⟨cs.simple sn, simple_mem_reflections cs sn, rfl, by
          rw [← hw_eq]; omega⟩
      · intro heq; subst heq; omega

    obtain ⟨σ, hσ_sub, hσ_eq⟩ : ∃ σ, σ.Sublist (ω' ++ [sn]) ∧ v = cs.wordProd σ :=
      bruhatLE_subexpression_forward cs hSEC_full hRSP hvw.1
        (hω_split ▸ hω_red) (by rw [hω_prod, hω_split])
    rcases sublist_concat_cases σ ω' sn hσ_sub with hcase1 | ⟨σ', hσ'_split, hσ'_sub⟩
    ·
      exact ⟨w',
        subexpression_bruhatLE_backward cs hSEC hω'_red hw'_def.symm hcase1 hσ_eq,
        hw'_lt_w, hw'_len⟩
    ·
      set v' := cs.wordProd σ' with hv'_def
      have hv_split : v = v' * cs.simple sn := by
        rw [hσ_eq, hσ'_split, ← List.concat_eq_append, cs.wordProd_concat]
      have hv'_le_w' : BruhatLE cs v' w' :=
        subexpression_bruhatLE_backward cs hSEC hω'_red hw'_def.symm hσ'_sub hv'_def.symm
      rcases bruhat_right_mul cs hSEC hv'_le_w' sn with h1 | h2
      ·
        exact ⟨w', hv_split ▸ h1, hw'_lt_w, hw'_len⟩
      ·
        by_cases hv_desc : cs.IsRightDescent v' sn
        ·
          have hv_le_w' : BruhatLE cs v w' := by
            rw [hv_split]
            have hlt : cs.length (v' * cs.simple sn) < cs.length v' := by
              have := cs.isRightDescent_iff.mp hv_desc; omega
            exact bruhatLE_trans cs
              (bruhatLE_of_step cs (bruhatStep_mul_simple_descent cs sn hlt))
              hv'_le_w'
          exact ⟨w', hv_le_w', hw'_lt_w, hw'_len⟩
        ·
          have hv_len : cs.length (v' * cs.simple sn) = cs.length v' + 1 :=
            cs.not_isRightDescent_iff.mp hv_desc
          have hv'_ne_w' : v' ≠ w' := by
            intro heq; rw [heq] at hv_split; exact hvw.2 (hv_split.trans hw_eq.symm)
          have hv'_lt_w' : BruhatLT cs v' w' := ⟨hv'_le_w', hv'_ne_w'⟩

          have hN' : cs.length v' + cs.length w' ≤ N := by
            have hv_eq_len : cs.length v = cs.length v' + 1 := by
              rw [← hv_split] at hv_len; exact hv_len
            omega
          obtain ⟨u', hv'_le_u', hu'_lt_w', hu'_len⟩ := ih hv'_lt_w' hN'

          rcases bruhat_right_mul cs hSEC hv'_le_u' sn with h3 | h4
          ·
            exact ⟨w', bruhatLE_trans cs (hv_split ▸ h3) hu'_lt_w'.1,
                   hw'_lt_w, hw'_len⟩
          ·

            rcases bruhat_right_mul cs hSEC hu'_lt_w'.1 sn with h5 | h6
            ·
              exact ⟨w', bruhatLE_trans cs (hv_split ▸ h4) h5,
                     hw'_lt_w, hw'_len⟩
            ·
              by_cases hu'_desc : cs.IsRightDescent u' sn
              ·
                have : BruhatLE cs (u' * cs.simple sn) w' := by
                  have hlt : cs.length (u' * cs.simple sn) < cs.length u' := by
                    have := cs.isRightDescent_iff.mp hu'_desc; omega
                  exact bruhatLE_trans cs
                    (bruhatLE_of_step cs (bruhatStep_mul_simple_descent cs sn hlt))
                    hu'_lt_w'.1
                exact ⟨w', bruhatLE_trans cs (hv_split ▸ h4) this,
                       hw'_lt_w, hw'_len⟩
              ·
                have hu'sn_len : cs.length (u' * cs.simple sn) = cs.length u' + 1 :=
                  cs.not_isRightDescent_iff.mp hu'_desc
                have hu'sn_len_eq : cs.length (u' * cs.simple sn) + 1 = cs.length w := by
                  omega
                have hu'sn_ne_w : u' * cs.simple sn ≠ w := by
                  intro heq
                  have : cs.length (u' * cs.simple sn) = cs.length w := by rw [heq]
                  omega
                have hu'sn_le_w : BruhatLE cs (u' * cs.simple sn) w :=
                  bruhatLE_trans cs h6 (hw_eq ▸ bruhatLE_refl cs _)
                exact ⟨u' * cs.simple sn,
                       hv_split ▸ h4,
                       ⟨hu'sn_le_w, hu'sn_ne_w⟩,
                       hu'sn_len_eq⟩

/-- The chain property for the Bruhat order: every strict inequality
$v < w$ extends to a saturated chain $v = u_0 < u_1 < \cdots < u_{n+1} = w$
in which each $\ell(u_{i+1}) = \ell(u_i) + 1$. -/
theorem bruhat_chain_property
    (hSEC_full : StrongExchangeCondition cs)
    (hRSP : ReducedSublistProperty cs)
    (hSEC : StrongExchangeForBruhat cs)
    {v w : W} (hvw : BruhatLT cs v w) :
    ∃ (n : ℕ) (f : Fin (n + 2) → W),
      f ⟨0, by omega⟩ = v ∧
      f ⟨n + 1, by omega⟩ = w ∧
      ∀ (i : Fin (n + 1)),
        BruhatLT cs (f ⟨i.val, by omega⟩) (f ⟨i.val + 1, by omega⟩) ∧
        cs.length (f ⟨i.val, by omega⟩) + 1 =
          cs.length (f ⟨i.val + 1, by omega⟩) := by

  have hlen_diff : cs.length v < cs.length w := by
    rcases Nat.lt_or_eq_of_le (bruhatLE_length_le cs hvw.1) with h | h
    · exact h
    · exact absurd (bruhatLE_eq_of_length_eq cs hvw.1 h) hvw.2
  suffices hsuff : ∀ (d : ℕ) {v w : W},
      BruhatLT cs v w → cs.length w - cs.length v ≤ d →
      ∃ (n : ℕ) (f : Fin (n + 2) → W),
        f ⟨0, by omega⟩ = v ∧
        f ⟨n + 1, by omega⟩ = w ∧
        ∀ (i : Fin (n + 1)),
          BruhatLT cs (f ⟨i.val, by omega⟩) (f ⟨i.val + 1, by omega⟩) ∧
          cs.length (f ⟨i.val, by omega⟩) + 1 =
            cs.length (f ⟨i.val + 1, by omega⟩) from
    hsuff _ hvw le_rfl
  intro d
  induction d with
  | zero =>
    intro v w hvw hd; exfalso
    have hlt : cs.length v < cs.length w := by
      rcases Nat.lt_or_eq_of_le (bruhatLE_length_le cs hvw.1) with h | h
      · exact h
      · exact absurd (bruhatLE_eq_of_length_eq cs hvw.1 h) hvw.2
    omega
  | succ d ih =>
    intro v w hvw hd
    obtain ⟨u, hvu, huw, huw_len⟩ := bruhat_predecessor cs hSEC_full hRSP hSEC hvw
    by_cases hvu_eq : v = u
    ·
      subst hvu_eq
      refine ⟨0, fun j => if j.val = 0 then v else w, rfl, ?_, ?_⟩
      · simp
      · intro ⟨i, hi⟩
        have hi0 : i = 0 := by omega
        subst hi0
        simp [huw, huw_len]
    ·
      have hv_lt_u : BruhatLT cs v u := ⟨hvu, hvu_eq⟩
      have hv_len_lt_u : cs.length v < cs.length u := by
        rcases Nat.lt_or_eq_of_le (bruhatLE_length_le cs hvu) with h | h
        · exact h
        · exact absurd (bruhatLE_eq_of_length_eq cs hvu h) hvu_eq
      have hd' : cs.length u - cs.length v ≤ d := by omega
      obtain ⟨n, f, hf0, hfn, hf_prop⟩ := ih hv_lt_u hd'

      refine ⟨n + 1, fun j => if hj : j.val ≤ n + 1 then f ⟨j.val, by omega⟩ else w, ?_, ?_, ?_⟩
      · show (if (⟨0, by omega⟩ : Fin (n + 3)).val ≤ n + 1 then f ⟨0, by omega⟩ else w) = v
        simp only [show (0 : ℕ) ≤ n + 1 from Nat.zero_le _]
        exact hf0
      · simp [show ¬(n + 2 ≤ n + 1) from by omega]
      · intro ⟨i, hi⟩
        by_cases hi_le : i ≤ n
        ·
          have hi1 : i ≤ n + 1 := by omega
          have hi2 : i + 1 ≤ n + 1 := by omega
          simp only [hi1, hi2, dite_true]
          exact hf_prop ⟨i, by omega⟩
        ·
          have hi_eq : i = n + 1 := by omega
          subst hi_eq
          simp only [show (n + 1 : ℕ) ≤ n + 1 from le_refl _, dite_true,
                      show ¬(n + 2 ≤ n + 1) from by omega, dite_false]
          rw [hfn]
          exact ⟨huw, huw_len⟩

end ChainProperty

end CoxeterBruhat
