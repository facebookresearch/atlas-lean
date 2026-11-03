/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.TitsCone
import Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
import Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Atlas.Buildings.code.CoxeterGroup.UnconditionalExchange
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Set.Finite.List

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Finset BigOperators CoxeterGroup TitsCone

namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The iterated dual-sigma word action: applying $\sigma_{s_1}^* \sigma_{s_2}^* \cdots$
in left-to-right order. This is the "co-action" version of the reflection action. -/
noncomputable def wordAction (M : CoxeterMatrix B) (ws : List B) (y : B → ℝ) : B → ℝ :=
  ws.foldl (fun v s => dualSigma M s v) y

/-- The empty word acts as the identity. -/
@[simp] theorem wordAction_nil (M : CoxeterMatrix B) (y : B → ℝ) :
    wordAction M [] y = y := rfl

/-- Cons step: prepending $s$ to the word means first applying the dual sigma at $s$. -/
theorem wordAction_cons (M : CoxeterMatrix B) (s : B) (ws : List B) (y : B → ℝ) :
    wordAction M (s :: ws) y = wordAction M ws (dualSigma M s y) :=
  List.foldl_cons ..

/-- Concatenation: the word action is the composition $\sigma^*_{ws_2} \circ \sigma^*_{ws_1}$. -/
theorem wordAction_append (M : CoxeterMatrix B) (ws₁ ws₂ : List B) (y : B → ℝ) :
    wordAction M (ws₁ ++ ws₂) y = wordAction M ws₂ (wordAction M ws₁ y) :=
  List.foldl_append ..

/-- Singleton word action: $\sigma^*_s$ applied to $y$. -/
theorem wordAction_singleton (M : CoxeterMatrix B) (s : B) (y : B → ℝ) :
    wordAction M [s] y = dualSigma M s y := rfl

/-- Applying the reverse word cancels: $\sigma^*_{\overline{ws}} \circ \sigma^*_{ws} = \mathrm{id}$. -/
theorem wordAction_reverse_cancel (M : CoxeterMatrix B) (ws : List B) (y : B → ℝ) :
    wordAction M ws.reverse (wordAction M ws y) = y := by
  induction ws generalizing y with
  | nil => rfl
  | cons s ws ih =>
    rw [wordAction_cons, List.reverse_cons, wordAction_append, wordAction_singleton]
    rw [ih]; exact dualSigma_involutive M s y

/-- Symmetric cancellation: $\sigma^*_{ws} \circ \sigma^*_{\overline{ws}} = \mathrm{id}$. -/
theorem wordAction_cancel_reverse (M : CoxeterMatrix B) (ws : List B) (y : B → ℝ) :
    wordAction M ws (wordAction M ws.reverse y) = y := by
  have h := wordAction_reverse_cancel M ws.reverse y
  rwa [List.reverse_reverse] at h

/-- $\sigma^*_s$ is $\mathbb{R}$-linear in the input. -/
theorem dualSigma_linear (M : CoxeterMatrix B) (s : B) (a b : ℝ) (x y : B → ℝ) :
    dualSigma M s (fun t => a * x t + b * y t) =
    fun t => a * dualSigma M s x t + b * dualSigma M s y t := by
  ext t; simp only [dualSigma]; ring

/-- The iterated word action is $\mathbb{R}$-linear: composition of linear maps. -/
theorem wordAction_linear (M : CoxeterMatrix B) (ws : List B) (a b : ℝ) (x y : B → ℝ) :
    wordAction M ws (fun t => a * x t + b * y t) =
    fun t => a * wordAction M ws x t + b * wordAction M ws y t := by
  induction ws generalizing x y with
  | nil => simp [wordAction]
  | cons s ws ih => rw [wordAction_cons, dualSigma_linear, wordAction_cons, wordAction_cons]; exact ih ..

/-- The Tits cone is closed under the dual word action: $\sigma^*_w$ sends
$\mathcal U$ to itself. -/
theorem titsConeSet_wordAction_closed (M : CoxeterMatrix B) (ws : List B) (x : B → ℝ)
    (hx : x ∈ titsConeSet M) : wordAction M ws x ∈ titsConeSet M := by
  obtain ⟨y, hy, ws', rfl⟩ := hx
  exact ⟨y, hy, ws' ++ ws, (wordAction_append M ws' ws y).symm⟩

/-- The simple reflection $\sigma_s^*$ fixes any vector lying on the wall
$\nu_s = 0$. -/
theorem dualSigma_fixed_on_wall (M : CoxeterMatrix B) (s : B) (ν : B → ℝ)
    (hν : ν s = 0) : dualSigma M s ν = ν := by
  ext t; simp only [dualSigma]; rw [hν]; ring

/-- Transpose identity: $\langle \sigma_s^* y, v\rangle = \langle y, \sigma_s v\rangle$,
expressing that $\sigma$ and $\sigma^*$ are mutually adjoint. -/
theorem dualSigma_sigma_transpose (M : CoxeterMatrix B) (s : B) (y v : B → ℝ) :
    ∑ t : B, (dualSigma M s y) t * v t = ∑ t : B, y t * (sigma M s v) t := by

  simp only [dualSigma, sigma]

  have hbf : bilinForm M v (e s) = ∑ i : B, v i * formVal M i s := by
    simp only [bilinForm]
    congr 1; ext i
    rw [Finset.sum_eq_single s]
    · simp [e, Pi.single]
    · intro j _ hj; simp [e, Pi.single, hj]
    · intro h; exact absurd (Finset.mem_univ s) h
  rw [hbf]


  have lhs_eq : ∑ t : B, (y t - 2 * y s * formVal M s t) * v t =
      ∑ t : B, y t * v t - 2 * y s * ∑ t : B, formVal M s t * v t := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1; ext t; ring
  have rhs_eq : ∑ t : B, y t * (v t - 2 * (∑ i : B, v i * formVal M i s) * (e s) t) =
      ∑ t : B, y t * v t - 2 * y s * ∑ i : B, v i * formVal M i s := by

    have : ∑ t : B, y t * (v t - 2 * (∑ i : B, v i * formVal M i s) * (e s) t) =
        ∑ t : B, (y t * v t - y t * (2 * (∑ i : B, v i * formVal M i s) * (e s) t)) := by
      congr 1; ext t; ring
    rw [this, Finset.sum_sub_distrib]
    congr 1

    have sum_indicator : ∑ t : B, y t * (2 * (∑ i : B, v i * formVal M i s) * (e s) t) =
        2 * y s * ∑ i : B, v i * formVal M i s := by
      rw [show (2 : ℝ) * y s * ∑ i : B, v i * formVal M i s =
          y s * (2 * (∑ i : B, v i * formVal M i s) * 1) by ring]
      rw [Finset.sum_eq_single s]
      · simp [e, Pi.single]
      · intro t _ ht; simp [e, Pi.single, ht]
      · intro h; exact absurd (Finset.mem_univ s) h
    exact sum_indicator
  rw [lhs_eq, rhs_eq]
  congr 1
  congr 1
  congr 1; ext t
  rw [formVal_symm M s t]; ring

/-- Coordinate formula via transpose: $(\sigma^*_w y)(s) = \sum_t y_t \cdot
(\sigma_w e_s)_t$. -/
theorem wordAction_transpose (M : CoxeterMatrix B) (ws : List B) (y : B → ℝ) (s : B) :
    wordAction M ws y s = ∑ t : B, y t * wordSigma M ws (e s) t := by
  induction ws generalizing y with
  | nil =>
    simp only [wordAction, wordSigma]


    simp only [e, Pi.single, Function.update, eq_comm]
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ ht; simp [show s ≠ t from Ne.symm ht]
    · intro h; exact absurd (Finset.mem_univ s) h
  | cons a rest ih =>
    rw [wordAction_cons, ih, wordSigma_cons]
    exact dualSigma_sigma_transpose M a y (wordSigma M rest (e s))

/-- The word action depends only on the group element $\mathrm{wordProd}(ws)$, not
on the word: two words representing the same Coxeter group element induce the
same dual word action. -/
theorem wordAction_eq_of_wordProd_eq (M : CoxeterMatrix B)
    (ws₁ ws₂ : List B) (h : M.toCoxeterSystem.wordProd ws₁ = M.toCoxeterSystem.wordProd ws₂)
    (y : B → ℝ) :
    wordAction M ws₁ y = wordAction M ws₂ y := by
  ext s
  rw [wordAction_transpose, wordAction_transpose]
  congr 1; ext t; congr 1
  exact congr_fun (wordSigma_eq_of_wordProd_eq M M.toCoxeterSystem ws₁ ws₂ h (e s)) t

/-- Descent detection: if the dual word action sends a nonnegative vector to a
vector with a negative $s$-coordinate, then $s$ is a right descent of the group
element $\mathrm{wordProd}(ws)$. -/
theorem isRightDescent_of_wordAction_neg (M : CoxeterMatrix B)
    (ws : List B) (y : B → ℝ) (hy : ∀ t, y t ≥ 0) (s : B)
    (hneg : wordAction M ws y s < 0) :
    M.toCoxeterSystem.IsRightDescent (M.toCoxeterSystem.wordProd ws) s := by
  set cs := M.toCoxeterSystem
  by_contra hasc_neg
  rw [CoxeterSystem.IsRightDescent] at hasc_neg
  push_neg at hasc_neg

  have hasc : cs.length (cs.wordProd ws * cs.simple s) > cs.length (cs.wordProd ws) := by
    have := cs.length_mul_simple (cs.wordProd ws) s; omega

  obtain ⟨rw, hrw_red, hrw_prod⟩ := cs.exists_reduced_word (cs.wordProd ws)

  have hrw_asc : cs.length (cs.wordProd rw * cs.simple s) > cs.length (cs.wordProd rw) := by
    rw [← hrw_prod]; exact hasc
  have hpos := CoxeterGroup.pos_of_ascent M cs rw s hrw_red hrw_asc

  have hσeq : ∀ t, wordSigma M ws (e s) t = wordSigma M rw (e s) t := by
    intro t
    exact congr_fun (wordSigma_eq_of_wordProd_eq M cs ws rw hrw_prod (e s)) t

  rw [wordAction_transpose] at hneg
  have hge : ∑ t : B, y t * wordSigma M ws (e s) t ≥ 0 :=
    Finset.sum_nonneg (fun t _ => mul_nonneg (hy t) (by rw [hσeq t]; exact hpos t))
  linarith

/-- Geometric exchange condition: when $(\sigma^*_w y)(s) < 0$ for $y \ge 0$,
the vector $\sigma_s^*(\sigma^*_w y)$ can be re-expressed via a shorter word $ws'$,
shrinking word length via the strong exchange property. -/
theorem exchange_condition (M : CoxeterMatrix B) :
  ∀ (ws : List B) (y : B → ℝ), (∀ s, y s ≥ 0) →
  ∀ (s : B), wordAction M ws y s < 0 →
  ∃ (ws' : List B) (y' : B → ℝ),
    ws'.length < ws.length ∧ (∀ s, y' s ≥ 0) ∧
    dualSigma M s (wordAction M ws y) = wordAction M ws' y' := by
  intro ws y hy s hneg
  set cs := M.toCoxeterSystem

  have hdesc := isRightDescent_of_wordAction_neg M ws y hy s hneg

  have hdesc_len : cs.length (cs.wordProd ws * cs.simple s) < cs.length (cs.wordProd ws) := hdesc

  obtain ⟨rw_word, hrw_red, hrw_prod⟩ := cs.exists_reduced_word (cs.wordProd ws)


  have hrw_len : rw_word.length = cs.length (cs.wordProd ws) := by
    rw [hrw_prod]; exact hrw_red.eq.symm

  have hrw_desc : cs.length (cs.wordProd rw_word * cs.simple s) < cs.length (cs.wordProd rw_word) := by
    rwa [← hrw_prod]

  obtain ⟨i, hi_prod, _⟩ := StrongExchangeBridge.exchange_descent_eraseIdx_unconditional rw_word s hrw_red hrw_desc


  set ws' := rw_word.eraseIdx i

  have hlen_ws' : ws'.length < ws.length := by
    have hlen_erase : ws'.length = rw_word.length - 1 := List.length_eraseIdx_of_lt i.isLt
    have hlen_ws_ge : cs.length (cs.wordProd ws) ≤ ws.length := cs.length_wordProd_le ws
    have hrw_pos : rw_word.length ≥ 1 := by
      by_contra h
      push_neg at h
      have hrw_zero : rw_word.length = 0 := Nat.lt_one_iff.mp h
      have : rw_word = [] := List.eq_nil_of_length_eq_zero hrw_zero
      subst this
      simp [CoxeterSystem.wordProd_nil] at hrw_prod
      rw [hrw_prod] at hdesc_len
      simp [CoxeterSystem.length_one, CoxeterSystem.length_simple] at hdesc_len
    omega


  have hprod_wss : cs.wordProd (ws ++ [s]) = cs.wordProd ws * cs.simple s := by
    rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one]
  have hprod_eq : cs.wordProd (ws ++ [s]) = cs.wordProd ws' := by
    rw [hprod_wss, hrw_prod, hi_prod]

  have haction_eq : dualSigma M s (wordAction M ws y) = wordAction M (ws ++ [s]) y := by
    rw [← wordAction_singleton, ← wordAction_append]
  have haction_inv : wordAction M (ws ++ [s]) y = wordAction M ws' y :=
    wordAction_eq_of_wordProd_eq M (ws ++ [s]) ws' hprod_eq y

  exact ⟨ws', y, hlen_ws', hy, by rw [haction_eq, haction_inv]⟩

/-- The wall parameter $t_0 = \min_{s \in \mathrm{neg\_set}} \frac{x_s}{x_s - \mu_s}$:
the smallest $t \in [0,1]$ for which the convex combination $(1-t)x + t\mu$ reaches
the wall $\{z : z_s = 0\}$ for some $s$. -/
noncomputable def wallParam (x μ : B → ℝ) (neg_set : Finset B)
    (hne : neg_set.Nonempty) (hx : ∀ s, x s ≥ 0) (hμ : ∀ s ∈ neg_set, μ s < 0) : ℝ :=
  (neg_set.image (fun s => x s / (x s - μ s))).min' (hne.image _)

/-- The wall parameter is the minimum over the negative set, so it bounds each
individual ratio. -/
theorem wallParam_le_ratio (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ : ∀ s ∈ neg_set, μ s < 0) (s : B) (hs : s ∈ neg_set) :
    wallParam x μ neg_set hne hx hμ ≤ x s / (x s - μ s) :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)

/-- The wall parameter is attained: some $s_0 \in \mathrm{neg\_set}$ realises the
minimum ratio $x_{s_0} / (x_{s_0} - \mu_{s_0})$. -/
theorem wallParam_eq_some_ratio (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ : ∀ s ∈ neg_set, μ s < 0) :
    ∃ s₀ ∈ neg_set, wallParam x μ neg_set hne hx hμ = x s₀ / (x s₀ - μ s₀) := by
  have := Finset.min'_mem (neg_set.image (fun s => x s / (x s - μ s))) (hne.image _)
  rw [Finset.mem_image] at this
  obtain ⟨s₀, hs₀, heq⟩ := this
  exact ⟨s₀, hs₀, heq.symm⟩

/-- The wall parameter is nonnegative, since each individual ratio is. -/
theorem wallParam_nonneg (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ : ∀ s ∈ neg_set, μ s < 0) :
    0 ≤ wallParam x μ neg_set hne hx hμ := by
  apply Finset.le_min'
  intro r hr
  rw [Finset.mem_image] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  exact div_nonneg (hx s) (by linarith [hμ s hs, hx s])

/-- The wall parameter lies in $[0, 1]$: for each $s$ in the negative set
$x_s / (x_s - \mu_s) \le 1$ since $\mu_s < 0$. -/
theorem wallParam_le_one (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ : ∀ s ∈ neg_set, μ s < 0) :
    wallParam x μ neg_set hne hx hμ ≤ 1 := by
  have ⟨s₀, hs₀⟩ := hne
  calc wallParam x μ neg_set hne hx hμ
      ≤ x s₀ / (x s₀ - μ s₀) := wallParam_le_ratio x μ neg_set hne hx hμ s₀ hs₀
    _ ≤ 1 := by rw [div_le_one (by linarith [hμ s₀ hs₀, hx s₀])]; linarith [hμ s₀ hs₀]

/-- The wall point $(1-t_0)\,x + t_0\,\mu$ at the wall parameter has nonnegative
coordinates at every $s'$: at indices in the negative set the choice of $t_0$
keeps the coordinate $\ge 0$; at others both summands are nonnegative. -/
theorem wallPoint_nonneg (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ_neg : ∀ s ∈ neg_set, μ s < 0) (hμ_pos : ∀ s, s ∉ neg_set → μ s ≥ 0)
    (s' : B) :
    let t₀ := wallParam x μ neg_set hne hx hμ_neg
    (1 - t₀) * x s' + t₀ * μ s' ≥ 0 := by
  simp only
  set t₀ := wallParam x μ neg_set hne hx hμ_neg
  have ht₀_nn := wallParam_nonneg x μ neg_set hne hx hμ_neg
  have ht₀_le1 := wallParam_le_one x μ neg_set hne hx hμ_neg
  by_cases hs' : s' ∈ neg_set
  · have hd : x s' - μ s' > 0 := by linarith [hx s', hμ_neg s' hs']
    have ht₀_le : t₀ ≤ x s' / (x s' - μ s') := wallParam_le_ratio x μ neg_set hne hx hμ_neg s' hs'
    have : t₀ * (x s' - μ s') ≤ x s' := by
      calc t₀ * (x s' - μ s') ≤ x s' / (x s' - μ s') * (x s' - μ s') :=
              mul_le_mul_of_nonneg_right ht₀_le (le_of_lt hd)
        _ = x s' := div_mul_cancel₀ (x s') (ne_of_gt hd)
    linarith
  · apply add_nonneg
    · exact mul_nonneg (by linarith) (hx s')
    · exact mul_nonneg ht₀_nn (hμ_pos s' hs')

/-- The wall point hits zero at the minimising index: some $s_0$ has wall-point
coordinate equal to $0$. -/
theorem wallPoint_zero (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ_neg : ∀ s ∈ neg_set, μ s < 0) :
    ∃ s₀ ∈ neg_set,
      let t₀ := wallParam x μ neg_set hne hx hμ_neg
      (1 - t₀) * x s₀ + t₀ * μ s₀ = 0 := by
  obtain ⟨s₀, hs₀, ht₀_eq⟩ := wallParam_eq_some_ratio x μ neg_set hne hx hμ_neg
  refine ⟨s₀, hs₀, ?_⟩
  have hd : x s₀ - μ s₀ > 0 := by linarith [hx s₀, hμ_neg s₀ hs₀]
  simp only [ht₀_eq]
  field_simp
  ring

/-- Strong induction on word length: any convex combination of $x \in \mathcal D_0$
and $\sigma^*_w y$ (with $y$ nonneg) lies in the Tits cone. This is the key step
of convexity; the wall-parameter / exchange-condition machinery shrinks $|w|$. -/
theorem convex_closure_titsCone (M : CoxeterMatrix B) :
    ∀ (n : ℕ),
    ∀ (ws : List B), ws.length ≤ n →
    ∀ (y : B → ℝ), (∀ s, y s ≥ 0) →
    ∀ (x : B → ℝ), (∀ s, x s ≥ 0) →
    ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
    (fun t => a * x t + b * wordAction M ws y t) ∈ titsConeSet M := by
  intro n
  induction n with
  | zero =>
    intro ws hlen y hy x hx a b ha hb hab
    have : ws = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst this; simp only [wordAction_nil]
    exact ⟨_, fun s => add_nonneg (mul_nonneg ha (hx s)) (mul_nonneg hb (hy s)), [], rfl⟩
  | succ n ih =>
    intro ws hlen y hy x hx a b ha hb hab
    set μ := wordAction M ws y with μ_def

    by_cases h_nn : ∀ s, a * x s + b * μ s ≥ 0
    · exact ⟨_, h_nn, [], rfl⟩
    · push_neg at h_nn
      obtain ⟨s_bad, hs_bad⟩ := h_nn

      have hμ_bad : μ s_bad < 0 := by
        by_contra h; push_neg at h
        linarith [mul_nonneg ha (hx s_bad), mul_nonneg hb h]

      have hb_pos : 0 < b := by
        by_contra h; push_neg at h
        have := le_antisymm h hb; subst this
        simp at hs_bad; linarith [mul_nonneg ha (hx s_bad)]

      set neg_set := Finset.univ.filter (fun s => μ s < 0) with neg_set_def
      have hne : neg_set.Nonempty := ⟨s_bad, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hμ_bad⟩⟩
      have hμ_neg : ∀ s ∈ neg_set, μ s < 0 := fun s hs => (Finset.mem_filter.mp hs).2
      have hμ_pos : ∀ s, s ∉ neg_set → μ s ≥ 0 := by
        intro s hs; rw [neg_set_def, Finset.mem_filter, not_and] at hs
        exact not_lt.mp (hs (Finset.mem_univ s))

      set t₀ := wallParam x μ neg_set hne hx hμ_neg
      have ht₀_nn := wallParam_nonneg x μ neg_set hne hx hμ_neg
      have ht₀_le1 := wallParam_le_one x μ neg_set hne hx hμ_neg

      set ν := fun t => (1 - t₀) * x t + t₀ * μ t with ν_def
      have hν_nn : ∀ s', ν s' ≥ 0 :=
        wallPoint_nonneg x μ neg_set hne hx hμ_neg hμ_pos

      obtain ⟨s₀, hs₀_mem, hν_zero⟩ := wallPoint_zero x μ neg_set hne hx hμ_neg
      have hμs₀ : μ s₀ < 0 := hμ_neg s₀ hs₀_mem

      have hb_gt_t₀ : t₀ < b := by
        by_contra h; push_neg at h


        have hd : x s_bad - μ s_bad > 0 := by linarith [hx s_bad]
        have : a * x s_bad + b * μ s_bad ≥ ν s_bad := by
          simp only [ν_def]; have ha_eq : a = 1 - b := by linarith
          rw [ha_eq]; nlinarith
        linarith [hν_nn s_bad]

      have ht₀_lt1 : t₀ < 1 := by linarith

      obtain ⟨ws', y', hlen', hy', hσ⟩ := exchange_condition M ws y hy s₀ hμs₀

      set c := (b - t₀) / (1 - t₀) with c_def
      have hc_nn : 0 ≤ c := div_nonneg (by linarith) (by linarith)
      have hc_le1 : c ≤ 1 := by rw [c_def, div_le_one (by linarith)]; linarith

      have hz_eq : (fun t => a * x t + b * μ t) = (fun t => (1 - c) * ν t + c * μ t) := by
        have h1t : (1 : ℝ) - t₀ ≠ 0 := by linarith
        ext t; simp only [ν_def, c_def]
        have ha_eq : a = 1 - b := by linarith
        rw [ha_eq]; field_simp; ring
      rw [hz_eq]

      have hσ_linear : dualSigma M s₀ (fun t => (1 - c) * ν t + c * μ t) =
          fun t => (1 - c) * ν t + c * (wordAction M ws' y') t := by
        rw [dualSigma_linear, dualSigma_fixed_on_wall M s₀ ν hν_zero, hσ]

      have h_refl_in_U :
          (fun t => (1 - c) * ν t + c * (wordAction M ws' y') t) ∈ titsConeSet M := by
        exact ih ws' (by omega) y' hy' ν hν_nn (1 - c) c (by linarith) hc_nn (by ring)


      have hσ_inv : dualSigma M s₀ (wordAction M ws' y') = μ := by
        rw [← hσ, dualSigma_involutive]
      have hinv : dualSigma M s₀ (fun t => (1 - c) * ν t + c * (wordAction M ws' y') t) =
          fun t => (1 - c) * ν t + c * μ t := by
        rw [dualSigma_linear, dualSigma_fixed_on_wall M s₀ ν hν_zero, hσ_inv]

      have h_in_U : (fun t => (1 - c) * ν t + c * μ t) ∈ titsConeSet M := by
        rw [← hinv]
        exact titsConeSet_wordAction_closed M [s₀] _ h_refl_in_U
      exact h_in_U

/-- Bounded version of convex_closure_titsCone: not only does the convex
combination lie in $\mathcal U$, but it is realised as $\sigma^*_{ws'} y'$ with
word length bounded by the input bound $n$. -/
theorem convex_closure_titsCone_bounded (M : CoxeterMatrix B) :
    ∀ (n : ℕ),
    ∀ (ws : List B), ws.length ≤ n →
    ∀ (y : B → ℝ), (∀ s, y s ≥ 0) →
    ∀ (x : B → ℝ), (∀ s, x s ≥ 0) →
    ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
    ∃ (ws' : List B) (y' : B → ℝ),
      (∀ s, y' s ≥ 0) ∧ ws'.length ≤ n ∧
      (fun t => a * x t + b * wordAction M ws y t) = wordAction M ws' y' := by
  intro n
  induction n with
  | zero =>
    intro ws hlen y hy x hx a b ha hb hab
    have : ws = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst this; simp only [wordAction_nil]
    exact ⟨[], fun s => a * x s + b * y s,
           fun s => add_nonneg (mul_nonneg ha (hx s)) (mul_nonneg hb (hy s)),
           Nat.zero_le 0, rfl⟩
  | succ n ih =>
    intro ws hlen y hy x hx a b ha hb hab
    set μ := wordAction M ws y with μ_def
    by_cases h_nn : ∀ s, a * x s + b * μ s ≥ 0
    · exact ⟨[], fun s => a * x s + b * μ s, h_nn, Nat.zero_le _, rfl⟩
    · push_neg at h_nn
      obtain ⟨s_bad, hs_bad⟩ := h_nn
      have hμ_bad : μ s_bad < 0 := by
        by_contra h; push_neg at h
        linarith [mul_nonneg ha (hx s_bad), mul_nonneg hb h]
      have hb_pos : 0 < b := by
        by_contra h; push_neg at h
        have := le_antisymm h hb; subst this
        simp at hs_bad; linarith [mul_nonneg ha (hx s_bad)]
      set neg_set := Finset.univ.filter (fun s => μ s < 0) with neg_set_def
      have hne : neg_set.Nonempty := ⟨s_bad, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hμ_bad⟩⟩
      have hμ_neg : ∀ s ∈ neg_set, μ s < 0 := fun s hs => (Finset.mem_filter.mp hs).2
      have hμ_pos : ∀ s, s ∉ neg_set → μ s ≥ 0 := by
        intro s hs; rw [neg_set_def, Finset.mem_filter, not_and] at hs
        exact not_lt.mp (hs (Finset.mem_univ s))
      set t₀ := wallParam x μ neg_set hne hx hμ_neg
      have ht₀_nn := wallParam_nonneg x μ neg_set hne hx hμ_neg
      have ht₀_le1 := wallParam_le_one x μ neg_set hne hx hμ_neg
      set ν := fun t => (1 - t₀) * x t + t₀ * μ t with ν_def
      have hν_nn : ∀ s', ν s' ≥ 0 :=
        wallPoint_nonneg x μ neg_set hne hx hμ_neg hμ_pos
      obtain ⟨s₀, hs₀_mem, hν_zero⟩ := wallPoint_zero x μ neg_set hne hx hμ_neg
      have hμs₀ : μ s₀ < 0 := hμ_neg s₀ hs₀_mem
      have hb_gt_t₀ : t₀ < b := by
        by_contra h; push_neg at h
        have hd : x s_bad - μ s_bad > 0 := by linarith [hx s_bad]
        have : a * x s_bad + b * μ s_bad ≥ ν s_bad := by
          simp only [ν_def]; have ha_eq : a = 1 - b := by linarith
          rw [ha_eq]; nlinarith
        linarith [hν_nn s_bad]
      have ht₀_lt1 : t₀ < 1 := by linarith
      obtain ⟨ws_ex, y_ex, hlen_ex, hy_ex, hσ⟩ := exchange_condition M ws y hy s₀ hμs₀
      set c := (b - t₀) / (1 - t₀) with c_def
      have hc_nn : 0 ≤ c := div_nonneg (by linarith) (by linarith)
      have hc_le1 : c ≤ 1 := by rw [c_def, div_le_one (by linarith)]; linarith
      have hz_eq : (fun t => a * x t + b * μ t) = (fun t => (1 - c) * ν t + c * μ t) := by
        have h1t : (1 : ℝ) - t₀ ≠ 0 := by linarith
        ext t; simp only [ν_def, c_def]
        have ha_eq : a = 1 - b := by linarith
        rw [ha_eq]; field_simp; ring

      have hlen_ex_n : ws_ex.length ≤ n := by omega
      obtain ⟨ws_ih, y_ih, hy_ih, hlen_ih, heq_ih⟩ :=
        ih ws_ex hlen_ex_n y_ex hy_ex ν hν_nn (1 - c) c (by linarith) hc_nn (by ring)


      have hσ_inv : dualSigma M s₀ (wordAction M ws_ex y_ex) = μ := by
        rw [← hσ, dualSigma_involutive]
      have hinv : dualSigma M s₀ (fun t => (1 - c) * ν t + c * (wordAction M ws_ex y_ex) t) =
          fun t => (1 - c) * ν t + c * μ t := by
        rw [dualSigma_linear, dualSigma_fixed_on_wall M s₀ ν hν_zero, hσ_inv]


      have hσ_eq : dualSigma M s₀ (wordAction M ws_ih y_ih) =
          wordAction M (ws_ih ++ [s₀]) y_ih := by
        rw [wordAction_append, wordAction_singleton]
      rw [hz_eq]
      refine ⟨ws_ih ++ [s₀], y_ih, hy_ih, ?_, ?_⟩
      ·
        rw [List.length_append, List.length_singleton]
        omega
      ·
        conv_lhs => rw [show (fun t => (1 - c) * ν t + c * μ t) =
          dualSigma M s₀ (fun t => (1 - c) * ν t + c * (wordAction M ws_ex y_ex) t)
          from hinv.symm]
        rw [heq_ih, hσ_eq]

/-- The Tits cone $\mathcal U \subset (B \to \mathbb R)$ is convex. -/
theorem titsConeSet_convex (M : CoxeterMatrix B) :
    Convex ℝ (titsConeSet M) := by
  intro p hp q hq a b ha hb hab

  obtain ⟨y₁, hy₁, ws₁, hp_eq⟩ := hp
  obtain ⟨y₂, hy₂, ws₂, hq_eq⟩ := hq

  have hp' : p = wordAction M ws₁ y₁ := hp_eq
  have hq' : q = wordAction M ws₂ y₂ := hq_eq
  subst hp'; subst hq'

  have key : (fun t => a * y₁ t + b * wordAction M (ws₂ ++ ws₁.reverse) y₂ t) ∈ titsConeSet M :=
    convex_closure_titsCone M (ws₂ ++ ws₁.reverse).length (ws₂ ++ ws₁.reverse) (le_refl _)
      y₂ hy₂ y₁ hy₁ a b ha hb hab

  have hmapped := titsConeSet_wordAction_closed M ws₁ _ key

  show a • wordAction M ws₁ y₁ + b • wordAction M ws₂ y₂ ∈ titsConeSet M
  have heq : a • wordAction M ws₁ y₁ + b • wordAction M ws₂ y₂ =
      wordAction M ws₁ (fun t => a * y₁ t + b * wordAction M (ws₂ ++ ws₁.reverse) y₂ t) := by
    rw [wordAction_linear]
    have cancel_y₂ : wordAction M ws₁ (wordAction M (ws₂ ++ ws₁.reverse) y₂) =
        wordAction M ws₂ y₂ := by
      rw [wordAction_append]
      exact wordAction_cancel_reverse M ws₁ (wordAction M ws₂ y₂)
    ext t; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [congr_fun cancel_y₂.symm t]
  rw [heq]; exact hmapped

/-- Scalar compatibility of $\sigma^*_s$: $\sigma^*_s(c \cdot x) = c \cdot \sigma^*_s(x)$. -/
theorem dualSigma_smul (M : CoxeterMatrix B) (s : B) (c : ℝ) (x : B → ℝ) :
    dualSigma M s (fun t => c * x t) = fun t => c * dualSigma M s x t := by
  ext t
  simp only [dualSigma]
  ring

/-- Scalar compatibility of the iterated word action: $\sigma^*_w(c \cdot x) = c \cdot \sigma^*_w(x)$. -/
theorem wordAction_smul (M : CoxeterMatrix B) (ws : List B) (c : ℝ) (x : B → ℝ) :
    wordAction M ws (fun t => c * x t) = fun t => c * wordAction M ws x t := by
  induction ws generalizing x with
  | nil => simp [wordAction]
  | cons s ws ih =>
    rw [wordAction_cons, dualSigma_smul, wordAction_cons]
    exact ih ..

/-- The Tits cone $\mathcal U$ is closed under nonnegative scaling: if $x \in \mathcal U$ and $c \ge 0$ then $c \cdot x \in \mathcal U$. -/
theorem titsConeSet_cone (M : CoxeterMatrix B) (x : B → ℝ) (hx : x ∈ titsConeSet M)
    (c : ℝ) (hc : 0 ≤ c) : c • x ∈ titsConeSet M := by
  obtain ⟨y, hy, ws, rfl⟩ := hx
  refine ⟨fun t => c * y t, fun s => mul_nonneg hc (hy s), ws, ?_⟩
  show c • wordAction M ws y = wordAction M ws (fun t => c * y t)
  rw [wordAction_smul]
  ext t; simp [Pi.smul_apply, smul_eq_mul]

/-- Existence in the fundamental domain: every $x \in \mathcal U$ is $\sigma^*_w$-image of some
$y$ in the closed fundamental chamber $\overline{C}$. -/
theorem fundamental_domain_existence (M : CoxeterMatrix B) (x : B → ℝ)
    (hx : x ∈ titsConeSet M) :
    ∃ (ws : List B) (y : B → ℝ), y ∈ titsFundamentalClosure M ∧
      x = wordAction M ws y := by
  obtain ⟨y, hy, ws, rfl⟩ := hx; exact ⟨ws, y, hy, rfl⟩

/-- The face $w \cdot F_I = \sigma^*_w(F_I)$: image of the standard face indexed by $I \subseteq S$
under the word action of $w$. -/
def wordFace (M : CoxeterMatrix B) (ws : List B) (I : Finset B) : Set (B → ℝ) :=
  (wordAction M ws) '' (titsFaceDual M I)

/-- Uniform bound: along the segment $[x, \mu] \subset \mathcal U$, every point can be written
as $\sigma^*_w(y)$ for $y \ge 0$ with $|w|$ bounded by a fixed $N$ depending only on $x, \mu$. -/
theorem segment_word_length_bounded (M : CoxeterMatrix B) (x μ : B → ℝ)
    (hx : x ∈ titsConeSet M) (hμ : μ ∈ titsConeSet M) :
    ∃ N : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ (ws : List B) (y : B → ℝ), (∀ s, y s ≥ 0) ∧ ws.length ≤ N ∧
        (fun s => (1 - t) * x s + t * μ s) = wordAction M ws y := by

  obtain ⟨y₁, hy₁, ws₁, hx_eq⟩ := hx
  obtain ⟨y₂, hy₂, ws₂, hμ_eq⟩ := hμ
  subst hx_eq; subst hμ_eq

  set ws_comb := ws₂ ++ ws₁.reverse with ws_comb_def

  refine ⟨ws₁.length + ws_comb.length, fun t ht0 ht1 => ?_⟩

  obtain ⟨ws_mid, y_mid, hy_mid, hlen_mid, heq_mid⟩ :=
    convex_closure_titsCone_bounded M ws_comb.length ws_comb (le_refl _)
      y₂ hy₂ y₁ hy₁ (1 - t) t (by linarith) ht0 (by ring)


  have cancel_y₂ : wordAction M ws₁ (wordAction M ws_comb y₂) =
      wordAction M ws₂ y₂ := by
    rw [ws_comb_def, wordAction_append]
    exact wordAction_cancel_reverse M ws₁ (wordAction M ws₂ y₂)

  have heq_seg : (fun s => (1 - t) * (wordAction M ws₁ y₁) s +
      t * (wordAction M ws₂ y₂) s) =
      wordAction M ws₁ (fun s => (1 - t) * y₁ s + t * (wordAction M ws_comb y₂) s) := by
    rw [wordAction_linear]
    ext s; congr 1
    exact congr_arg (t * ·) (congr_fun cancel_y₂ s).symm

  show ∃ ws y, (∀ s, y s ≥ 0) ∧ ws.length ≤ ws₁.length + ws_comb.length ∧
    (fun s => (1 - t) * wordAction M ws₁ y₁ s + t * wordAction M ws₂ y₂ s) = wordAction M ws y
  rw [heq_seg, heq_mid]
  refine ⟨ws_mid ++ ws₁, y_mid, hy_mid, ?_, ?_⟩
  ·
    rw [List.length_append]
    have : ws_mid.length ≤ ws_comb.length := hlen_mid
    rw [ws_comb_def, List.length_append, List.length_reverse] at this
    omega
  ·
    rw [wordAction_append]

/-- The segment $[x, \mu]$ is covered by finitely many faces $w \cdot F_I$ with $|w|$ bounded
by a constant $N$ depending only on the endpoints. -/
theorem segment_finite_face_covering (M : CoxeterMatrix B) (x μ : B → ℝ)
    (hx : x ∈ titsConeSet M) (hμ : μ ∈ titsConeSet M) :
    ∃ N : ℕ, ∀ (z : B → ℝ),
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = fun s => (1 - t) * x s + t * μ s) →
      ∃ (ws : List B) (I : Finset B), ws.length ≤ N ∧ z ∈ wordFace M ws I := by
  obtain ⟨N, hN⟩ := segment_word_length_bounded M x μ hx hμ
  refine ⟨N, fun z ⟨t, ht0, ht1, hz⟩ => ?_⟩
  obtain ⟨ws, y, hy, hlen, heq⟩ := hN t ht0 ht1
  set I := Finset.univ.filter (fun s => y s = 0)
  refine ⟨ws, I, hlen, ?_⟩
  simp only [wordFace, Set.mem_image]
  refine ⟨y, ⟨fun s hs => (Finset.mem_filter.mp hs).2, fun s hs => ?_⟩, hz ▸ heq.symm⟩
  exact lt_of_le_of_ne (hy s) (fun h => hs (Finset.mem_filter.mpr ⟨Finset.mem_univ s, h.symm⟩))

/-- Face intersection rigidity: if $w \cdot F_I \cap F_J \ne \emptyset$ then $I = J$ and $w$ fixes
$F_I$ pointwise. This is the key combinatorial property of the face decomposition of $\mathcal U$. -/
theorem face_intersection_property (M : CoxeterMatrix B) :
  ∀ (ws : List B) (I J : Finset B),
  (wordFace M ws I ∩ (titsFaceDual M J : Set (B → ℝ))).Nonempty →
  I = J ∧ ∀ (y : B → ℝ), y ∈ titsFaceDual M I → wordAction M ws y = y := by


  set cs := M.toCoxeterSystem

  suffices h : ∀ (n : ℕ) (ws : List B), cs.length (cs.wordProd ws) ≤ n →
    ∀ (I J : Finset B),
    (wordFace M ws I ∩ (titsFaceDual M J : Set (B → ℝ))).Nonempty →
    I = J ∧ ∀ (y : B → ℝ), y ∈ titsFaceDual M I → wordAction M ws y = y by
    intro ws I J hne
    exact h (cs.length (cs.wordProd ws)) ws le_rfl I J hne
  intro n
  induction n with
  | zero =>
    intro ws hlen I J hne

    have hlen0 : cs.length (cs.wordProd ws) = 0 := Nat.le_zero.mp hlen
    have hone : cs.wordProd ws = 1 := cs.length_eq_zero_iff.mp hlen0

    have hid : ∀ y, wordAction M ws y = y := by
      intro y
      have := wordAction_eq_of_wordProd_eq M ws []
        (by rw [hone, cs.wordProd_nil]) y
      simpa using this

    have hface : wordFace M ws I = titsFaceDual M I := by
      ext z; simp only [wordFace, Set.mem_image]
      constructor
      · rintro ⟨z', hz', heq⟩; rw [hid z'] at heq; rwa [← heq]
      · intro hz; exact ⟨z, hz, hid z⟩

    rw [hface] at hne
    obtain ⟨z, hzI, hzJ⟩ := hne
    simp only [titsFaceDual, Set.mem_setOf_eq] at hzI hzJ
    constructor
    · ext s
      constructor
      · intro hs
        by_contra hs'
        have h1 := hzI.1 s hs
        have h2 := hzJ.2 s hs'
        linarith
      · intro hs
        by_contra hs'
        have h1 := hzJ.1 s hs
        have h2 := hzI.2 s hs'
        linarith
    · intro y _; exact hid y
  | succ n ih =>
    intro ws hlen I J hne

    obtain ⟨rw_word, hrw_red, hrw_prod⟩ := cs.exists_reduced_word (cs.wordProd ws)

    have hrw_len : rw_word.length = cs.length (cs.wordProd ws) := by
      rw [hrw_prod]; exact hrw_red.eq.symm

    have hact_eq : ∀ y, wordAction M ws y = wordAction M rw_word y :=
      fun y => wordAction_eq_of_wordProd_eq M ws rw_word hrw_prod y

    by_cases hℓ_zero : cs.length (cs.wordProd ws) = 0
    · exact ih ws (by omega) I J hne

    have hrw_nonempty : rw_word ≠ [] := by
      intro h; subst h; simp [cs.wordProd_nil] at hrw_prod
      rw [hrw_prod] at hℓ_zero; simp [cs.length_one] at hℓ_zero

    obtain ⟨rest_rw, s, hrw_eq⟩ : ∃ (init : List B) (last : B), rw_word = init ++ [last] :=
      ⟨rw_word.dropLast, rw_word.getLast hrw_nonempty,
       (rw_word.dropLast_append_getLast hrw_nonempty).symm⟩

    have hdesc : cs.IsRightDescent (cs.wordProd rw_word) s := by
      rw [CoxeterSystem.IsRightDescent]
      rw [hrw_eq, cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one,
          cs.simple_mul_simple_cancel_right]
      have h1 : cs.length (cs.wordProd rest_rw) ≤ rest_rw.length := cs.length_wordProd_le rest_rw
      have h2 := hrw_red.eq
      rw [hrw_eq, cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one,
          List.length_append, List.length_singleton] at h2
      omega

    have hneg_root : CoxeterGroup.IsNegative (wordSigma M rw_word (e s)) := by
      exact CoxeterGroup.neg_of_descent M cs rw_word s hrw_red hdesc

    have haction_s_nonpos : ∀ (y : B → ℝ), (∀ t, y t ≥ 0) →
        wordAction M ws y s ≤ 0 := by
      intro y hy
      rw [hact_eq, wordAction_transpose]
      apply Finset.sum_nonpos
      intro t _
      exact mul_nonpos_of_nonneg_of_nonpos (hy t)
        (by have := hneg_root t
            exact le_of_eq rfl |>.trans
              (by rwa [congr_fun (wordSigma_eq_of_wordProd_eq M cs rw_word rw_word rfl (e s)) t]))

    obtain ⟨p, hp_face, hp_J⟩ := hne
    simp only [wordFace, Set.mem_image] at hp_face
    obtain ⟨z', hz'_I, hp_eq⟩ := hp_face

    have hz'_nonneg : ∀ t, z' t ≥ 0 := by
      intro t
      simp only [titsFaceDual, Set.mem_setOf_eq] at hz'_I
      by_cases ht : t ∈ I
      · exact le_of_eq (hz'_I.1 t ht).symm
      · exact le_of_lt (hz'_I.2 t ht)

    have hws_s_nonpos : wordAction M ws z' s ≤ 0 := haction_s_nonpos z' hz'_nonneg

    have hp_s_nonneg : p s ≥ 0 := by
      simp only [titsFaceDual, Set.mem_setOf_eq] at hp_J
      by_cases hs_J : s ∈ J
      · exact le_of_eq (hp_J.1 s hs_J).symm
      · exact le_of_lt (hp_J.2 s hs_J)

    have hws_s_zero : wordAction M ws z' s = 0 := by linarith [hp_eq ▸ hp_s_nonneg]

    have hs_in_J : s ∈ J := by
      by_contra hs_nJ
      simp only [titsFaceDual, Set.mem_setOf_eq] at hp_J
      have := hp_J.2 s hs_nJ
      linarith [hp_eq ▸ hws_s_zero]

    have hrw_action : ∀ v, wordAction M rw_word v = dualSigma M s (wordAction M rest_rw v) := by
      intro v; rw [hrw_eq, wordAction_append, wordAction_singleton]

    have hrest_s : wordAction M rest_rw z' s = 0 := by
      have h1 : wordAction M ws z' s = dualSigma M s (wordAction M rest_rw z') s := by
        rw [hact_eq, hrw_action]
      rw [dualSigma_on_s] at h1
      linarith

    have hdual_fix : dualSigma M s (wordAction M rest_rw z') = wordAction M rest_rw z' :=
      dualSigma_fixed_on_wall M s (wordAction M rest_rw z') hrest_s

    have hws_eq_rest : wordAction M ws z' = wordAction M rest_rw z' := by
      rw [hact_eq, hrw_action z', hdual_fix]

    have hrest_in_J : wordAction M rest_rw z' ∈ titsFaceDual M J := by
      rwa [← hws_eq_rest, hp_eq]

    have hne_rest : (wordFace M rest_rw I ∩ (titsFaceDual M J : Set (B → ℝ))).Nonempty :=
      ⟨wordAction M rest_rw z', ⟨z', hz'_I, rfl⟩, hrest_in_J⟩

    have hrest_len : cs.length (cs.wordProd rest_rw) ≤ n := by
      have hlen_rest_rw : rest_rw.length ≤ n := by
        have : rw_word.length = rest_rw.length + 1 := by
          rw [hrw_eq, List.length_append, List.length_singleton]
        omega
      exact le_trans (cs.length_wordProd_le rest_rw) hlen_rest_rw

    obtain ⟨hIJ_rest, hfix_rest⟩ := ih rest_rw hrest_len I J hne_rest

    refine ⟨hIJ_rest, fun y hy => ?_⟩

    have hs_in_I : s ∈ I := hIJ_rest ▸ hs_in_J

    have hy_s_zero : y s = 0 := by
      simp only [titsFaceDual, Set.mem_setOf_eq] at hy
      exact hy.1 s hs_in_I

    have hrest_fix : wordAction M rest_rw y = y := hfix_rest y hy
    rw [hact_eq, hrw_action y, hrest_fix]
    exact dualSigma_fixed_on_wall M s y hy_s_zero

/-- Every point of the closed fundamental chamber lies on the face $F_I$ where $I$ is its
zero-coordinate set $\{s : y_s = 0\}$. -/
theorem closure_mem_face (M : CoxeterMatrix B) (y : B → ℝ) (hy : y ∈ titsFundamentalClosure M) :
    y ∈ titsFaceDual M (Finset.univ.filter (fun s => y s = 0)) := by
  simp only [titsFaceDual, Set.mem_setOf_eq, titsFundamentalClosure, Set.mem_setOf_eq] at *
  constructor
  · intro s hs
    exact (Finset.mem_filter.mp hs).2
  · intro s hs
    have := hy s
    rw [Finset.mem_filter, not_and] at hs
    have hne : y s ≠ 0 := fun h => hs (Finset.mem_univ s) h
    exact lt_of_le_of_ne this (Ne.symm hne)

/-- Uniqueness in the fundamental domain: if $y_1, y_2 \in \overline{C}$ and $\sigma^*_w(y_2) = y_1$
for some $w$, then $y_1 = y_2$. Combined with existence, this shows $\overline{C}$ is a strict
fundamental domain for the $W$-action on $\mathcal U$. -/
theorem fundamental_domain_uniqueness (M : CoxeterMatrix B) :
    ∀ (y₁ y₂ : B → ℝ), y₁ ∈ titsFundamentalClosure M →
    y₂ ∈ titsFundamentalClosure M →
    ∀ (ws : List B), wordAction M ws y₂ = y₁ → y₁ = y₂ := by
  intro y₁ y₂ hy₁ hy₂ ws hws

  set J := Finset.univ.filter (fun s => y₂ s = 0) with J_def
  have hy₂J : y₂ ∈ titsFaceDual M J := closure_mem_face M y₂ hy₂

  set I := Finset.univ.filter (fun s => y₁ s = 0) with I_def
  have hy₁I : y₁ ∈ titsFaceDual M I := closure_mem_face M y₁ hy₁

  have hmem : (wordFace M ws J ∩ (titsFaceDual M I : Set (B → ℝ))).Nonempty := by
    refine ⟨y₁, ?_, hy₁I⟩
    simp only [wordFace, Set.mem_image]
    exact ⟨y₂, hy₂J, hws⟩

  obtain ⟨hJI, hfix_face⟩ := face_intersection_property M ws J I hmem

  have hfix : wordAction M ws y₂ = y₂ := hfix_face y₂ hy₂J
  rw [hfix] at hws
  exact hws.symm

/-- Local finiteness of the face stratification along a segment: a segment $[x,\mu] \subset \mathcal U$
meets only finitely many faces $w \cdot F_I$. -/
theorem titsCone_segment_finite_faces (M : CoxeterMatrix B) (x μ : B → ℝ)
    (hx : x ∈ titsConeSet M) (hμ : μ ∈ titsConeSet M) :
    Set.Finite {F : Set (B → ℝ) |
      (∃ (ws : List B) (I : Finset B), F = wordFace M ws I) ∧
      ∃ t ∈ Set.Icc (0 : ℝ) 1,
        (fun s => (1 - t) * x s + t * μ s) ∈ F} := by
  obtain ⟨N, hN⟩ := segment_finite_face_covering M x μ hx hμ

  apply Set.Finite.subset
    (s := (fun p : List B × Finset B => wordFace M p.1 p.2) ''
      {p | p.1.length ≤ N})
  · apply Set.Finite.image
    exact (Set.Finite.prod (List.finite_length_le B N) Set.finite_univ).subset
      (fun ⟨ws, I⟩ h => ⟨h, Set.mem_univ _⟩)
  · intro F ⟨⟨ws0, I0, hF_eq⟩, t, ⟨ht0, ht1⟩, hmem_F⟩
    rw [hF_eq] at hmem_F
    obtain ⟨ws, I, hlen, hmem'⟩ := hN _ ⟨t, ht0, ht1, rfl⟩


    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists]
    simp only [wordFace, Set.mem_image] at hmem_F hmem'
    obtain ⟨y0, hy0, heq0⟩ := hmem_F
    obtain ⟨y1, hy1, heq1⟩ := hmem'


    have heq_combined : wordAction M (ws0 ++ ws.reverse) y0 = y1 := by
      rw [wordAction_append]
      rw [show wordAction M ws0 y0 = wordAction M ws y1 from heq0.trans heq1.symm]
      exact wordAction_reverse_cancel M ws y1


    have hnonempty : (wordFace M (ws0 ++ ws.reverse) I0 ∩
        (titsFaceDual M I : Set (B → ℝ))).Nonempty :=
      ⟨y1, ⟨y0, hy0, heq_combined⟩, hy1⟩
    obtain ⟨hI_eq, hfix_combined⟩ := face_intersection_property M (ws0 ++ ws.reverse) I0 I hnonempty


    have hface_eq : wordFace M ws0 I0 = wordFace M ws I := by
      rw [hI_eq]
      ext z; simp only [wordFace, Set.mem_image]
      constructor
      · rintro ⟨z', hz', rfl⟩
        refine ⟨z', hz', ?_⟩

        have hcomb : wordAction M (ws0 ++ ws.reverse) z' = z' :=
          hfix_combined z' (hI_eq ▸ hz')
        rw [wordAction_append] at hcomb


        have := congr_arg (wordAction M ws) hcomb
        rw [wordAction_cancel_reverse] at this
        exact this.symm
      · rintro ⟨z', hz', rfl⟩
        refine ⟨z', hz', ?_⟩
        have hcomb : wordAction M (ws0 ++ ws.reverse) z' = z' :=
          hfix_combined z' (hI_eq ▸ hz')
        rw [wordAction_append] at hcomb
        have := congr_arg (wordAction M ws) hcomb
        rw [wordAction_cancel_reverse] at this
        exact this
    exact ⟨ws, I, hlen, by rw [hF_eq, hface_eq]⟩

/-- **Main theorem on the Tits cone $\mathcal U$.** Bundles convexity, cone closure under
nonnegative scaling, existence and uniqueness of the closed fundamental chamber $\overline{C}$,
the face intersection rigidity property, and uniform finiteness of the face covering on any segment. -/
theorem titsCone_main_theorem (M : CoxeterMatrix B) :

    Convex ℝ (titsConeSet M) ∧

    (∀ (x : B → ℝ), x ∈ titsConeSet M → ∀ (c : ℝ), 0 ≤ c → c • x ∈ titsConeSet M) ∧

    (∀ (x : B → ℝ), x ∈ titsConeSet M →
      ∃ (ws : List B) (y : B → ℝ), y ∈ titsFundamentalClosure M ∧
        x = wordAction M ws y) ∧

    (∀ (y₁ y₂ : B → ℝ), y₁ ∈ titsFundamentalClosure M →
      y₂ ∈ titsFundamentalClosure M →
      ∀ (ws : List B), wordAction M ws y₂ = y₁ → y₁ = y₂) ∧

    (∀ (ws : List B) (I J : Finset B),
      (wordFace M ws I ∩ (titsFaceDual M J : Set (B → ℝ))).Nonempty →
      I = J ∧ ∀ (y : B → ℝ), y ∈ titsFaceDual M I → wordAction M ws y = y) ∧

    (∀ (x μ : B → ℝ), x ∈ titsConeSet M → μ ∈ titsConeSet M →
      ∃ N : ℕ, ∀ (z : B → ℝ),
        (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = fun s => (1 - t) * x s + t * μ s) →
        ∃ (ws : List B) (I : Finset B), ws.length ≤ N ∧ z ∈ wordFace M ws I) := by
  exact ⟨titsConeSet_convex M,
         fun x hx c hc => titsConeSet_cone M x hx c hc,
         fun x hx => fundamental_domain_existence M x hx,
         fundamental_domain_uniqueness M,
         face_intersection_property M,
         fun x μ hx hμ => segment_finite_face_covering M x μ hx hμ⟩

end TitsCone
