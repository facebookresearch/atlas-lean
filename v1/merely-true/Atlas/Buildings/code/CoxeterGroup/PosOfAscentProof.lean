/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
import Atlas.Buildings.code.CoxeterGroup.SimpleReflectionInversions
import Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine
import Mathlib.GroupTheory.Coxeter.Length
import Atlas.Buildings.code.CoxeterGroup.DihedralPositivity
import Atlas.Buildings.code.CoxeterGroup.DihedralPositivityFinite
import Atlas.Buildings.code.CoxeterGroup.ParabolicDecomp
import Atlas.Buildings.code.CoxeterGroup.ParabolicPositivity
import Atlas.Buildings.code.CoxeterGroup.DihedralLengthBound

set_option maxHeartbeats 1600000

open CoxeterGroup

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Pointwise linearity of $\sigma_w$ on vectors supported in $\{s, t\}$:
$\sigma_w(v)(u) = v_s \cdot \sigma_w(\alpha_s)(u) + v_t \cdot \sigma_w(\alpha_t)(u)$. -/
theorem wordSigma_of_supported_two (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (word : List B) (v : B → ℝ) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
    wordSigma M word v = fun u =>
      v s * wordSigma M word (e s) u + v t * wordSigma M word (e t) u := by
  have hv : v = v s • e s + v t • e t := by
    ext u
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, Pi.single_apply]
    by_cases hus : u = s
    · subst hus; simp [hst]
    · by_cases hut : u = t
      · subst hut; simp [Ne.symm hst]
      · simp [hus, hut, hsupp u hus hut]
  conv_lhs => rw [hv]
  rw [wordSigma_add]
  simp only [wordSigma_smul]
  ext u; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

set_option linter.unusedSectionVars false in
/-- Inductive step (Case B) of the positivity-on-ascent argument: handles the case where
$t$ ascends $w$ on the right but $s$ descends $w$. The argument reduces to a smaller
word via parabolic decomposition. -/
theorem pos_of_ascent_case_b {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (n : ℕ)
    (ih : ∀ m < n, ∀ (word : List B) (s : B),
      word.length = m → cs.IsReduced word →
      cs.length (cs.wordProd word * cs.simple s) > cs.length (cs.wordProd word) →
      IsPositive (wordSigma M word (e s)))
    (init : List B) (s t : B)
    (hts : t ≠ s)
    (hred_init : cs.IsReduced init)
    (hasc_t : cs.length (cs.wordProd init * cs.simple t) > cs.length (cs.wordProd init))
    (hdesc_s : cs.length (cs.wordProd init * cs.simple s) < cs.length (cs.wordProd init))
    (hasc : cs.length (cs.wordProd (init ++ [t]) * cs.simple s) >
            cs.length (cs.wordProd (init ++ [t])))
    (hinit_len : init.length < n) :
    IsPositive (wordSigma M (init ++ [t]) (e s)) := by

  have hst : s ≠ t := Ne.symm hts
  obtain ⟨init', hred_init', hprod'⟩ := cs.exists_reduced_word (cs.wordProd init * cs.simple s)

  have hred' : cs.IsReduced init' := hred_init'

  have hinit'_len : init'.length + 1 = init.length := by
    have h1 : cs.length (cs.wordProd init) = init.length := hred_init
    have h2 : init'.length = cs.length (cs.wordProd init * cs.simple s) := by rw [hprod']; exact hred_init'.symm

    rcases cs.length_mul_simple (cs.wordProd init) s with h | h
    · omega
    · omega

  have hasc_s' : cs.length (cs.wordProd init' * cs.simple s) >
                 cs.length (cs.wordProd init') := by
    rw [← hprod', mul_assoc, cs.simple_mul_simple_self, mul_one]
    exact hdesc_s

  have hprod_full : cs.wordProd (init' ++ [s, t]) = cs.wordProd (init ++ [t]) := by
    rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_cons, cs.wordProd_nil, mul_one,
        cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one]

    rw [← mul_assoc (cs.wordProd init') (cs.simple s) (cs.simple t)]
    congr 1

    rw [← hprod', mul_assoc, cs.simple_mul_simple_self, mul_one]

  rw [← wordSigma_eq_of_wordProd_eq M cs (init' ++ [s, t]) (init ++ [t]) hprod_full (e s)]

  have hdecomp : init' ++ [s, t] = init' ++ ([s, t] : List B) := by simp
  rw [hdecomp, wordSigma_append]

  set v := wordSigma M [s, t] (e s)
  have hv_supp : ∀ u, u ≠ s → u ≠ t → v u = 0 :=
    wordSigma_support_two M s t hst [s, t]
      (by intro b hb; simp at hb; rcases hb with rfl | rfl; exact Or.inl rfl; exact Or.inr rfl)
      (e s) (e_supported_two s t)

  have hlin := wordSigma_of_supported_two M s t hst init' v hv_supp
  have hinit'_lt : init'.length < n := by omega
  have ih_s' : IsPositive (wordSigma M init' (e s)) :=
    ih init'.length hinit'_lt init' s rfl hred' hasc_s'

  have hm2 : M s t ≠ 2 := by
    intro heq

    have hcomm : cs.simple s * cs.simple t = cs.simple t * cs.simple s := by
      have hpow : (cs.simple s * cs.simple t) ^ M.M s t = 1 := cs.simple_mul_simple_pow s t
      change (cs.simple s * cs.simple t) ^ (M s t) = 1 at hpow
      rw [heq, pow_two] at hpow
      have hsinv : cs.simple s * cs.simple s = 1 := cs.simple_mul_simple_self s
      have htinv : cs.simple t * cs.simple t = 1 := cs.simple_mul_simple_self t
      have hs_inv : (cs.simple s)⁻¹ = cs.simple s := by
        exact mul_left_cancel (a := cs.simple s)
          (show cs.simple s * (cs.simple s)⁻¹ = cs.simple s * cs.simple s from by
            rw [mul_inv_cancel, ← hsinv])
      have ht_inv : (cs.simple t)⁻¹ = cs.simple t := by
        exact mul_left_cancel (a := cs.simple t)
          (show cs.simple t * (cs.simple t)⁻¹ = cs.simple t * cs.simple t from by
            rw [mul_inv_cancel, ← htinv])
      have hinv : (cs.simple s * cs.simple t)⁻¹ = cs.simple s * cs.simple t :=
        inv_eq_of_mul_eq_one_right hpow
      rw [mul_inv_rev, ht_inv, hs_inv] at hinv
      exact hinv.symm

    have hlen_wt : cs.length (cs.wordProd init * cs.simple t) = cs.length (cs.wordProd init) + 1 := by
      rcases cs.length_mul_simple (cs.wordProd init) t with h | h
      · exact h
      · omega

    have hlen_wts : cs.length (cs.wordProd init * cs.simple t * cs.simple s) =
        cs.length (cs.wordProd init) + 2 := by
      have hasc' : cs.length (cs.wordProd init * cs.simple t * cs.simple s) >
          cs.length (cs.wordProd init * cs.simple t) := by
        have h := hasc
        rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one, mul_assoc] at h
        rwa [← mul_assoc] at h
      rcases cs.length_mul_simple (cs.wordProd init * cs.simple t) s with h | h
      · rw [h, hlen_wt]
      · omega

    have heq : cs.wordProd init * cs.simple t * cs.simple s =
        cs.wordProd init * cs.simple s * cs.simple t := by
      rw [mul_assoc, mul_assoc, hcomm]

    have hlen_wst : cs.length (cs.wordProd init * cs.simple s * cs.simple t) ≤
        cs.length (cs.wordProd init) := by
      have hle := cs.length_mul_le (cs.wordProd init * cs.simple s) (cs.simple t)
      rw [cs.length_simple] at hle
      rcases cs.length_mul_simple (cs.wordProd init) s with h | h
      · omega
      · omega

    rw [heq] at hlen_wts
    omega
  have hv_pos : IsPositive v := dihedral_pos_len2 M s t hst hm2
  have hvs : v s ≥ 0 := hv_pos s
  have hvt : v t ≥ 0 := hv_pos t

  rcases cs.length_mul_simple (cs.wordProd init') t with hasc_t' | hdesc_t'
  ·
    have ih_t' : IsPositive (wordSigma M init' (e t)) :=
      ih init'.length hinit'_lt init' t rfl hred' (by omega)
    intro u
    have := congr_fun hlin u
    rw [this]
    nlinarith [ih_s' u, ih_t' u, hvs, hvt]
  ·

    obtain ⟨x, y_word, hprod_xy, hxs_eq, hxt_eq, hy_mem, hlen_add⟩ :=
      cs.parabolic_decomp_rank2 (cs.wordProd init') s t hst

    obtain ⟨x_word, hx_red, hx_prod⟩ := cs.exists_reduced_word x

    have hx_len : x_word.length = cs.length x := by rw [hx_prod]; exact hx_red.symm

    have hx_lt : x_word.length < n := by
      have h_init'_len_eq : cs.length (cs.wordProd init') = init'.length := hred'
      have : x_word.length = cs.length x := hx_len

      omega

    have hxs_asc : cs.length (cs.wordProd x_word * cs.simple s) >
        cs.length (cs.wordProd x_word) := by
      rw [← hx_prod]; omega
    have hxt_asc : cs.length (cs.wordProd x_word * cs.simple t) >
        cs.length (cs.wordProd x_word) := by
      rw [← hx_prod]; omega

    have pos_xs : IsPositive (wordSigma M x_word (e s)) :=
      ih x_word.length hx_lt x_word s rfl hx_red hxs_asc
    have pos_xt : IsPositive (wordSigma M x_word (e t)) :=
      ih x_word.length hx_lt x_word t rfl hx_red hxt_asc

    have hprod_init'_eq : cs.wordProd (x_word ++ y_word) = cs.wordProd init' := by
      rw [cs.wordProd_append, ← hx_prod, hprod_xy]
    rw [← wordSigma_eq_of_wordProd_eq M cs (x_word ++ y_word) init' hprod_init'_eq v,
        wordSigma_append]

    have hv_eq : wordSigma M y_word v = wordSigma M (y_word ++ [s, t]) (e s) := by
      change wordSigma M y_word (wordSigma M [s, t] (e s)) = wordSigma M (y_word ++ [s, t]) (e s)
      rw [← wordSigma_append]

    have hprod_x_yst : x * cs.wordProd (y_word ++ [s, t]) =
        cs.wordProd init' * cs.wordProd [s, t] := by
      rw [cs.wordProd_append, ← mul_assoc, hprod_xy]

    have hprod_x_yst2 : x * cs.wordProd (y_word ++ [s, t]) = cs.wordProd (init ++ [t]) := by
      rw [hprod_x_yst, ← cs.wordProd_append]; exact hprod_full

    have hlen_init_t : cs.length (cs.wordProd (init ++ [t])) = init.length + 1 := by
      rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one]
      rcases cs.length_mul_simple (cs.wordProd init) t with h | h
      · rw [h, hred_init]
      · omega

    have hlen_yst_lower : cs.length (cs.wordProd (y_word ++ [s, t])) ≥ y_word.length + 2 := by
      have htri := cs.length_mul_le x (cs.wordProd (y_word ++ [s, t]))
      rw [hprod_x_yst2, hlen_init_t] at htri
      have hxlen : cs.length x + y_word.length = init'.length := by
        have := hlen_add; rw [hred'] at this; exact this
      have : init'.length + 1 = init.length := hinit'_len
      omega

    have hlen_yst_upper : cs.length (cs.wordProd (y_word ++ [s, t])) ≤ y_word.length + 2 := by
      have := cs.length_wordProd_le (y_word ++ [s, t])
      simp [List.length_append] at this; omega

    have hred_yst : cs.IsReduced (y_word ++ [s, t]) := by
      unfold CoxeterSystem.IsReduced
      simp [List.length_append]; omega

    have hmem_yst : ∀ b ∈ y_word ++ [s, t], b = s ∨ b = t := by
      intro b hb; simp [List.mem_append] at hb
      rcases hb with hb | hb | hb
      · exact hy_mem b hb
      · exact Or.inl hb
      · exact Or.inr hb

    have hchain_yst : List.Chain' (· ≠ ·) (y_word ++ [s, t]) := by

      rw [show List.Chain' (· ≠ ·) (y_word ++ [s, t]) ↔
        ∀ (i : ℕ) (_hi : i + 1 < (y_word ++ [s, t]).length),
        (y_word ++ [s, t])[i] ≠ (y_word ++ [s, t])[i + 1] from List.isChain_iff_getElem]
      intro i hi heq_adj

      set w := y_word ++ [s, t]
      have hw_eq : cs.wordProd w = cs.wordProd (w.take i ++ w.drop (i + 2)) := by
        have hi' : i < w.length := by omega
        conv_lhs => rw [← List.take_append_drop i w]
        rw [cs.wordProd_append]
        have hdrop_i : w.drop i = w[i] :: w.drop (i + 1) := List.drop_eq_getElem_cons hi'
        have hdrop_i1 : w.drop (i + 1) = w[i + 1] :: w.drop (i + 2) :=
          List.drop_eq_getElem_cons (show i + 1 < w.length from by omega)
        rw [hdrop_i, hdrop_i1, cs.wordProd_cons, cs.wordProd_cons, heq_adj]
        rw [show cs.simple w[i + 1] * (cs.simple w[i + 1] * cs.wordProd (w.drop (i + 2))) =
             (cs.simple w[i + 1] * cs.simple w[i + 1]) * cs.wordProd (w.drop (i + 2)) from (mul_assoc _ _ _).symm]
        rw [cs.simple_mul_simple_self, one_mul, ← cs.wordProd_append]
      have hlen_short : cs.length (cs.wordProd w) ≤ w.length - 2 := by
        rw [hw_eq]
        have hle := cs.length_wordProd_le (w.take i ++ w.drop (i + 2))
        have : (w.take i ++ w.drop (i + 2)).length = w.length - 2 := by
          simp [List.length_take, List.length_drop]; omega
        omega
      have hred_val : cs.length (cs.wordProd w) = w.length := hred_yst
      omega

    have hlast_yst : (y_word ++ [s, t]) = [] ∨
        (∃ h : (y_word ++ [s, t]) ≠ [], (y_word ++ [s, t]).getLast h = t) := by
      right; exact ⟨by simp, by simp⟩

    have hlen_word_lt : (y_word ++ [s, t]).length < M.M s t ∨ M.M s t = 0 := by

      by_cases hM : M.M s t = 0
      · exact Or.inr hM
      · left

        have hmem_ysts : ∀ b ∈ y_word ++ [s, t, s], b = s ∨ b = t := by
          intro b hb; simp [List.mem_append] at hb
          rcases hb with hb | hb | hb | hb
          · exact hy_mem b hb
          · exact Or.inl hb
          · exact Or.inr hb
          · exact Or.inl hb

        have hle_M : cs.length (cs.wordProd (y_word ++ [s, t, s])) ≤ M.M s t :=
          cs.length_wordProd_le_M s t (y_word ++ [s, t, s]) hmem_ysts hM

        have hprod_ysts : cs.wordProd (y_word ++ [s, t, s]) =
            cs.wordProd (y_word ++ [s, t]) * cs.simple s := by
          rw [show y_word ++ [s, t, s] = (y_word ++ [s, t]) ++ [s] from by simp]
          rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one]

        have hlen_yst_val : cs.length (cs.wordProd (y_word ++ [s, t])) =
            y_word.length + 2 := by omega

        have hlen_x_yst : cs.length (x * cs.wordProd (y_word ++ [s, t])) =
            cs.length x + cs.length (cs.wordProd (y_word ++ [s, t])) := by
          have h1 : x_word.length + y_word.length = init'.length := by
            have := hlen_add; rw [← hx_len, hred'] at this; exact this
          rw [hprod_x_yst2, hlen_init_t, hlen_yst_val, ← hx_len]
          omega

        have hasc_yst : cs.length (x * cs.wordProd (y_word ++ [s, t]) * cs.simple s) =
            cs.length (x * cs.wordProd (y_word ++ [s, t])) + 1 := by
          rw [hprod_x_yst2]
          rcases cs.length_mul_simple (cs.wordProd (init ++ [t])) s with h | h
          · exact h
          · exfalso; omega

        have hsub := cs.length_mul_le x (cs.wordProd (y_word ++ [s, t]) * cs.simple s)
        rw [mul_assoc] at hasc_yst
        have hge_yst_s : cs.length (cs.wordProd (y_word ++ [s, t]) * cs.simple s) ≥
            cs.length (cs.wordProd (y_word ++ [s, t])) + 1 := by

          omega

        have hlen_yst_s : cs.length (cs.wordProd (y_word ++ [s, t]) * cs.simple s) =
            cs.length (cs.wordProd (y_word ++ [s, t])) + 1 := by
          rcases cs.length_mul_simple (cs.wordProd (y_word ++ [s, t])) s with h | h
          · exact h
          · omega

        have hlen_ysts : cs.length (cs.wordProd (y_word ++ [s, t, s])) = y_word.length + 3 := by
          rw [hprod_ysts, hlen_yst_s, hlen_yst_val]

        simp [List.length_append]
        omega

    have vy_pos : IsPositive (wordSigma M (y_word ++ [s, t]) (e s)) :=
      parabolic_pos M s t hst (y_word ++ [s, t]) hmem_yst hlen_word_lt hchain_yst hlast_yst

    have vy_pos2 : IsPositive (wordSigma M y_word v) := by rw [hv_eq]; exact vy_pos

    have vy_supp : ∀ u, u ≠ s → u ≠ t → (wordSigma M y_word v) u = 0 :=
      wordSigma_support_two M s t hst y_word hy_mem v hv_supp

    exact parabolic_pos_vector_of_both_positive M s t hst x_word pos_xs pos_xt
      (wordSigma M y_word v) vy_pos2 vy_supp

/-- Strong-induction proof of positivity on ascent: if $w$ is reduced and $s$ ascends
$w$ on the right, then $\sigma_w(\alpha_s)$ is a positive vector. -/
theorem pos_of_ascent_proof {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) :
    ∀ (n : ℕ) (word : List B) (s : B),
    word.length = n →
    cs.IsReduced word →
    cs.length (cs.wordProd word * cs.simple s) > cs.length (cs.wordProd word) →
    IsPositive (wordSigma M word (e s)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro word s hlen hred hasc

  rcases word.eq_nil_or_concat' with rfl | ⟨init, t, rfl⟩
  ·
    intro u; simp [wordSigma, e, Pi.single_apply]; split <;> linarith
  ·

    have hts : t ≠ s := by
      intro heq; subst heq
      have h1 : cs.length (cs.wordProd (init ++ [t]) * cs.simple t) ≤ init.length := by
        rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one,
            mul_assoc, cs.simple_mul_simple_self, mul_one]
        exact cs.length_wordProd_le init
      have h2 : cs.length (cs.wordProd (init ++ [t])) = (init ++ [t]).length := hred
      simp at h2; omega

    have hred_init : cs.IsReduced init := by
      unfold CoxeterSystem.IsReduced at hred ⊢
      have hle := cs.length_wordProd_le init
      rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one] at hred
      simp at hred
      rcases cs.length_mul_simple (cs.wordProd init) t with h1 | h1 <;> omega
    have hasc_t : cs.length (cs.wordProd init * cs.simple t) >
                  cs.length (cs.wordProd init) := by
      have hred_i : cs.length (cs.wordProd init) = init.length := hred_init
      have hred_full := hred; unfold CoxeterSystem.IsReduced at hred_full
      rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one] at hred_full
      simp at hred_full; omega
    have hinit_len : init.length < n := by simp at hlen; omega

    have ih_t : IsPositive (wordSigma M init (e t)) :=
      ih init.length hinit_len init t rfl hred_init (by omega)

    rcases cs.length_mul_simple (cs.wordProd init) s with hasc_s | hdesc_s
    ·
      have ih_s : IsPositive (wordSigma M init (e s)) :=
        ih init.length hinit_len init s rfl hred_init (by omega)

      have hfv : formVal M s t ≤ 0 := formVal_nonpos_of_ne M s t (Ne.symm hts)
      have hst : s ≠ t := Ne.symm hts
      have hdecomp : wordSigma M (init ++ [t]) (e s) = wordSigma M init (sigma M t (e s)) := by
        rw [wordSigma_append, wordSigma_singleton]
      have hsupp : ∀ u, u ≠ s → u ≠ t → (sigma M t (e s)) u = 0 :=
        sigma_support_two M s t hst t (Or.inr rfl) (e s) (e_supported_two s t)
      have hcoeff_s : (sigma M t (e s)) s = 1 := by
        rw [sigma_coord_ne M t (e s) s hts.symm]; simp [e]
      have hcoeff_t : (sigma M t (e s)) t = -2 * formVal M s t := by
        rw [sigma_t_coord_t_of_supported M s t hst (e s) (e_supported_two s t)]
        simp [e, hst]
      have hlin := wordSigma_of_supported_two M s t hst init (sigma M t (e s)) hsupp
      rw [hdecomp]
      intro u
      have := congr_fun hlin u
      rw [this, hcoeff_s, hcoeff_t]
      have h1 := ih_s u
      have h2 := ih_t u
      nlinarith

    ·
      exact pos_of_ascent_case_b M cs n ih init s t hts hred_init (by omega) (by omega) hasc hinit_len

/-- Positivity on ascent: for a reduced word $w$ with $\ell(ws) > \ell(w)$, the vector
$\sigma_w(\alpha_s)$ is positive. -/
theorem pos_of_ascent {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hasc : cs.length (cs.wordProd word * cs.simple s) >
            cs.length (cs.wordProd word)) :
    IsPositive (wordSigma M word (e s)) :=
  pos_of_ascent_proof M cs word.length word s rfl hred hasc

/-- Negativity on descent: for a reduced word $w$ with $\ell(ws) < \ell(w)$, the vector
$\sigma_w(\alpha_s)$ is negative. -/
theorem neg_of_descent {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hdesc : cs.length (cs.wordProd word * cs.simple s) <
             cs.length (cs.wordProd word)) :
    IsNegative (wordSigma M word (e s)) := by

  set w := cs.wordProd word
  obtain ⟨word', hred', hprod'⟩ := cs.exists_reduced_word (w * cs.simple s)

  have hasc' : cs.length (cs.wordProd word' * cs.simple s) >
               cs.length (cs.wordProd word') := by
    rw [← hprod', mul_assoc, cs.simple_mul_simple_self, mul_one]
    exact hdesc

  have hpos := pos_of_ascent M cs word' s hred' hasc'

  have hprod_eq : cs.wordProd (word' ++ [s]) = w := by
    rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one,
        ← hprod', mul_assoc, cs.simple_mul_simple_self, mul_one]

  have hflip := wordSigma_append_s_neg M word' s

  have hinv := wordSigma_eq_of_wordProd_eq M cs (word' ++ [s]) word hprod_eq (e s)

  intro t
  have : wordSigma M word (e s) t = -(wordSigma M word' (e s) t) := by
    rw [← hinv]; exact congr_fun hflip t
  rw [this]
  linarith [hpos t]

end CoxeterGroup
