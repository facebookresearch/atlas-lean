/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
import Atlas.Buildings.code.CoxeterGroup.RootSystem
import Atlas.Buildings.code.CoxeterGroup.SignChangeExchangeFinal
import Atlas.Buildings.code.CoxeterGroup.Reflections

set_option maxHeartbeats 1600000

open Finset BigOperators CoxeterGroup

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Conjugation identity: if $\alpha = \sigma_u(\alpha_j)$ and $t = u s_j u^{-1}$, then
$\sigma_t$ acts on $\mathbb{R}^B$ as the generalized reflection $s_\alpha$ along $\alpha$.
This is the Section 1.6 lemma $\beta = w\alpha \Rightarrow w s_\alpha w^{-1} = s_\beta$. -/
theorem wordSigma_reflection_root_neg {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word_u : List B) (j : B) :
    let α := wordSigma M word_u (e j)
    let u := cs.wordProd word_u
    let t := u * cs.simple j * u⁻¹
    ∀ word_t : List B, cs.wordProd word_t = t →
    ∀ v : B → ℝ, wordSigma M word_t v = generalizedReflection M α v := by
  intro α u t word_t hprod_t v

  obtain ⟨word_u_inv, _, hprod_inv⟩ := cs.exists_isReduced (cs.wordProd word_u)⁻¹

  have hprod_concat : cs.wordProd (word_u ++ [j] ++ word_u_inv) = t := by
    rw [cs.wordProd_append, cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil,
        mul_one, ← hprod_inv]
  have hsame : wordSigma M word_t v = wordSigma M (word_u ++ [j] ++ word_u_inv) v :=
    wordSigma_eq_of_wordProd_eq M cs word_t (word_u ++ [j] ++ word_u_inv)
      (by rw [hprod_t, hprod_concat]) v
  rw [hsame]

  rw [List.append_assoc, wordSigma_append, wordSigma_append, wordSigma_singleton]

  set v' := wordSigma M word_u_inv v with hv'_def

  have hcancel : wordSigma M word_u (wordSigma M word_u_inv v) = v := by
    have hprod_id : cs.wordProd (word_u ++ word_u_inv) = 1 := by
      rw [cs.wordProd_append, ← hprod_inv, mul_inv_cancel]
    have heq := wordSigma_eq_of_wordProd_eq M cs (word_u ++ word_u_inv) []
      (by rw [hprod_id, cs.wordProd_nil]) v
    rwa [wordSigma_append] at heq

  have hsigma_eq : sigma M j v' = v' + (-2 * bilinForm M v' (e j)) • (e j) := by
    ext t
    simp only [sigma, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

  rw [hsigma_eq, wordSigma_add, wordSigma_smul, hcancel]


  have hform : bilinForm M v' (e j) = bilinForm M v α := by
    rw [hv'_def]
    calc bilinForm M (wordSigma M word_u_inv v) (e j)
        = bilinForm M (wordSigma M word_u (wordSigma M word_u_inv v))
            (wordSigma M word_u (e j)) := by
          rw [wordSigma_preserves_form]
      _ = bilinForm M v α := by
          rw [hcancel]
  rw [hform]

  ext t
  simp only [generalizedReflection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring


/-- Alias of `wordSigma_reflection_root_neg`: the conjugated reflection acts as the
generalized reflection along the conjugated root. -/
theorem conjugate_reflection_eq {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word_u : List B) (j : B) :
    let α := wordSigma M word_u (e j)
    let u := cs.wordProd word_u
    let t := u * cs.simple j * u⁻¹
    ∀ word_t : List B, cs.wordProd word_t = t →
    ∀ v : B → ℝ, wordSigma M word_t v = generalizedReflection M α v :=
  wordSigma_reflection_root_neg M cs word_u j

/-- The Coxeter representation of $w s_i w^{-1}$ equals the generalized reflection along
the root $w \cdot \alpha_i$. -/
theorem conj_simpleReflection_eq_generalizedReflection {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) (w : W) (s : B) :
    ∀ v : B → ℝ,
    (coxeterRepresentation M cs (w * cs.simple s * w⁻¹)) v =
    generalizedReflection M (coxeterRepresentation M cs w (e s)) v := by
  obtain ⟨word_w, _, hprod_w⟩ := cs.exists_isReduced w
  obtain ⟨word_t, _, hprod_t⟩ := cs.exists_isReduced (w * cs.simple s * w⁻¹)
  have hprod_eq : cs.wordProd word_t =
      cs.wordProd word_w * cs.simple s * (cs.wordProd word_w)⁻¹ := by
    rw [← hprod_w]; exact hprod_t.symm
  intro v
  have hlhs : (coxeterRepresentation M cs (w * cs.simple s * w⁻¹)) v =
      wordSigma M word_t v := by
    rw [hprod_t, coxeterRepresentation_wordProd_apply]
  have hroot : (coxeterRepresentation M cs w) (e s) = wordSigma M word_w (e s) := by
    rw [hprod_w, coxeterRepresentation_wordProd_apply]
  rw [hlhs, hroot]
  exact wordSigma_reflection_root_neg M cs word_w s word_t hprod_eq v


/-- Reflection positivity on ascent: for $\alpha = \sigma_u(\alpha_j)$ a positive root
and $t = u s_j u^{-1}$, if $w$ is reduced and $\ell(wt) > \ell(w)$, then
$\sigma_w(\alpha) > 0$. -/
theorem pos_of_ascent_reflection {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word_w : List B) (word_u : List B) (j : B)
    (hred_w : cs.IsReduced word_w)
    (hroot_pos : IsPositive (wordSigma M word_u (e j)))
    (hasc : cs.length (cs.wordProd word_w * (cs.wordProd word_u * cs.simple j * (cs.wordProd word_u)⁻¹)) >
            cs.length (cs.wordProd word_w)) :
    IsPositive (wordSigma M word_w (wordSigma M word_u (e j))) := by
  set w := cs.wordProd word_w with hw_def
  set u := cs.wordProd word_u
  set t := u * cs.simple j * u⁻¹
  set α := wordSigma M word_u (e j)

  suffices goal : ∀ (n : ℕ) (word_w : List B),
      word_w.length = n →
      cs.IsReduced word_w →
      cs.length (cs.wordProd word_w * t) > cs.length (cs.wordProd word_w) →
      IsPositive (wordSigma M word_w α) by
    exact goal word_w.length word_w rfl hred_w hasc
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro word_w hlen hred hasc_w

  match h_word : word_w with
  | [] =>

    exact hroot_pos
  | s₀ :: rest =>


    set sw₀ := cs.wordProd rest with hsw₀_def
    have hw_eq : cs.wordProd (s₀ :: rest) = cs.simple s₀ * sw₀ := by
      rw [cs.wordProd_cons]

    have hred_rest : cs.IsReduced rest := by
      show cs.length sw₀ = rest.length
      have hle : cs.length sw₀ ≤ rest.length := cs.length_wordProd_le rest
      have hred' : cs.length (cs.simple s₀ * sw₀) = rest.length + 1 := by
        have : cs.IsReduced (s₀ :: rest) := hred
        unfold CoxeterSystem.IsReduced at this
        rw [hw_eq] at this
        rw [this]; simp [List.length_cons]
      rcases cs.length_simple_mul sw₀ s₀ with h1 | h1
      · omega
      · omega


    have hs₀_inv : cs.simple s₀ * cs.simple s₀ = 1 := cs.simple_mul_simple_self s₀
    have hs₀w : cs.simple s₀ * cs.wordProd (s₀ :: rest) = sw₀ := by
      rw [hw_eq, ← mul_assoc, hs₀_inv, one_mul]
    have hs₀wt : cs.simple s₀ * (cs.wordProd (s₀ :: rest) * t) = sw₀ * t := by
      rw [← mul_assoc, hs₀w]

    have hlen_sw₀ : cs.length sw₀ = rest.length := hred_rest

    have hlen_w : cs.length (cs.wordProd (s₀ :: rest)) = rest.length + 1 := by
      rw [hred]; simp [List.length_cons]


    have hasc_rest : cs.length (sw₀ * t) > cs.length sw₀ := by
      rw [← hs₀wt]
      rcases cs.length_simple_mul (cs.wordProd (s₀ :: rest) * t) s₀ with h1 | h1
      ·
        rw [h1, hlen_sw₀]; omega
      ·
        rw [hlen_sw₀]; omega

    have hlen_rest : rest.length < n := by
      rw [← hlen]; simp [List.length_cons]
    have hpos_rest : IsPositive (wordSigma M rest α) :=
      ih rest.length hlen_rest rest rfl hred_rest hasc_rest


    set β := wordSigma M rest α with hβ_def
    show IsPositive (sigma M s₀ β)


    set wu := cs.wordProd (s₀ :: rest) * u with hwu_def
    obtain ⟨word_wu, hred_wu, hprod_wu⟩ := cs.exists_isReduced wu


    have hsigma_wu : wordSigma M word_wu (e j) = sigma M s₀ β := by
      have : sigma M s₀ β = wordSigma M ((s₀ :: rest) ++ word_u) (e j) := by
        rw [wordSigma_append, wordSigma_cons]
      rw [this]
      apply wordSigma_eq_of_wordProd_eq M cs
      rw [← hprod_wu, hwu_def, cs.wordProd_append]

    rcases cs.length_mul_simple (cs.wordProd word_wu) j with hasc_j | hdesc_j
    ·
      have : IsPositive (wordSigma M word_wu (e j)) :=
        pos_of_ascent M cs word_wu j hred_wu (by omega)
      rw [hsigma_wu] at this; exact this
    ·
      have hneg_wu : IsNegative (wordSigma M word_wu (e j)) :=
        neg_of_descent M cs word_wu j hred_wu (by omega)
      rw [hsigma_wu] at hneg_wu


      have hform_β : bilinForm M β β = 1 := by
        rw [hβ_def]
        have : bilinForm M (wordSigma M rest α) (wordSigma M rest α) = bilinForm M α α := by
          rw [wordSigma_preserves_form]
        rw [this]
        show bilinForm M (wordSigma M word_u (e j)) (wordSigma M word_u (e j)) = 1
        rw [wordSigma_preserves_form, bilinForm_e_e, formVal_diag]

      have hβ_eq : β = e s₀ := CoxeterSignChangeExchangeFinal.isPositive_sigma_isNegative_eq_e M s₀ β hpos_rest hneg_wu hform_β


      have hsigma_rest_u : wordSigma M (rest ++ word_u) (e j) = e s₀ := by
        rw [wordSigma_append]; exact hβ_eq


      have hconj := CoxeterSignChangeExchangeFinal.wordProd_cons_eq_append_of_wordSigma_eq_e cs
        (rest ++ word_u) j s₀ hsigma_rest_u

      have hprod_rest_u : cs.wordProd (rest ++ word_u) = sw₀ * u := by
        rw [cs.wordProd_append]
      rw [hprod_rest_u] at hconj


      have hwt_eq : cs.wordProd (s₀ :: rest) * t = sw₀ := by
        rw [hw_eq]
        show cs.simple s₀ * sw₀ * (u * cs.simple j * u⁻¹) = sw₀
        have : cs.simple s₀ * sw₀ * (u * cs.simple j * u⁻¹)
             = cs.simple s₀ * ((sw₀ * u) * cs.simple j) * u⁻¹ := by group
        rw [this, ← hconj]
        have : cs.simple s₀ * (cs.simple s₀ * (sw₀ * u)) * u⁻¹ = sw₀ := by
          rw [← mul_assoc (cs.simple s₀) (cs.simple s₀), hs₀_inv, one_mul, mul_assoc,
              mul_inv_cancel, mul_one]
        exact this


      have : cs.length (cs.wordProd (s₀ :: rest) * t) = rest.length := by
        rw [hwt_eq, hlen_sw₀]
      omega


/-- Reflection negativity on descent: for $\alpha = \sigma_u(\alpha_j)$ a positive root
and $t = u s_j u^{-1}$, if $w$ is reduced and $\ell(wt) < \ell(w)$, then
$\sigma_w(\alpha) < 0$. -/
theorem neg_of_descent_reflection {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word_w : List B) (word_u : List B) (j : B)
    (hred_w : cs.IsReduced word_w)
    (hroot_pos : IsPositive (wordSigma M word_u (e j)))
    (hdesc : cs.length (cs.wordProd word_w * (cs.wordProd word_u * cs.simple j * (cs.wordProd word_u)⁻¹)) <
             cs.length (cs.wordProd word_w)) :
    IsNegative (wordSigma M word_w (wordSigma M word_u (e j))) := by
  set w := cs.wordProd word_w
  set u := cs.wordProd word_u
  set t := u * cs.simple j * u⁻¹
  set α := wordSigma M word_u (e j)
  have ht_sq : t * t = 1 := by
    simp only [t]
    have : u * cs.simple j * u⁻¹ * (u * cs.simple j * u⁻¹)
         = u * (cs.simple j * cs.simple j) * u⁻¹ := by group
    rw [this, cs.simple_mul_simple_self, mul_one, mul_inv_cancel]
  set v := w * t
  have hvt : v * t = w := by
    simp only [v]; rw [mul_assoc, ht_sq, mul_one]
  have hasc_v : cs.length (v * t) > cs.length v := by
    rw [hvt]; exact hdesc
  obtain ⟨word_v, hred_v, hprod_v⟩ := cs.exists_isReduced v
  have hpos_v : IsPositive (wordSigma M word_v α) := by
    apply pos_of_ascent_reflection M cs word_v word_u j hred_v hroot_pos
    rwa [← hprod_v]
  obtain ⟨word_t, hred_t, hprod_t⟩ := cs.exists_isReduced t
  have hflip_full := wordSigma_reflection_root_neg M cs word_u j word_t (by rw [← hprod_t])

  have hform_α : bilinForm M α α = 1 := by
    show bilinForm M (wordSigma M word_u (e j)) (wordSigma M word_u (e j)) = 1
    rw [wordSigma_preserves_form, bilinForm_e_e, formVal_diag]
  have hflip : wordSigma M word_t α = fun b => -(α b) := by
    have := hflip_full α
    rw [this]
    ext b
    simp only [generalizedReflection]
    rw [hform_α]
    ring
  have hprod_vt : cs.wordProd (word_v ++ word_t) = w := by
    rw [cs.wordProd_append, ← hprod_v, ← hprod_t, hvt]
  have hinv := wordSigma_eq_of_wordProd_eq M cs word_w (word_v ++ word_t)
    (by rw [hprod_vt]) α
  intro b
  have : wordSigma M word_w α b = -(wordSigma M word_v α b) := by
    rw [hinv, wordSigma_append]
    conv_lhs => rw [show wordSigma M word_t α = fun b => -(α b) from hflip]
    have hsmul : (fun b => -(α b)) = (-1 : ℝ) • α := by
      ext b; simp [Pi.smul_apply, smul_eq_mul]
    rw [hsmul, wordSigma_smul]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [this]
  linarith [hpos_v b]

end CoxeterGroup
