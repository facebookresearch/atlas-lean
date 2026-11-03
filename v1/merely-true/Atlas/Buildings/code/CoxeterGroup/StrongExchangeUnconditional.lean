/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.DescentInversionBridge
import Atlas.Buildings.code.CoxeterGroup.ReflectionIdentificationGenuine
import Atlas.Buildings.code.CoxeterGroup.SignChangeExchangeFinal
import Atlas.Buildings.code.CoxeterGroup.ReflectionLengthDecrease

open CoxeterReflectionId

namespace StrongExchangeUnconditional

set_option linter.unusedSectionVars false

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- If $\omega \cdot s$ is a reduced word, so is its prefix $\omega$. -/
lemma isReduced_of_append_isReduced {W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (word : List B) (s : B)
    (h : cs.IsReduced (word ++ [s])) : cs.IsReduced word := by
  unfold CoxeterSystem.IsReduced at h ⊢
  have h1 := cs.length_wordProd_le word
  rw [List.length_append, List.length_singleton] at h
  have h3 : cs.wordProd (word ++ [s]) = cs.wordProd word * cs.simple s := by
    rw [cs.wordProd_append, cs.wordProd_singleton]
  rw [h3] at h
  rcases cs.length_mul_simple (cs.wordProd word) s with h4 | h4 <;> omega

/-- If $i$ is not a right descent of $v$ then $\ell(vs_i) = \ell(v) + 1$. -/
lemma not_descent_length_eq {W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (v : W) (i : B)
    (h : ¬cs.IsRightDescent v i) : cs.length (v * cs.simple i) = cs.length v + 1 := by
  unfold CoxeterSystem.IsRightDescent at h
  push Not at h
  rcases cs.length_mul_simple v i with h1 | h1 <;> omega

/-- If $i$ is a right descent of $w$ then $\ell(ws_i) + 1 = \ell(w)$. -/
lemma descent_length_eq {W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (w : W) (i : B)
    (h : cs.IsRightDescent w i) : cs.length (w * cs.simple i) + 1 = cs.length w := by
  unfold CoxeterSystem.IsRightDescent at h
  rcases cs.length_mul_simple w i with h1 | h1 <;> omega

/-- **Reflection identification (core)**: in a Bruhat cover $v \lessdot w = vt$ where $i$ is a
descent of $w$ but not of $v$, the reflection $t$ must be the simple reflection $s_i$. This is the
geometric core of the strong exchange theorem. -/
theorem reflection_identification_core (M : CoxeterMatrix B)
    (v w t : M.Group) (ht : t ∈ CoxeterBruhat.reflections M M.toCoxeterSystem)
    (hvt : v * t = w) (hlen : M.toCoxeterSystem.length v + 1 = M.toCoxeterSystem.length w)
    (i : B) (hv_asc : ¬M.toCoxeterSystem.IsRightDescent v i)
    (hw_desc : M.toCoxeterSystem.IsRightDescent w i) :
    t = M.toCoxeterSystem.simple i := by
  set cs := M.toCoxeterSystem

  have ht_inv : t * t = 1 := CoxeterBruhat.reflection_sq cs ht
  have hwt_eq_v : w * t = v := by
    have : w * t = (v * t) * t := by rw [hvt]
    rw [this, mul_assoc, ht_inv, mul_one]

  obtain ⟨u, j, htdef⟩ := ht

  obtain ⟨word_u, hred_u, hprod_u⟩ := cs.exists_isReduced u


  have key : ∃ word_u₀ : List B,
      CoxeterGroup.IsPositive (CoxeterGroup.wordSigma M word_u₀ (CoxeterGroup.e j)) ∧
      t = cs.wordProd word_u₀ * cs.simple j * (cs.wordProd word_u₀)⁻¹ := by
    by_cases hu_desc : cs.IsRightDescent u j
    ·
      refine ⟨word_u ++ [j], ?_, ?_⟩
      ·
        rw [CoxeterGroup.wordSigma_append, CoxeterGroup.wordSigma_singleton]
        have hsig : CoxeterGroup.sigma M j (CoxeterGroup.e j) = fun t => -(CoxeterGroup.e j t) :=
          CoxeterGroup.sigma_e_self M j
        rw [hsig]
        have : (fun t => -(CoxeterGroup.e j t)) = -(CoxeterGroup.e j) := by ext t; simp
        rw [this]
        have := CoxeterGroup.wordSigma_smul M word_u (-1 : ℝ) (CoxeterGroup.e j)
        simp at this
        rw [this]
        rw [CoxeterGroup.neg_isPositive_iff]
        exact DescentInversionBridge.descent_implies_isNegative M cs word_u j hred_u
          (by rw [← hprod_u]; exact hu_desc)
      ·
        rw [cs.wordProd_append, cs.wordProd_singleton, ← hprod_u, htdef]
        group
    ·
      refine ⟨word_u, ?_, ?_⟩
      · exact DescentInversionBridge.ascent_implies_isPositive M cs word_u j hred_u
          (by rw [← hprod_u]; exact hu_desc)
      · rw [htdef, ← hprod_u]
  obtain ⟨word_u₀, hα_pos, htdef₀⟩ := key
  set α := CoxeterGroup.wordSigma M word_u₀ (CoxeterGroup.e j) with hα_def

  have hform_α : CoxeterGroup.bilinForm M α α = 1 := by
    rw [hα_def, CoxeterGroup.wordSigma_preserves_form,
        CoxeterGroup.bilinForm_e_e, CoxeterGroup.formVal_diag]

  obtain ⟨prefix_, hred_pi, hprod_pi⟩ :=
    StrongExchangeBridge.exists_reduced_word_ending_in_descent (cs := cs) w i hw_desc

  have hlen_wt : cs.length (w * t) < cs.length w := by
    rw [hwt_eq_v]; omega
  have hlen_desc : cs.length (cs.wordProd (prefix_ ++ [i]) *
      (cs.wordProd word_u₀ * cs.simple j * (cs.wordProd word_u₀)⁻¹)) <
      cs.length (cs.wordProd (prefix_ ++ [i])) := by
    rw [hprod_pi, ← htdef₀]; exact hlen_wt
  have hneg_w : CoxeterGroup.IsNegative (CoxeterGroup.wordSigma M (prefix_ ++ [i]) α) :=
    CoxeterGroup.neg_of_descent_reflection M cs (prefix_ ++ [i]) word_u₀ j hred_pi hα_pos hlen_desc

  have hdecomp : CoxeterGroup.wordSigma M (prefix_ ++ [i]) α =
      CoxeterGroup.wordSigma M prefix_ (CoxeterGroup.sigma M i α) := by
    rw [CoxeterGroup.wordSigma_append, CoxeterGroup.wordSigma_singleton]
  rw [hdecomp] at hneg_w


  have hσiα_neg : CoxeterGroup.IsNegative (CoxeterGroup.sigma M i α) := by
    by_contra hσiα_not_neg

    have hσiα_eq : CoxeterGroup.sigma M i α =
        CoxeterGroup.wordSigma M ([i] ++ word_u₀) (CoxeterGroup.e j) := by
      rw [CoxeterGroup.wordSigma_append, CoxeterGroup.wordSigma_singleton, hα_def]

    have hlen_sigu : cs.length (cs.wordProd ([i] ++ word_u₀) * cs.simple j) <
        cs.length (cs.wordProd ([i] ++ word_u₀)) ∨
        cs.length (cs.wordProd ([i] ++ word_u₀) * cs.simple j) >
        cs.length (cs.wordProd ([i] ++ word_u₀)) := by
      have := cs.length_mul_simple (cs.wordProd ([i] ++ word_u₀)) j
      omega
    obtain ⟨word_iu, hred_iu, hprod_iu⟩ := cs.exists_isReduced (cs.wordProd ([i] ++ word_u₀))
    rcases hlen_sigu with hdesc_iu | hasc_iu
    ·
      exfalso; apply hσiα_not_neg
      have hneg_iu : CoxeterGroup.IsNegative (CoxeterGroup.wordSigma M word_iu (CoxeterGroup.e j)) :=
        DescentInversionBridge.descent_implies_isNegative M cs word_iu j hred_iu
          (by rw [← hprod_iu]; exact hdesc_iu)
      rw [hσiα_eq]
      rwa [DescentInversionBridge.wordSigma_eq_of_wordProd_eq M cs ([i] ++ word_u₀) word_iu
        (by rw [← hprod_iu]) (CoxeterGroup.e j)]
    ·


      exfalso

      have hσiα_pos : CoxeterGroup.IsPositive (CoxeterGroup.sigma M i α) := by
        rw [hσiα_eq]
        have hpos_iu : CoxeterGroup.IsPositive (CoxeterGroup.wordSigma M word_iu (CoxeterGroup.e j)) :=
          DescentInversionBridge.ascent_implies_isPositive M cs word_iu j hred_iu
            (by rw [← hprod_iu]; intro h; exact Nat.lt_irrefl _ (lt_trans h hasc_iu))
        rwa [DescentInversionBridge.wordSigma_eq_of_wordProd_eq M cs ([i] ++ word_u₀) word_iu
          (by rw [← hprod_iu]) (CoxeterGroup.e j)]

      have hred_prefix : cs.IsReduced prefix_ :=
        isReduced_of_append_isReduced cs prefix_ i hred_pi

      have hprod_prefix : cs.wordProd prefix_ = w * cs.simple i := by
        have h1 : cs.wordProd (prefix_ ++ [i]) = cs.wordProd prefix_ * cs.simple i := by
          rw [cs.wordProd_append, cs.wordProd_singleton]
        rw [hprod_pi] at h1

        have : cs.wordProd prefix_ = w * (cs.simple i)⁻¹ := by
          rw [h1]; group
        rw [this, show (cs.simple i)⁻¹ = cs.simple i from by
          have : cs.simple i * cs.simple i = 1 := cs.simple_mul_simple_self i
          exact inv_eq_of_mul_eq_one_right this]


      have hascent_len : cs.length (cs.wordProd prefix_ *
          (cs.wordProd ([i] ++ word_u₀) * cs.simple j * (cs.wordProd ([i] ++ word_u₀))⁻¹)) >
          cs.length (cs.wordProd prefix_) := by

        have hprod_iu : cs.wordProd ([i] ++ word_u₀) = cs.simple i * cs.wordProd word_u₀ := by
          rw [cs.wordProd_append, cs.wordProd_singleton]
        have hconj : cs.wordProd ([i] ++ word_u₀) * cs.simple j * (cs.wordProd ([i] ++ word_u₀))⁻¹ =
            cs.simple i * (cs.wordProd word_u₀ * cs.simple j * (cs.wordProd word_u₀)⁻¹) * cs.simple i := by
          rw [hprod_iu]; group
          have hsi_inv : cs.simple i ^ (-1 : ℤ) = cs.simple i := by
            rw [zpow_neg_one]
            exact inv_eq_of_mul_eq_one_right (cs.simple_mul_simple_self i)
          rw [hsi_inv]
        rw [hprod_prefix, hconj]

        have : w * cs.simple i * (cs.simple i * (cs.wordProd word_u₀ * cs.simple j *
            (cs.wordProd word_u₀)⁻¹) * cs.simple i) = v * cs.simple i := by
          have hsi_sq : cs.simple i * cs.simple i = 1 := cs.simple_mul_simple_self i
          rw [← htdef₀]


          calc w * cs.simple i * (cs.simple i * t * cs.simple i)
              = w * (cs.simple i * cs.simple i) * t * cs.simple i := by group
            _ = w * 1 * t * cs.simple i := by rw [hsi_sq]
            _ = (w * t) * cs.simple i := by group
            _ = v * cs.simple i := by rw [hwt_eq_v]
        rw [this]

        have hlen_vsi := not_descent_length_eq cs v i hv_asc
        have hlen_wsi := descent_length_eq cs w i hw_desc
        omega

      have hpos_prefix : CoxeterGroup.IsPositive
          (CoxeterGroup.wordSigma M prefix_ (CoxeterGroup.wordSigma M ([i] ++ word_u₀) (CoxeterGroup.e j))) :=
        CoxeterGroup.pos_of_ascent_reflection M cs prefix_ ([i] ++ word_u₀) j hred_prefix hσiα_pos hascent_len

      rw [hσiα_eq] at hneg_w

      have hzero := CoxeterSignChangeExchangeFinal.isPositive_isNegative_eq_zero hpos_prefix hneg_w

      have hform_prefix : CoxeterGroup.bilinForm M
          (CoxeterGroup.wordSigma M prefix_ (CoxeterGroup.wordSigma M ([i] ++ word_u₀) (CoxeterGroup.e j)))
          (CoxeterGroup.wordSigma M prefix_ (CoxeterGroup.wordSigma M ([i] ++ word_u₀) (CoxeterGroup.e j))) = 1 := by
        rw [CoxeterGroup.wordSigma_preserves_form, CoxeterGroup.wordSigma_preserves_form,
            CoxeterGroup.bilinForm_e_e, CoxeterGroup.formVal_diag]
      rw [hzero] at hform_prefix
      simp [CoxeterGroup.bilinForm] at hform_prefix


  have hα_eq_ei : α = CoxeterGroup.e i :=
    CoxeterSignChangeExchangeFinal.isPositive_sigma_isNegative_eq_e M i α hα_pos hσiα_neg hform_α

  have hcommute : cs.simple i * cs.wordProd word_u₀ = cs.wordProd word_u₀ * cs.simple j :=
    CoxeterSignChangeExchangeFinal.wordProd_cons_eq_append_of_wordSigma_eq_e cs word_u₀ j i
      (by rw [← hα_def]; exact hα_eq_ei)

  rw [htdef₀]
  symm
  calc cs.simple i = (cs.simple i * cs.wordProd word_u₀) * (cs.wordProd word_u₀)⁻¹ := by group
    _ = (cs.wordProd word_u₀ * cs.simple j) * (cs.wordProd word_u₀)⁻¹ := by rw [hcommute]
    _ = cs.wordProd word_u₀ * cs.simple j * (cs.wordProd word_u₀)⁻¹ := by group

/-- Unconditional inversion-difference bridge: the reflection identification core packaged. -/
theorem inversionDifferenceBridge_unconditional (M : CoxeterMatrix B) :
    InversionDifferenceBridgeHyp (M.toCoxeterSystem) :=
  ⟨fun v w t ht hvt hlen i hv hw =>
    reflection_identification_core M v w t ht hvt hlen i hv hw⟩

/-- Unconditional reflection identification hypothesis for any Coxeter matrix. -/
theorem reflectionIdentificationHyp_unconditional (M : CoxeterMatrix B) :
    CoxeterBruhat.ReflectionIdentificationHyp (M.toCoxeterSystem) :=
  reflection_identification_genuine
    (inversionDifferenceBridge_unconditional M)

/-- **Unconditional strong exchange theorem** for the Bruhat order: any Coxeter system satisfies
the strong exchange condition. -/
theorem strongExchangeForBruhat_unconditional (M : CoxeterMatrix B) :
    CoxeterBruhat.StrongExchangeForBruhat (M.toCoxeterSystem) :=
  CoxeterBruhat.strong_exchange_of_reflection_id M.toCoxeterSystem
    (reflectionIdentificationHyp_unconditional M)

end StrongExchangeUnconditional
