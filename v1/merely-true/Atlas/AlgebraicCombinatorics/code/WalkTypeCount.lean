/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.HasseWalks
import Atlas.AlgebraicCombinatorics.code.HasseWalkFormula
import Atlas.AlgebraicCombinatorics.code.WalkOperatorLemmas
import Atlas.AlgebraicCombinatorics.code.WalkCountOps
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

open scoped Nat
open HasseWalks

noncomputable section

namespace WalkTypeCount

def runningLevel (w : List HStep) (k : ℕ) : ℤ :=
  ((w.take k).filter (· == HStep.U)).length -
  ((w.take k).filter (· == HStep.D)).length

def IsValidStepWord (w : List HStep) (n : ℕ) : Prop :=
  runningLevel w w.length = (n : ℤ) ∧
  ∀ k : ℕ, k ≤ w.length → 0 ≤ runningLevel w k

def walkTypeCount (w : List HStep) (lam : YoungDiagram) : ℕ := by
  classical
  exact Nat.card (HasseWalk w ⊥ lam)

def downPositions (w : List HStep) : Finset (Fin w.length) :=
  Finset.univ.filter (fun i => w[i] = HStep.D)

def numDRight (w : List HStep) (i : Fin w.length) : ℕ :=
  ((w.take i.val).filter (· == HStep.D)).length

def numURight (w : List HStep) (i : Fin w.length) : ℕ :=
  ((w.take i.val).filter (· == HStep.U)).length

def downStepProduct (w : List HStep) : ℤ :=
  ∏ i ∈ downPositions w,
    ((numURight w i : ℤ) - (numDRight w i : ℤ))

def applyStepWord : List HStep → (YoungDiagram →₀ ℤ) → (YoungDiagram →₀ ℤ)
  | [], f => f
  | HStep.U :: rest, f => applyStepWord rest (WalkCountFormula.liftU f)
  | HStep.D :: rest, f => applyStepWord rest (WalkCountFormula.liftD f)

theorem applyStepWord_add (w : List HStep) (f g : YoungDiagram →₀ ℤ) :
    applyStepWord w (f + g) = applyStepWord w f + applyStepWord w g := by
  induction w generalizing f g with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | U =>
      show applyStepWord rest (WalkCountFormula.liftU (f + g)) =
        applyStepWord rest (WalkCountFormula.liftU f) +
        applyStepWord rest (WalkCountFormula.liftU g)
      rw [map_add]; exact ih _ _
    | D =>
      show applyStepWord rest (WalkCountFormula.liftD (f + g)) =
        applyStepWord rest (WalkCountFormula.liftD f) +
        applyStepWord rest (WalkCountFormula.liftD g)
      rw [map_add]; exact ih _ _

theorem applyStepWord_smul (w : List HStep) (c : ℤ) (f : YoungDiagram →₀ ℤ) :
    applyStepWord w (c • f) = c • applyStepWord w f := by
  induction w generalizing f with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | U =>
      show applyStepWord rest (WalkCountFormula.liftU (c • f)) =
        c • applyStepWord rest (WalkCountFormula.liftU f)
      rw [map_smul]; exact ih _
    | D =>
      show applyStepWord rest (WalkCountFormula.liftD (c • f)) =
        c • applyStepWord rest (WalkCountFormula.liftD f)
      rw [map_smul]; exact ih _

theorem applyStepWord_zero (w : List HStep) :
    applyStepWord w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | U =>
      show applyStepWord rest (WalkCountFormula.liftU 0) = 0
      rw [map_zero]; exact ih
    | D =>
      show applyStepWord rest (WalkCountFormula.liftD 0) = 0
      rw [map_zero]; exact ih

def downFactor : List HStep → ℕ → ℤ
  | [], _ => 1
  | HStep.U :: rest, m => downFactor rest (m + 1)
  | HStep.D :: rest, m => (m : ℤ) * downFactor rest (m - 1)

def finalLevel : List HStep → ℕ → ℕ
  | [], m => m
  | HStep.U :: rest, m => finalLevel rest (m + 1)
  | HStep.D :: rest, m => finalLevel rest (m - 1)

set_option maxHeartbeats 400000 in
theorem applyStepWord_smul_iterU_emptyBasis
    (w : List HStep) (c : ℤ) (m : ℕ) :
    applyStepWord w (c • WalkCountFormula.iterU m WalkCountFormula.emptyBasis) =
      (c * downFactor w m) • WalkCountFormula.iterU (finalLevel w m) WalkCountFormula.emptyBasis := by
  induction w generalizing c m with
  | nil =>
    simp only [applyStepWord, downFactor, finalLevel, mul_one]
  | cons s rest ih =>
    cases s with
    | U =>
      show applyStepWord rest (WalkCountFormula.liftU (c • WalkCountFormula.iterU m WalkCountFormula.emptyBasis)) = _
      rw [map_smul, ← LinearMap.comp_apply, ← WalkCountFormula.iterU_succ']
      exact ih c (m + 1)
    | D =>
      show applyStepWord rest (WalkCountFormula.liftD (c • WalkCountFormula.iterU m WalkCountFormula.emptyBasis)) = _
      rw [map_smul, WalkCountFormula.liftD_iterU_emptyBasis, ← mul_smul]
      rw [ih (c * (m : ℤ)) (m - 1)]
      simp only [downFactor, finalLevel]; ring_nf

theorem applyStepWord_emptyBasis_eq (w : List HStep) :
    applyStepWord w WalkCountFormula.emptyBasis =
      downFactor w 0 • WalkCountFormula.iterU (finalLevel w 0) WalkCountFormula.emptyBasis := by
  have h := applyStepWord_smul_iterU_emptyBasis w 1 0
  simp only [WalkCountFormula.iterU_zero, LinearMap.id_apply, one_smul, one_mul] at h
  exact h

@[simp]
theorem runningLevel_zero (w : List HStep) : runningLevel w 0 = 0 := by
  simp [runningLevel]

theorem runningLevel_cons_U_succ (rest : List HStep) (k : ℕ) :
    runningLevel (HStep.U :: rest) (k + 1) = 1 + runningLevel rest k := by
  simp only [runningLevel, List.take_succ_cons, List.filter_cons, beq_iff_eq]
  simp (config := { decide := true }) only [ite_true, ite_false, List.length_cons]
  push_cast; ring

theorem runningLevel_cons_D_succ (rest : List HStep) (k : ℕ) :
    runningLevel (HStep.D :: rest) (k + 1) = runningLevel rest k - 1 := by
  simp only [runningLevel, List.take_succ_cons, List.filter_cons, beq_iff_eq]
  simp (config := { decide := true }) only [ite_true, ite_false, List.length_cons]
  push_cast; ring

set_option maxHeartbeats 400000 in
theorem finalLevel_eq_of_valid (w : List HStep) (m : ℕ)
    (hvalid : ∀ k : ℕ, k ≤ w.length → 0 ≤ (m : ℤ) + runningLevel w k) :
    (finalLevel w m : ℤ) = (m : ℤ) + runningLevel w w.length := by
  induction w generalizing m with
  | nil => simp [finalLevel, runningLevel]
  | cons s rest ih =>
    cases s with
    | U =>
      simp only [finalLevel, List.length_cons]
      have hvalid' : ∀ k : ℕ, k ≤ rest.length →
          0 ≤ ((m + 1 : ℕ) : ℤ) + runningLevel rest k := by
        intro k hk
        have := hvalid (k + 1) (by simp [List.length_cons]; omega)
        rw [runningLevel_cons_U_succ] at this
        push_cast at this ⊢; linarith
      rw [ih (m + 1) hvalid', runningLevel_cons_U_succ]
      push_cast; ring
    | D =>
      simp only [finalLevel, List.length_cons]
      have hm_pos : 1 ≤ (m : ℤ) := by
        have := hvalid 1 (by simp [List.length_cons])
        rw [runningLevel_cons_D_succ] at this
        simp only [runningLevel_zero] at this; linarith
      have hvalid' : ∀ k : ℕ, k ≤ rest.length →
          0 ≤ ((m - 1 : ℕ) : ℤ) + runningLevel rest k := by
        intro k hk
        have := hvalid (k + 1) (by simp only [List.length_cons]; omega)
        rw [runningLevel_cons_D_succ] at this
        omega
      rw [ih (m - 1) hvalid', runningLevel_cons_D_succ]
      omega

theorem numURight_sub_numDRight_eq_runningLevel (w : List HStep) (i : Fin w.length) :
    (numURight w i : ℤ) - (numDRight w i : ℤ) = runningLevel w i.val := by
  simp only [numURight, numDRight, runningLevel]

theorem downStepProduct_eq_prod_runningLevel (w : List HStep) :
    downStepProduct w = ∏ i ∈ downPositions w, runningLevel w i.val := by
  simp only [downStepProduct, numURight_sub_numDRight_eq_runningLevel]

set_option maxHeartbeats 400000 in
theorem downFactor_eq_downStepProduct_offset (w : List HStep) (m : ℕ)
    (hvalid : ∀ k : ℕ, k ≤ w.length → 0 ≤ (m : ℤ) + runningLevel w k) :
    downFactor w m = ∏ i ∈ downPositions w, ((m : ℤ) + runningLevel w i.val) := by
  induction w generalizing m with
  | nil =>
    simp [downFactor, downPositions]
  | cons s rest ih =>
    cases s with
    | U =>
      simp only [downFactor]
      have hvalid' : ∀ k, k ≤ rest.length →
          0 ≤ ((m + 1 : ℕ) : ℤ) + runningLevel rest k := by
        intro k hk
        have := hvalid (k + 1) (by simp [List.length_cons]; omega)
        rw [runningLevel_cons_U_succ] at this; push_cast at this ⊢; linarith
      rw [ih (m + 1) hvalid']
      apply Finset.prod_nbij (fun (i : Fin rest.length) => (⟨i.val + 1, by simp [List.length_cons]⟩ : Fin (HStep.U :: rest).length))
      · intro ⟨i, hi_lt⟩ hi_mem
        simp only [downPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hi_mem ⊢
        show (HStep.U :: rest)[i + 1]'(by simp [List.length_cons]; omega) = HStep.D
        simp only [List.getElem_cons_succ]
        exact hi_mem
      · intro i _ j _ h; simp [Fin.ext_iff] at h; exact Fin.ext (by omega)
      · intro ⟨j, hj⟩ hj_mem
        simp only [downPositions, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_image,
          Finset.mem_coe] at hj_mem ⊢
        cases j with
        | zero =>
          exfalso
          have : HStep.U = HStep.D := by simp at hj_mem
          exact HStep.noConfusion this
        | succ j' =>
          have hj' : j' < rest.length := by simp [List.length_cons] at hj; omega
          refine ⟨⟨j', hj'⟩, ?_, by simp⟩
          have hd : (HStep.U :: rest)[j' + 1] = HStep.D := by simp at hj_mem; exact hj_mem
          simpa [downPositions, Finset.mem_filter, List.getElem_cons_succ] using hd
      · intro ⟨i, hi_lt⟩ _
        simp only [runningLevel_cons_U_succ]; push_cast; ring
    | D =>
      simp only [downFactor]
      have hm_pos : 1 ≤ (m : ℤ) := by
        have := hvalid 1 (by simp [List.length_cons])
        rw [runningLevel_cons_D_succ] at this
        simp only [runningLevel_zero] at this; linarith
      have hvalid' : ∀ k, k ≤ rest.length →
          0 ≤ ((m - 1 : ℕ) : ℤ) + runningLevel rest k := by
        intro k hk
        have := hvalid (k + 1) (by simp only [List.length_cons]; omega)
        rw [runningLevel_cons_D_succ] at this; omega
      rw [ih (m - 1) hvalid']
      have h0_mem : (⟨0, by simp⟩ : Fin (HStep.D :: rest).length) ∈ downPositions (HStep.D :: rest) := by
        simp only [downPositions, Finset.mem_filter, Finset.mem_univ, true_and]
        show (HStep.D :: rest)[0] = HStep.D
        simp
      rw [← Finset.mul_prod_erase _ _ h0_mem]
      have : (↑m + runningLevel (HStep.D :: rest) 0) = (m : ℤ) := by simp [runningLevel]
      rw [this]
      congr 1
      apply Finset.prod_nbij (fun (i : Fin rest.length) => (⟨i.val + 1, by simp [List.length_cons]⟩ : Fin (HStep.D :: rest).length))
      · intro ⟨i, hi_lt⟩ hi_mem
        simp only [downPositions, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, ne_eq, Fin.ext_iff] at hi_mem ⊢
        constructor
        · omega
        · show (HStep.D :: rest)[i + 1]'(by simp [List.length_cons]; exact hi_lt) = HStep.D
          simp only [List.getElem_cons_succ]; exact hi_mem
      · intro i _ j _ h; simp [Fin.ext_iff] at h; exact Fin.ext (by omega)
      · intro ⟨j, hj⟩ hj_mem
        simp only [downPositions, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
          true_and, Set.mem_image, Finset.mem_coe, Fin.ext_iff, ne_eq] at hj_mem ⊢
        obtain ⟨hne, hd⟩ := hj_mem
        cases j with
        | zero => exact absurd rfl hne
        | succ j' =>
          have hj' : j' < rest.length := by simp [List.length_cons] at hj; omega
          refine ⟨⟨j', hj'⟩, ?_, by simp⟩
          have hd' : (HStep.D :: rest)[j' + 1] = HStep.D := by simp at hd; exact hd
          simpa [downPositions, Finset.mem_filter, List.getElem_cons_succ] using hd'
      · intro ⟨i, hi_lt⟩ _
        simp only [runningLevel_cons_D_succ]; omega

theorem downFactor_zero_eq_downStepProduct (w : List HStep)
    (hvalid : ∀ k : ℕ, k ≤ w.length → 0 ≤ runningLevel w k) :
    downFactor w 0 = downStepProduct w := by
  rw [downFactor_eq_downStepProduct_offset w 0 (by simpa using hvalid)]
  rw [downStepProduct_eq_prod_runningLevel]
  simp only [Nat.cast_zero, zero_add]

end WalkTypeCount

end






noncomputable section

open HasseWalks

namespace WalkTypeCount

lemma applyStepWord_finset_sum_single
    (w : List HStep) (S : Finset YoungDiagram) :
    applyStepWord w (S.sum (fun σ => Finsupp.single σ 1)) =
      S.sum (fun σ => applyStepWord w (Finsupp.single σ 1)) := by
  classical
  induction S using Finset.cons_induction_on with
  | empty => simp [applyStepWord_zero]
  | cons a S hnotin ih =>
    rw [Finset.sum_cons, applyStepWord_add, ih, Finset.sum_cons]


end WalkTypeCount

end


theorem WalkTypeCount.applyStepWord_emptyBasis_eq_downStepProduct_smul_iterU
    (w : List HasseWalks.HStep) (n : ℕ)
    (hw : WalkTypeCount.IsValidStepWord w n) :
    WalkTypeCount.applyStepWord w WalkCountFormula.emptyBasis =
      WalkTypeCount.downStepProduct w • WalkCountFormula.iterU n WalkCountFormula.emptyBasis := by
  open WalkTypeCount in
  rw [applyStepWord_emptyBasis_eq]
  congr 1
  · exact downFactor_zero_eq_downStepProduct w hw.2
  · have hfl := finalLevel_eq_of_valid w 0 (by simpa using hw.2)
    simp only [Nat.cast_zero, zero_add] at hfl; rw [hw.1] at hfl
    have : finalLevel w 0 = n := by exact_mod_cast hfl
    rw [this]

noncomputable section

open HasseWalks

namespace WalkTypeCount

theorem iterU_emptyBasis_coeff_eq_numSYT (lam : YoungDiagram) :
    (WalkCountFormula.iterU lam.card WalkCountFormula.emptyBasis) lam =
      (HasseWalkFormula.numSYT lam : ℤ) := by
  have h1 := HasseWalkFormula.upWalkCount_eq_iterU_apply lam.card lam
  have h2 := HasseWalkFormula.upWalkCount_eq_numSYT lam
  have h2_nat : HasseWalkFormula.upWalkCount lam.card lam = HasseWalkFormula.numSYT lam := by
    exact_mod_cast h2
  rw [← h1]; exact_mod_cast h2_nat


end WalkTypeCount

end
