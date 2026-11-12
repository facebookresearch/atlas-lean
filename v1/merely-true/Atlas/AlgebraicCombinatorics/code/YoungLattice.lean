/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.Order.Cover
import Mathlib.Order.Grade
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring

set_option autoImplicit false

open SpernerProperty

namespace YoungLattice

def Lmn (m n : ℕ) : Type :=
  {f : Fin m → Fin (n + 1) // Antitone f}

namespace Lmn

instance instPartialOrder (m n : ℕ) : PartialOrder (Lmn m n) :=
  Subtype.partialOrder _

noncomputable instance instDecidableEq (m n : ℕ) : DecidableEq (Lmn m n) :=
  Classical.decEq _

noncomputable instance instFintype (m n : ℕ) : Fintype (Lmn m n) := by
  classical
  exact Fintype.subtype (Finset.univ.filter (fun f : Fin m → Fin (n + 1) => Antitone f))
    (fun f => by simp [Finset.mem_filter])

@[ext]
lemma ext {m n : ℕ} {p q : Lmn m n} (h : ∀ i, p.val i = q.val i) : p = q :=
  Subtype.ext (funext h)

def sumParts {m n : ℕ} (p : Lmn m n) : ℕ :=
  ∑ i : Fin m, (p.val i).val

def zero (m n : ℕ) : Lmn m n :=
  ⟨fun _ => 0, fun _ _ _ => le_refl _⟩

def top (m n : ℕ) : Lmn m n :=
  ⟨fun _ => Fin.last n, fun _ _ _ => le_refl _⟩

lemma zero_le {m n : ℕ} (p : Lmn m n) : zero m n ≤ p :=
  fun _ => Fin.zero_le _

lemma sumParts_zero {m n : ℕ} : sumParts (zero m n) = 0 := by
  simp [sumParts, zero]

lemma sumParts_top {m n : ℕ} : sumParts (top m n) = m * n := by
  simp only [sumParts, top, Fin.val_last]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

lemma isMin_iff {m n : ℕ} {p : Lmn m n} : IsMin p ↔ p = zero m n := by
  constructor
  · intro h
    have hle := h (zero_le p)
    ext i; exact le_antisymm (hle i) (zero_le p i)
  · rintro rfl; intro q _; exact zero_le q

lemma sumParts_strictMono {m n : ℕ} : StrictMono (sumParts (m := m) (n := n)) := by
  intro ⟨p, hp⟩ ⟨q, hq⟩ hlt
  simp only [sumParts]
  have hle : p ≤ q := le_of_lt hlt
  have hne : p ≠ q := ne_of_lt hlt
  have : ∃ i, p i < q i := by
    by_contra h; push Not at h
    exact hne (funext fun i => le_antisymm (hle i) (h i))
  obtain ⟨j, hj⟩ := this
  exact Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ _, hj⟩

lemma exists_between {m n : ℕ} {p q : Lmn m n}
    (hle : ∀ i, p.val i ≤ q.val i) (hne : p ≠ q)
    (hge2 : sumParts q ≥ sumParts p + 2) :
    ∃ r : Lmn m n, p ≤ r ∧ r < q ∧ p ≠ r := by
  have hdiff : ∃ j, p.val j < q.val j := by
    by_contra hc; push Not at hc
    exact hne (ext fun i => le_antisymm (hle i) (hc i))
  let S := Finset.univ.filter (fun j : Fin m => p.val j < q.val j)
  have hS_ne : S.Nonempty := by
    obtain ⟨j, hj⟩ := hdiff
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let j := S.max' hS_ne
  have hj_lt : p.val j < q.val j := (Finset.mem_filter.mp (Finset.max'_mem S hS_ne)).2
  have hj_max : ∀ k, p.val k < q.val k → k ≤ j :=
    fun k hk => Finset.le_max' S k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
  have hj_eq : ∀ i, j < i → p.val i = q.val i := by
    intro i hi; by_contra hne_i
    exact not_lt.mpr (hj_max i (lt_of_le_of_ne (hle i) hne_i)) hi
  have hqj_pos : 0 < (q.val j).val := by omega
  let nv : Fin (n+1) := ⟨(q.val j).val - 1, by omega⟩
  have hnv_val : nv.val = (q.val j).val - 1 := rfl
  have hnv_ne_qj : nv ≠ q.val j := by
    intro h; exact absurd (congr_arg Fin.val h) (by omega)
  let rval := Function.update q.val j nv
  have hrval_j : rval j = nv := Function.update_self j nv q.val
  have hrval_ne : ∀ i, i ≠ j → rval i = q.val i :=
    fun i hi => Function.update_of_ne hi nv q.val
  have hr_anti : Antitone rval := by
    intro a b hab
    by_cases ha : a = j <;> by_cases hb : b = j
    · subst ha; subst hb; exact le_refl _
    · subst ha; rw [hrval_j, hrval_ne b hb, Fin.le_def, hnv_val]
      have hb_gt : j < b := lt_of_le_of_ne hab (fun h => hb h.symm)
      have h1 := congr_arg Fin.val (hj_eq b hb_gt).symm
      have h2 : (p.val b).val ≤ (p.val j).val := p.property hab
      omega
    · subst hb; rw [hrval_j, hrval_ne a ha, Fin.le_def, hnv_val]
      have : (q.val j).val ≤ (q.val a).val := q.property hab; omega
    · rw [hrval_ne a ha, hrval_ne b hb]; exact q.property hab
  let r : Lmn m n := ⟨rval, hr_anti⟩
  refine ⟨r, ?_, ?_, ?_⟩
  · intro i; by_cases hi : i = j
    · subst hi; show p.val j ≤ rval j; rw [hrval_j, Fin.le_def, hnv_val]; omega
    · show p.val i ≤ rval i; rw [hrval_ne i hi]; exact hle i
  · refine lt_of_le_of_ne ?_ ?_
    · intro i; by_cases hi : i = j
      · subst hi; show rval j ≤ q.val j; rw [hrval_j, Fin.le_def, hnv_val]; omega
      · show rval i ≤ q.val i; rw [hrval_ne i hi]
    · intro heq
      have : rval j = q.val j := congr_fun (Subtype.ext_iff.mp heq) j
      rw [hrval_j] at this; exact hnv_ne_qj this
  · intro heq
    have h_eq_fn : ∀ i, p.val i = rval i := fun i => congr_fun (Subtype.ext_iff.mp heq) i
    have h_other : ∀ i, i ≠ j → (p.val i).val = (q.val i).val := by
      intro i hi; rw [show p.val i = rval i from h_eq_fn i, hrval_ne i hi]
    have h_j_val : (p.val j).val = (q.val j).val - 1 := by
      have := h_eq_fn j; rw [hrval_j] at this; exact congr_arg Fin.val this
    have sum_diff_one : sumParts q = sumParts p + 1 := by
      simp only [sumParts]
      have hterm : ∀ i, (q.val i).val = (p.val i).val + if i = j then 1 else 0 := by
        intro i; by_cases hi : i = j
        · subst hi; simp; omega
        · simp [hi, h_other i hi]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
      rw [Finset.sum_eq_single j (fun b _ hb => if_neg hb)
        (fun h => absurd (Finset.mem_univ j) h)]
      simp
    omega

lemma covBy_sumParts {m n : ℕ} {p q : Lmn m n} (h : p ⋖ q) :
    sumParts p ⋖ sumParts q := by
  suffices sumParts q = sumParts p + 1 by rw [this]; exact Order.covBy_succ _
  have hlt := h.lt
  have hle : ∀ i, p.val i ≤ q.val i := le_of_lt hlt
  have hne : p ≠ q := ne_of_lt hlt
  have hlt_sum := sumParts_strictMono hlt
  by_contra hne_sum
  have hge2 : sumParts q ≥ sumParts p + 2 := by omega
  obtain ⟨r, hp_le_r, hr_lt_q, hp_ne_r⟩ := exists_between hle hne hge2
  exact h.2 (lt_of_le_of_ne hp_le_r hp_ne_r) hr_lt_q

lemma isMin_sumParts {m n : ℕ} {p : Lmn m n} (h : IsMin p) :
    IsMin (sumParts p) := by
  rw [isMin_iff] at h; subst h; rw [sumParts_zero]; exact isMin_bot

instance instGradeOrder (m n : ℕ) : GradeOrder ℕ (Lmn m n) :=
  GradeOrder.mk sumParts sumParts_strictMono (fun {_ _} h => covBy_sumParts h)

instance instGradeMinOrder (m n : ℕ) : GradeMinOrder ℕ (Lmn m n) :=
  GradeMinOrder.mk (fun {_} h => isMin_sumParts h)

lemma grade_eq {m n : ℕ} (p : Lmn m n) : grade ℕ p = sumParts p := rfl

def complement {m n : ℕ} (p : Lmn m n) : Lmn m n :=
  ⟨fun i => ⟨n - (p.val (Fin.rev i)).val, by omega⟩,
   fun a b hab => by
    simp only [Fin.le_def]
    have := p.property (Fin.rev_le_rev.mpr hab); omega⟩

lemma complement_complement {m n : ℕ} (p : Lmn m n) :
    p.complement.complement = p := by
  apply ext; intro i
  show (complement (complement p)).val i = p.val i
  simp only [complement, Fin.rev_rev]
  apply Fin.ext; simp only []
  have := (p.val i).isLt; omega

lemma complement_injective {m n : ℕ} : Function.Injective (complement (m := m) (n := n)) := by
  intro p q h
  have := congr_arg complement h
  rwa [complement_complement, complement_complement] at this

lemma sumParts_complement_add {m n : ℕ} (p : Lmn m n) :
    sumParts p.complement + sumParts p = m * n := by
  unfold sumParts complement
  have hreindex : ∑ x : Fin m, (p.val x).val = ∑ x : Fin m, (p.val (Fin.rev x)).val :=
    Fintype.sum_equiv Fin.revPerm (fun x => (p.val x).val) (fun x => (p.val (Fin.rev x)).val)
      (fun i => by simp [Fin.revPerm])
  rw [hreindex, ← Finset.sum_add_distrib]
  simp_rw [Nat.sub_add_cancel (Nat.lt_succ_iff.mp (p.val (Fin.rev _)).isLt)]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

lemma grade_complement {m n : ℕ} (p : Lmn m n) :
    grade ℕ p.complement = m * n - grade ℕ p := by
  rw [grade_eq, grade_eq]; have := sumParts_complement_add p; omega

lemma grade_le_mul {m n : ℕ} (p : Lmn m n) : grade ℕ p ≤ m * n := by
  rw [grade_eq]; have := sumParts_complement_add p; omega

instance instGradedPoset (m n : ℕ) : GradedPoset (Lmn m n) where
  rank := m * n
  grade_le_rank := grade_le_mul
  grade_rank_exists := ⟨top m n, by rw [grade_eq, sumParts_top]⟩

theorem Lmn_isRankSymmetric (m n : ℕ) : IsRankSymmetric (α := Lmn m n) := by
  intro i hi
  have hrank : GradedPoset.rank (α := Lmn m n) = m * n := rfl
  rw [hrank] at hi ⊢
  unfold rankCount
  apply Finset.card_nbij complement
  ·
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
               true_and] at hp ⊢
    rw [grade_complement, hp]
  ·
    intro p _ q _ h
    exact complement_injective h
  ·
    intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
               true_and, Set.mem_image] at hq ⊢
    refine ⟨q.complement, ?_, complement_complement q⟩
    rw [grade_complement]
    have h_le := grade_le_mul q
    omega

end Lmn

end YoungLattice
