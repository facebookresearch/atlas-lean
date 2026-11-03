/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.YoungDiagrams
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

open Polynomial

namespace QBinomial

noncomputable def qBinom : ℕ → ℕ → Polynomial ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | k + 1, j + 1 =>
    if j + 1 > k + 1 then 0
    else qBinom k (j + 1) + (X : Polynomial ℤ) ^ (k - j) * qBinom k j

@[simp] theorem qBinom_zero_zero : qBinom 0 0 = 1 := rfl
@[simp] theorem qBinom_zero_succ (j : ℕ) : qBinom 0 (j + 1) = 0 := rfl
@[simp] theorem qBinom_succ_zero (k : ℕ) : qBinom (k + 1) 0 = 1 := rfl

@[simp] theorem qBinom_zero_right (k : ℕ) : qBinom k 0 = 1 := by
  cases k <;> simp

theorem qBinom_succ_succ_of_le (k j : ℕ) (h : j ≤ k) :
    qBinom (k + 1) (j + 1) =
      qBinom k (j + 1) + (X : Polynomial ℤ) ^ (k - j) * qBinom k j := by
  conv_lhs => unfold qBinom
  rw [if_neg (by omega : ¬ (j + 1 > k + 1))]

theorem qBinom_succ_succ_of_gt (k j : ℕ) (h : k < j) :
    qBinom (k + 1) (j + 1) = 0 := by
  conv_lhs => unfold qBinom
  rw [if_pos (by omega : j + 1 > k + 1)]

theorem qBinom_eq_zero_of_lt {k j : ℕ} (h : k < j) : qBinom k j = 0 := by
  induction k generalizing j with
  | zero =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rfl
  | succ k _ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact qBinom_succ_succ_of_gt k j (by omega)

@[simp]
theorem qBinom_self (k : ℕ) : qBinom k k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [qBinom_succ_succ_of_le k k le_rfl, qBinom_eq_zero_of_lt (by omega : k < k + 1),
        Nat.sub_self, pow_zero, one_mul, zero_add, ih]

theorem qBinom_pascal (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    qBinom k j = qBinom (k - 1) j +
      (X : Polynomial ℤ) ^ (k - j) * qBinom (k - 1) (j - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hle : j ≤ k := by omega
  have h1 : k + 1 - 1 = k := by omega
  have h2 : j + 1 - 1 = j := by omega
  have h3 : k + 1 - (j + 1) = k - j := by omega
  rw [h1, h2, h3]
  exact qBinom_succ_succ_of_le k j hle

open YoungLattice YoungLattice.Lmn

noncomputable def rankGenPoly (m n : ℕ) : Polynomial ℤ :=
  ∑ p : Lmn m n, (X : Polynomial ℤ) ^ sumParts p

theorem rankGenPoly_zero_left (n : ℕ) : rankGenPoly 0 n = 1 := by
  classical
  simp only [rankGenPoly]
  have huniq : ∀ (p : Lmn 0 n), p = ⟨Fin.elim0, fun a => a.elim0⟩ := by
    intro p; ext i; exact i.elim0
  rw [show (Finset.univ : Finset (Lmn 0 n)) = {⟨Fin.elim0, fun a => a.elim0⟩} from by
    ext p; simp [huniq p]]
  simp [sumParts]

theorem rankGenPoly_zero_right (m : ℕ) : rankGenPoly m 0 = 1 := by
  classical
  simp only [rankGenPoly]
  have huniq : ∀ (p : Lmn m 0), p = ⟨fun _ => 0, fun _ _ _ => le_refl _⟩ := by
    intro p; apply Lmn.ext; intro i
    exact Fin.ext (by have := (p.val i).isLt; omega)
  rw [show (Finset.univ : Finset (Lmn m 0)) = {⟨fun _ => 0, fun _ _ _ => le_refl _⟩} from by
    ext p; simp [huniq p]]
  simp [sumParts]

theorem rankGenPoly_succ_succ (m n : ℕ) :
    rankGenPoly (m + 1) (n + 1) =
      rankGenPoly (m + 1) n + (X : Polynomial ℤ) ^ (n + 1) * rankGenPoly m (n + 1) := by
  let fwd : Lmn (m + 1) (n + 1) → Lmn (m + 1) n ⊕ Lmn m (n + 1) := fun p =>
    if h : (p.val 0).val < n + 1
    then Sum.inl ⟨fun i => ⟨(p.val i).val, lt_of_le_of_lt (p.property (Fin.zero_le i)) h⟩,
      fun a b hab => p.property hab⟩
    else Sum.inr ⟨fun i => p.val i.succ,
      fun a b hab => p.property (Fin.succ_le_succ_iff.mpr hab)⟩
  let bwd : Lmn (m + 1) n ⊕ Lmn m (n + 1) → Lmn (m + 1) (n + 1) := fun
    | Sum.inl q => ⟨fun i => ⟨(q.val i).val, by have := (q.val i).isLt; omega⟩,
        fun a b hab => q.property hab⟩
    | Sum.inr q => ⟨fun i =>
        if hi : i = 0 then Fin.last (n + 1)
        else q.val ⟨i.val - 1, by have := i.isLt; omega⟩,
        fun a b hab => by
          by_cases ha : a = 0
          · subst ha; exact Fin.le_last _
          · by_cases hb : b = 0
            · subst hb; exact absurd hab (not_le.mpr (Fin.pos_iff_ne_zero.mpr ha))
            · simp only [ha, hb, ↓reduceDIte]
              apply q.property; simp only [Fin.le_def]; omega⟩
  have hleft_inv : ∀ p, bwd (fwd p) = p := by
    intro p; dsimp only [fwd, bwd]
    split_ifs with h
    · apply Lmn.ext; intro i; exact Fin.ext rfl
    · apply Lmn.ext; intro i
      by_cases hi : i = 0
      · subst hi; simp only [↓reduceDIte]
        exact Fin.ext (by simp only [Fin.val_last]; have := (p.val 0).isLt; omega)
      · simp only [hi, ↓reduceDIte]
        have hne : i.val ≠ 0 := Fin.val_ne_of_ne hi
        have harg : (⟨i.val - 1, by omega⟩ : Fin m).succ = i :=
          Fin.ext (by simp only [Fin.val_succ]; omega)
        exact congrArg p.val harg
  have hright_inv : ∀ s, fwd (bwd s) = s := by
    intro s; rcases s with q | q
    · dsimp only [fwd, bwd]
      have h : (q.val 0).val < n + 1 := (q.val 0).isLt
      simp only [h, ↓reduceDIte]
      exact congrArg Sum.inl (Lmn.ext (fun i => Fin.ext rfl))
    · dsimp only [fwd, bwd]
      have h : ¬ (Fin.last (n + 1)).val < n + 1 := by simp [Fin.val_last]
      simp only [h, ↓reduceDIte]
      exact congrArg Sum.inr (Lmn.ext (fun i => by
        simp only [Fin.succ_ne_zero, ↓reduceDIte, Fin.val_succ, Nat.add_sub_cancel]))
  let e : Lmn (m + 1) (n + 1) ≃ Lmn (m + 1) n ⊕ Lmn m (n + 1) :=
    ⟨fwd, bwd, hleft_inv, hright_inv⟩
  have hsp_inl : ∀ q : Lmn (m + 1) n,
      (e.symm (Sum.inl q)).sumParts = q.sumParts := by
    intro q; simp only [e, Equiv.symm, bwd, sumParts]; rfl
  have hsp_inr : ∀ q : Lmn m (n + 1),
      (e.symm (Sum.inr q)).sumParts = (n + 1) + q.sumParts := by
    intro q
    show (∑ i : Fin (m + 1), ((bwd (Sum.inr q)).val i).val) = (n + 1) + q.sumParts
    change (∑ i : Fin (m + 1), ((if hi : i = 0 then Fin.last (n + 1)
        else q.val ⟨i.val - 1, _⟩) : Fin (n + 2)).val) = (n + 1) + q.sumParts
    rw [Fin.sum_univ_succ]
    simp [↓reduceDIte, Fin.val_last, sumParts, Fin.succ_ne_zero, Fin.val_succ]
  show rankGenPoly (m + 1) (n + 1) =
    rankGenPoly (m + 1) n + X ^ (n + 1) * rankGenPoly m (n + 1)
  unfold rankGenPoly
  conv_lhs => rw [show ∑ p : Lmn (m+1) (n+1), X ^ p.sumParts =
    ∑ s : Lmn (m+1) n ⊕ Lmn m (n+1), X ^ (e.symm s).sumParts from
    (Equiv.sum_comp e.symm _).symm]
  rw [Fintype.sum_sum_type]
  simp_rw [hsp_inl, hsp_inr, pow_add, ← Finset.mul_sum]

theorem qBinom_recurrence (m n : ℕ) :
    qBinom ((m + 1) + (n + 1)) (m + 1) =
      qBinom ((m + 1) + n) (m + 1) +
      (X : Polynomial ℤ) ^ (n + 1) * qBinom (m + (n + 1)) m := by
  rw [show (m + 1) + (n + 1) = (m + n + 1) + 1 from by omega,
      qBinom_succ_succ_of_le (m + n + 1) m (by omega)]
  congr 1
  · congr 1; omega
  · have h3 : m + n + 1 - m = n + 1 := by omega
    have h4 : m + (n + 1) = m + n + 1 := by omega
    rw [h3, h4]

theorem rankGenPoly_eq_qBinom (m n : ℕ) :
    rankGenPoly m n = qBinom (m + n) m := by
  induction m generalizing n with
  | zero =>
    simp only [Nat.zero_add]
    rw [rankGenPoly_zero_left, qBinom_zero_right]
  | succ m ihm =>
    induction n with
    | zero =>
      rw [rankGenPoly_zero_right]
      simp
    | succ n ihn =>
      rw [rankGenPoly_succ_succ, ihm (n + 1), ihn, qBinom_recurrence]

end QBinomial
