/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.YoungLattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false

namespace YoungLattice

namespace Lmn

def shiftDown {m n : ℕ} (p : Lmn (m + 1) (n + 1)) (h : p.val (Fin.last m) ≠ 0) :
    Lmn (m + 1) n :=
  ⟨fun i => ⟨(p.val i).val - 1, by
    have hpos : 0 < (p.val (Fin.last m)).val := Fin.pos_iff_ne_zero.mpr h
    have hle := p.property (Fin.le_last i); have := (p.val i).isLt; omega⟩,
   fun a b hab => by simp only [Fin.le_def]; have := p.property hab; omega⟩

def shiftUp {m n : ℕ} (q : Lmn (m + 1) n) : Lmn (m + 1) (n + 1) :=
  ⟨fun i => ⟨(q.val i).val + 1, by have := (q.val i).isLt; omega⟩,
   fun a b hab => by simp only [Fin.le_def]; have := q.property hab; omega⟩

def restrictToInit {m n : ℕ} (p : Lmn (m + 1) (n + 1))
    (_h : p.val (Fin.last m) = 0) : Lmn m (n + 1) :=
  ⟨fun i => p.val (Fin.castSucc i),
   fun _ _ hab => p.property (Fin.castSucc_le_castSucc_iff.mpr hab)⟩

def extendZero {m n : ℕ} (q : Lmn m (n + 1)) : Lmn (m + 1) (n + 1) :=
  ⟨Fin.snoc q.val (0 : Fin (n + 2)),
   fun a b (hab : a ≤ b) => by
    rcases Fin.eq_castSucc_or_eq_last b with ⟨j, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact q.property (Fin.castSucc_le_castSucc_iff.mp hab)
      · exact absurd hab (not_le.mpr (Fin.castSucc_lt_last j))
    · simp only [Fin.snoc_last]; exact Fin.zero_le _⟩

lemma extendZero_last {m n : ℕ} (q : Lmn m (n + 1)) :
    (extendZero q).val (Fin.last m) = 0 := by
  simp [extendZero, Fin.snoc_last]

lemma shiftUp_last_ne_zero {m n : ℕ} (q : Lmn (m + 1) n) :
    (shiftUp q).val (Fin.last m) ≠ 0 := by
  simp only [shiftUp, ne_eq, Fin.ext_iff, Fin.val_zero]; omega

noncomputable def sumEquiv (m n : ℕ) :
    Lmn (m + 1) (n + 1) ≃ Lmn m (n + 1) ⊕ Lmn (m + 1) n := by
  classical
  exact
  { toFun := fun p =>
      if h : p.val (Fin.last m) = 0 then Sum.inl (restrictToInit p h)
      else Sum.inr (shiftDown p h)
    invFun := fun | Sum.inl q => extendZero q | Sum.inr q => shiftUp q
    left_inv := by
      intro p; simp only; split_ifs with h
      · apply Lmn.ext; intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp [extendZero, restrictToInit, Fin.snoc_castSucc]
        · simp only [extendZero, Fin.snoc_last]; exact h.symm
      · apply Lmn.ext; intro i
        simp only [shiftUp, shiftDown]; apply Fin.ext; simp only []
        have hpos : 0 < (p.val (Fin.last m)).val := Fin.pos_iff_ne_zero.mpr h
        have hle := p.property (Fin.le_last i); omega
    right_inv := by
      intro s; rcases s with q | q
      · simp only
        have h := extendZero_last q; simp only [h, ↓reduceDIte]
        exact congrArg Sum.inl (by
          apply Lmn.ext; intro i
          simp [restrictToInit, extendZero, Fin.snoc_castSucc])
      · simp only
        have h := shiftUp_last_ne_zero q; simp only [h, ↓reduceDIte]
        exact congrArg Sum.inr (by
          apply Lmn.ext; intro i
          simp only [shiftDown, shiftUp]
          apply Fin.ext; simp only []; omega) }

lemma card_succ_succ (m n : ℕ) :
    Fintype.card (Lmn (m + 1) (n + 1)) =
    Fintype.card (Lmn m (n + 1)) + Fintype.card (Lmn (m + 1) n) := by
  classical
  rw [Fintype.card_congr (sumEquiv m n), Fintype.card_sum]

lemma card_zero (n : ℕ) : Fintype.card (Lmn 0 n) = 1 := by
  haveI : Unique (Lmn 0 n) :=
    ⟨⟨⟨Fin.elim0, fun a => a.elim0⟩⟩, fun a => by ext i; exact i.elim0⟩
  exact Fintype.card_unique

lemma card_right_zero (m : ℕ) : Fintype.card (Lmn m 0) = 1 := by
  haveI : Unique (Lmn m 0) :=
    ⟨⟨⟨fun _ => 0, fun _ _ _ => le_refl _⟩⟩,
     fun a => by
      apply Lmn.ext; intro i
      exact Fin.ext (by have := (a.val i).isLt; omega)⟩
  exact Fintype.card_unique

theorem card_eq_choose (m n : ℕ) :
    Fintype.card (Lmn m n) = (m + n).choose m := by
  induction m generalizing n with
  | zero => simp [card_zero]
  | succ m ihm =>
    induction n with
    | zero => simp [card_right_zero]
    | succ n ihn =>
      rw [card_succ_succ, ihm (n + 1), ihn]
      have h1 : m + 1 + (n + 1) = (m + n + 1) + 1 := by omega
      have h2 : m + (n + 1) = m + n + 1 := by omega
      have h3 : (m + 1) + n = m + n + 1 := by omega
      rw [h1, h2, h3]
      exact Nat.choose_succ_succ (m + n + 1) m

end Lmn

end YoungLattice
