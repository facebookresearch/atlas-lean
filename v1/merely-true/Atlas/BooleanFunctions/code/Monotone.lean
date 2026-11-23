/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic
import Atlas.BooleanFunctions.code.FourierExpansion
import Atlas.BooleanFunctions.code.Influence

namespace BooleanFourier

def IsMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  Monotone f

lemma Bool.false_true_of_le_ne {a b : Bool} (hle : a ≤ b) (hne : a ≠ b) :
    a = false ∧ b = true := by
  cases a <;> cases b <;> simp_all [Bool.le_iff_imp]

lemma chi_singleton {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    chi {i} x = boolToReal (x i) := by
  simp [chi]

lemma flipCoord_flipCoord {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipCoord (flipCoord x i) i = x := by
  ext j; simp only [flipCoord, Function.update]; split_ifs with h
  · subst h; simp
  · rfl

lemma flipCoord_ne_self' {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipCoord x i ≠ x := by
  intro h; have := congr_fun h i; simp [flipCoord] at this

lemma le_flipCoord_of_false {n : ℕ} (x : Fin n → Bool) (i : Fin n) (hxi : x i = false) :
    x ≤ flipCoord x i := by
  intro j; simp only [flipCoord, Function.update]
  split_ifs with h
  · subst h; rw [hxi]; exact Bool.false_le _
  · exact le_refl _

lemma flipCoord_le_of_true {n : ℕ} (x : Fin n → Bool) (i : Fin n) (hxi : x i = true) :
    flipCoord x i ≤ x := by
  intro j; simp only [flipCoord, Function.update]
  split_ifs with h
  · subst h; rw [hxi]; exact Bool.false_le _
  · exact le_refl _

open Finset in
theorem monotone_fourierCoeff_singleton_eq_influence {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : Monotone f) (i : Fin n) :
    fourierCoeff (fun x => boolToReal (f x)) {i} = influence f i := by
  simp only [fourierCoeff, chi_singleton, influence]

  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  suffices h : (∑ x : Fin n → Bool, boolToReal (f x) * boolToReal (x i) : ℝ) =
      ((Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card : ℝ) by
    rw [one_div, ← h]; ring

  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x => f x ≠ f (flipCoord x i))
    (fun x => boolToReal (f x) * boolToReal (x i))

  have hfilt : ∑ x ∈ Finset.univ.filter (fun x => f x ≠ f (flipCoord x i)),
      boolToReal (f x) * boolToReal (x i) =
      ((Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card : ℝ) := by
    have hterm : ∀ x ∈ Finset.univ.filter (fun x => f x ≠ f (flipCoord x i)),
        boolToReal (f x) * boolToReal (x i) = (1 : ℝ) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      cases hxi : x i
      case false =>
        obtain ⟨hfx, _⟩ := Bool.false_true_of_le_ne (hf (le_flipCoord_of_false x i hxi)) hx
        rw [hfx]; simp [boolToReal]
      case true =>
        obtain ⟨_, hfx⟩ := Bool.false_true_of_le_ne (hf (flipCoord_le_of_true x i hxi)) hx.symm
        rw [hfx]; simp [boolToReal]
    rw [Finset.sum_congr rfl hterm]
    simp [Finset.sum_const, nsmul_eq_mul]

  have hcompl : ∑ x ∈ Finset.univ.filter (fun x => ¬(f x ≠ f (flipCoord x i))),
      boolToReal (f x) * boolToReal (x i) = 0 := by
    apply Finset.sum_involution (fun x _ => flipCoord x i)
    ·
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
      have h1 : f (flipCoord x i) = f x := hx.symm
      have h2 : (flipCoord x i) i = !(x i) := by simp [flipCoord]
      rw [h1, h2]
      have hzero : boolToReal (x i) + boolToReal (!(x i)) = 0 := by
        cases (x i) <;> simp [boolToReal]
      have hcancel : boolToReal (f x) * boolToReal (x i) +
          boolToReal (f x) * boolToReal (!(x i)) = 0 := by
        calc boolToReal (f x) * boolToReal (x i) +
            boolToReal (f x) * boolToReal (!(x i))
          _ = boolToReal (f x) * (boolToReal (x i) + boolToReal (!(x i))) := by ring
          _ = boolToReal (f x) * 0 := by rw [hzero]
          _ = 0 := by ring
      linarith [hcancel]
    ·
      intro x _ _
      exact flipCoord_ne_self' x i
    ·
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx ⊢
      rw [flipCoord_flipCoord]
      exact hx.symm
    ·
      intro x _
      exact flipCoord_flipCoord x i
  linarith [hsplit]

end BooleanFourier
