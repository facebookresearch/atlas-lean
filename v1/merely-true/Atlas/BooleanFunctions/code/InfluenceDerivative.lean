/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Influence
import Atlas.BooleanFunctions.code.Derivatives
import Mathlib.Tactic

namespace BooleanFourier

def boolToSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def boolDiscreteDerivative {n : ℕ} (g : (Fin (n + 1) → Bool) → ℝ)
    (i : Fin (n + 1)) : (Fin n → Bool) → ℝ :=
  fun y => (1 / 2 : ℝ) * (g (Fin.insertNth i true y) - g (Fin.insertNth i false y))

@[simp]
theorem boolDiscreteDerivative_apply {n : ℕ} (g : (Fin (n + 1) → Bool) → ℝ)
    (i : Fin (n + 1)) (y : Fin n → Bool) :
    boolDiscreteDerivative g i y =
      (1 / 2 : ℝ) * (g (Fin.insertNth i true y) - g (Fin.insertNth i false y)) :=
  rfl

lemma flipCoord_insertNth {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    flipCoord (Fin.insertNth i b y) i = Fin.insertNth i (!b) y := by
  simp only [flipCoord, Fin.insertNth_apply_same]
  rw [Fin.update_insertNth]

lemma ne_flipCoord_iff_insertNth {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool)
    (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    (f (Fin.insertNth i b y) ≠ f (flipCoord (Fin.insertNth i b y) i)) ↔
    (f (Fin.insertNth i true y) ≠ f (Fin.insertNth i false y)) := by
  rw [flipCoord_insertNth]
  cases b
  · exact ne_comm
  · rfl

lemma influence_filter_card_eq {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) (i : Fin (n + 1)) :
    (Finset.univ.filter fun x : Fin (n + 1) → Bool => f x ≠ f (flipCoord x i)).card =
    2 * (Finset.univ.filter fun y : Fin n → Bool =>
      f (Fin.insertNth i true y) ≠ f (Fin.insertNth i false y)).card := by
  rw [Finset.card_filter, Finset.card_filter]
  have h := Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => Bool) i).symm
    (fun x : Fin (n + 1) → Bool => if f x ≠ f (flipCoord x i) then 1 else 0)
    (fun p : Bool × (Fin n → Bool) =>
      if f (Fin.insertNth i p.1 p.2) ≠ f (flipCoord (Fin.insertNth i p.1 p.2) i) then 1 else 0)
    (by intro p; simp)
  rw [h]
  simp_rw [ne_flipCoord_iff_insertNth f i]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ← two_mul]

theorem influence_eq_l2_norm_sq_discreteDerivative {n : ℕ}
    (f : (Fin (n + 1) → Bool) → Bool) (i : Fin (n + 1)) :
    influence f i =
      (∑ y : Fin n → Bool,
        (boolDiscreteDerivative (fun x => boolToSign (f x)) i y) ^ 2) /
        (2 ^ n : ℝ) := by
  have deriv_sq : ∀ y : Fin n → Bool,
      (boolDiscreteDerivative (fun x => boolToSign (f x)) i y) ^ 2 =
      if f (Fin.insertNth i true y) = f (Fin.insertNth i false y) then (0 : ℝ) else 1 := by
    intro y
    simp only [boolDiscreteDerivative, boolToSign]
    cases f (Fin.insertNth i true y) <;> cases f (Fin.insertNth i false y) <;> simp <;> norm_num
  simp_rw [deriv_sq]
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, zero_add, nsmul_eq_mul, mul_one]
  simp only [influence]
  rw [influence_filter_card_eq f i]
  push_cast
  rw [pow_succ]
  ring

end BooleanFourier
