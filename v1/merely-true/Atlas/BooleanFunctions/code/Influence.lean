/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field

namespace BooleanFourier

def flipCoord {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

noncomputable def influence {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : ℝ :=
  ((Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card : ℝ) / (2 ^ n : ℝ)

noncomputable def totalInfluence {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ i : Fin n, influence f i

def numPivotal {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin n => f x ≠ f (flipCoord x i)).card

theorem totalInfluence_eq_expected_pivotal {n : ℕ} (f : (Fin n → Bool) → Bool) :
    totalInfluence f =
      (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, (numPivotal f x : ℝ) := by
  unfold totalInfluence influence numPivotal

  rw [← Finset.sum_div, one_div, inv_mul_eq_div]
  congr 1

  simp only [Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]

end BooleanFourier
