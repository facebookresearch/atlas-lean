/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Influence
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace BooleanFourier

open Finset

theorem influence_le_one {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    influence f i ≤ 1 := by
  unfold influence
  rw [div_le_one (by positivity : (2 : ℝ) ^ n > 0)]
  have hle : (Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card ≤
      Finset.univ.card :=
    Finset.card_filter_le _ _
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hle
  exact_mod_cast hle

theorem totalInfluence_le_n {n : ℕ} (f : (Fin n → Bool) → Bool) :
    totalInfluence f ≤ (n : ℝ) := by
  show ∑ i : Fin n, influence f i ≤ (n : ℝ)
  calc ∑ i : Fin n, influence f i
      ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => influence_le_one f i)
    _ = (n : ℝ) := by simp [Finset.card_univ, Fintype.card_fin]

def IsIntersectingFamily {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A B : Finset (Fin n), A ∈ F → B ∈ F → (A ∩ B).Nonempty

def IsJunta {n : ℕ} (F : Finset (Finset (Fin n))) (J : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ J ∧
    ∀ A B : Finset (Fin n), A ∩ S = B ∩ S → (A ∈ F ↔ B ∈ F)

noncomputable def muPWeight (n : ℕ) (p : ℝ) (A : Finset (Fin n)) : ℝ :=
  p ^ A.card * (1 - p) ^ (n - A.card)

noncomputable def muPMeasure {n : ℕ} (F : Finset (Finset (Fin n))) (p : ℝ) : ℝ :=
  ∑ A ∈ F, muPWeight n p A

def IsEpsCloseToIntersectingJunta {n : ℕ} (F : Finset (Finset (Fin n)))
    (p : ℝ) (ε : ℝ) (J : ℕ) : Prop :=
  ∃ G : Finset (Finset (Fin n)),
    IsIntersectingFamily G ∧ IsJunta G J ∧
      muPMeasure (F \ G) p ≤ ε


end BooleanFourier
