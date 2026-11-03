/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Influence
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace BooleanFourier

noncomputable def highInfluenceCoords {n : ℕ} (f : (Fin n → Bool) → Bool) (τ : ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => τ ≤ influence f i

lemma influence_nonneg {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    0 ≤ influence f i := by
  unfold influence
  positivity

theorem high_influence_count_le {n : ℕ} (f : (Fin n → Bool) → Bool)
    (τ : ℝ) (hτ : 0 < τ) :
    ((highInfluenceCoords f τ).card : ℝ) ≤ totalInfluence f / τ := by
  set J := highInfluenceCoords f τ
  have hJ : ∀ i ∈ J, τ ≤ influence f i := by
    intro i hi
    simp only [J, highInfluenceCoords, Finset.mem_filter] at hi
    exact hi.2
  have h1 : (J.card : ℝ) * τ ≤ ∑ i ∈ J, influence f i := by
    have hsm : J.card • τ ≤ ∑ i ∈ J, influence f i :=
      Finset.card_nsmul_le_sum J (fun i => influence f i) τ (fun i hi => hJ i hi)
    rwa [nsmul_eq_mul] at hsm
  have h2 : ∑ i ∈ J, influence f i ≤ totalInfluence f := by
    exact Finset.sum_le_univ_sum_of_nonneg (fun i => influence_nonneg f i)
  rw [le_div_iff₀ hτ]
  linarith

end BooleanFourier
