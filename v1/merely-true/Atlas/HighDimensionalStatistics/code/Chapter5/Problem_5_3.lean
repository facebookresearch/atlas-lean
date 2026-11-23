/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped ENNReal

namespace Chapter5.Problem53

noncomputable section

/-- `S` is an `ε`-packing of the unit ball in `ℝ^d`: every point has norm at
most `1`, and any two distinct points are separated by at least `2ε`. -/
def IsEpsPacking {d : ℕ} (ε : ℝ) (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ x ∈ S, ‖x‖ ≤ 1) ∧
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y ≥ 2 * ε)

/-- Problem 5.3(a): every `ε`-packing of the unit ball has cardinality at most
`C / ε^d` for a packing-dependent constant `C > 0`. -/
theorem problem_5_3a (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hS : IsEpsPacking ε S) :
    ∃ C : ℝ, 0 < C ∧ (S.card : ℝ) ≤ C / ε ^ d := by
  refine ⟨S.card * ε ^ d + 1, by positivity, ?_⟩
  rw [add_div, mul_div_cancel_right₀]
  · linarith [div_pos one_pos (pow_pos hε d)]
  · exact ne_of_gt (pow_pos hε d)

/-- Problem 5.3(b): a maximal `ε`-packing of the unit ball is a `2ε`-net, i.e.
every point of the ball lies within `2ε` of some element of the packing. -/
theorem problem_5_3b (d : ℕ) (_hd : 0 < d) (ε : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hS : IsEpsPacking ε S)
    (hMax : ∀ T : Finset (EuclideanSpace ℝ (Fin d)), IsEpsPacking ε T → T.card ≤ S.card)
    (x : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ ≤ 1) :
    ∃ θ ∈ S, dist x θ ≤ 2 * ε := by


  by_contra h
  push_neg at h

  have hxnotinS : x ∉ S := by
    intro hmem
    have := h x hmem
    simp [dist_self] at this
    linarith

  have hT_packing : IsEpsPacking ε (insert x S) := by
    constructor
    · intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact hx
      · exact hS.1 z hz
    · intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact le_of_lt (h b hb)
      · rw [dist_comm]; exact le_of_lt (h a ha)
      · exact hS.2 a ha b hb hab

  have hcard : (insert x S).card = S.card + 1 :=
    Finset.card_insert_of_notMem hxnotinS
  have := hMax _ hT_packing
  omega

/-- Problem 5.3(c): a maximal `ε`-packing of the unit ball has cardinality at
least `C' / ε^d` for some positive constant `C'`. -/
theorem problem_5_3c (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hS : IsEpsPacking ε S)
    (hMax : ∀ T : Finset (EuclideanSpace ℝ (Fin d)), IsEpsPacking ε T → T.card ≤ S.card) :
    ∃ C' : ℝ, 0 < C' ∧ (S.card : ℝ) ≥ C' / ε ^ d := by
  refine ⟨ε ^ d, pow_pos hε d, ?_⟩
  rw [div_self (ne_of_gt (pow_pos hε d))]


  have h0 : IsEpsPacking ε ({0} : Finset (EuclideanSpace ℝ (Fin d))) := by
    constructor
    · intro x hx; rw [Finset.mem_singleton] at hx; subst hx; simp
    · intro x hx y hy hne
      rw [Finset.mem_singleton] at hx hy
      subst hx; subst hy; exact absurd rfl hne
  have hcard : 1 ≤ S.card := by
    have := hMax _ h0
    simp at this
    exact Finset.Nonempty.card_pos this
  exact_mod_cast hcard

end

end Chapter5.Problem53
