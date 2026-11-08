/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset

namespace ProjectionTheory

/-- Projection map over `ZMod p`: `projMap p θ (x₁, x₂) = x₁ + θ · x₂`, the
direction-`θ` projection in the affine plane `𝔽_p²`. -/
noncomputable def projMap (p : ℕ) (θ : ZMod p) (x : ZMod p × ZMod p) : ZMod p :=
  x.1 + θ * x.2

/-- The image `π_θ(X) ⊆ 𝔽_p` of a finite set `X ⊆ 𝔽_p²` under the projection
`projMap p θ`. -/
noncomputable def projImage (p : ℕ) (θ : ZMod p) (X : Finset (ZMod p × ZMod p)) :
    Finset (ZMod p) :=
  X.image (projMap p θ)

/-- Double-counting inequality on `𝔽_p²`: if for every direction `t ∈ D` the projection
`π_t(X)` has size at most `S`, then `|X| · |D| ≤ S · (|D| + |X|)`. This is the key
estimate underlying the contagious-structure double-counting lemma. -/
lemma double_counting_ineq (p : ℕ) [hp : Fact (Nat.Prime p)]
    (X : Finset (ZMod p × ZMod p)) (D : Finset (ZMod p))
    (hX : X.Nonempty) (S : ℕ) (hS : ∀ t ∈ D, (projImage p t X).card ≤ S) :
    X.card * D.card ≤ S * (D.card + X.card) := by
  classical

  have hCS : ∀ t, X.card ^ 2 ≤ (projImage p t X).card *
      ((X ×ˢ X).filter (fun pair => projMap p t pair.1 = projMap p t pair.2)).card := by
    intro t
    set img := projImage p t X; set f := projMap p t
    have h1 : X.card = ∑ y ∈ img, (X.filter (fun x => f x = y)).card :=
      card_eq_sum_card_image f X
    have h2 := @sq_sum_le_card_mul_sum_sq _ ℕ _ _ _ _ (s := img)
      (f := fun y => (X.filter (fun x => f x = y)).card)
    have h3 : ∑ y ∈ img, (X.filter (fun x => f x = y)).card ^ 2 =
      ∑ x ∈ X, (X.filter (fun z => f z = f x)).card := by
      rw [Finset.sum_comp (fun y => (X.filter (fun x => f x = y)).card) f]
      congr 1; ext y; rw [sq]; simp [smul_eq_mul]
    have h4 : ∑ x ∈ X, (X.filter (fun z => f z = f x)).card =
      ((X ×ˢ X).filter (fun p => f p.1 = f p.2)).card := by
      rw [card_filter]; simp_rw [Finset.sum_product_right, ← card_filter]
    nlinarith [h1, h2, h3, h4]


  have hUB : ∑ t ∈ D, ((X ×ˢ X).filter
      (fun pair => projMap p t pair.1 = projMap p t pair.2)).card
      ≤ X.card * D.card + X.card ^ 2 := by
    simp_rw [card_filter, Finset.sum_product]
    conv_lhs => rw [Finset.sum_comm (s := D) (t := X)]
    simp_rw [Finset.sum_comm (s := D), ← card_filter]
    calc ∑ x₁ ∈ X, ∑ x₂ ∈ X,
          (D.filter (fun t => projMap p t x₁ = projMap p t x₂)).card
        ≤ ∑ x₁ ∈ X, ∑ x₂ ∈ X, (if x₁ = x₂ then D.card else 1) := by
          apply Finset.sum_le_sum; intro x₁ _
          apply Finset.sum_le_sum; intro x₂ _
          split_ifs with heq
          · subst heq; exact Finset.card_filter_le _ _
          ·
            calc (D.filter (fun t => projMap p t x₁ = projMap p t x₂)).card
                ≤ (Finset.univ.filter
                    (fun t => projMap p t x₁ = projMap p t x₂)).card :=
                  Finset.card_le_card
                    (Finset.filter_subset_filter _ (Finset.subset_univ _))
              _ ≤ 1 := by
                  unfold projMap; apply Finset.card_le_one.mpr
                  intro θ₁ hθ₁ θ₂ hθ₂
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ₁ hθ₂
                  have hsub : (θ₁ - θ₂) * (x₁.2 - x₂.2) = 0 := by
                    linear_combination hθ₁ - hθ₂
                  rcases mul_eq_zero.mp hsub with hh | hh
                  · exact sub_eq_zero.mp hh
                  · exfalso; apply heq
                    exact Prod.ext
                      (add_right_cancel (hθ₁.trans (by rw [sub_eq_zero.mp hh])))
                      (sub_eq_zero.mp hh)
      _ = X.card * D.card + X.card * (X.card - 1) := by
          have inner : ∀ x₁ ∈ X, ∑ x₂ ∈ X, (if x₁ = x₂ then D.card else 1) =
              D.card + (X.card - 1) := by
            intro x₁ hx₁
            rw [← Finset.add_sum_erase X _ hx₁]; simp only [if_true]; congr 1
            have h2 : ∀ x₂ ∈ X.erase x₁, (if x₁ = x₂ then D.card else 1) = 1 :=
              fun x₂ hx₂ => if_neg (fun h => (Finset.ne_of_mem_erase hx₂) h.symm)
            rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_one,
                Finset.card_erase_of_mem hx₁]
          rw [Finset.sum_congr rfl inner, Finset.sum_const, smul_eq_mul]; ring
      _ ≤ X.card * D.card + X.card ^ 2 := by nlinarith [Nat.sub_le X.card 1]

  have hXpos : 0 < X.card := Finset.card_pos.mpr hX
  have hComb : D.card * X.card ^ 2 ≤ S * (X.card * D.card + X.card ^ 2) := by
    calc D.card * X.card ^ 2
        = ∑ t ∈ D, X.card ^ 2 := by simp [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ t ∈ D, (S * ((X ×ˢ X).filter
          (fun pair => projMap p t pair.1 = projMap p t pair.2)).card) :=
          Finset.sum_le_sum
            (fun t ht => le_trans (hCS t) (Nat.mul_le_mul_right _ (hS t ht)))
      _ = S * ∑ t ∈ D, _ := by rw [← Finset.mul_sum]
      _ ≤ S * (X.card * D.card + X.card ^ 2) := Nat.mul_le_mul_left _ hUB
  exact Nat.le_of_mul_le_mul_left
    (by nlinarith : X.card * (X.card * D.card) ≤ X.card * (S * (D.card + X.card))) hXpos

/-- **Lemma (Double Counting, lower bound).** For any subset `X ⊆ 𝔽_p²` and any nonempty
set of directions `D ⊆ 𝔽_p`, there exists `t ∈ D` such that
`|π_t(X)| ≥ (1/2) · min(|X|, |D|)`. That is, `max_{t ∈ D} |π_t(X)| ≳ min(|X|, |D|)`. -/
theorem double_counting_lower_bound :
    ∃ C : ℚ, C > 0 ∧ ∀ (p : ℕ) (_ : Nat.Prime p)
    (X : Finset (ZMod p × ZMod p)) (D : Finset (ZMod p)),
    D.Nonempty →
    ∃ t ∈ D, C * min (X.card : ℚ) (D.card : ℚ) ≤ ((projImage p t X).card : ℚ) := by
  refine ⟨1/2, by norm_num, ?_⟩
  intro p hp X D hD
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  classical
  obtain ⟨t₀, ht₀D, ht₀max⟩ :=
    Finset.exists_max_image D (fun t => (projImage p t X).card) hD
  refine ⟨t₀, ht₀D, ?_⟩
  set S := (projImage p t₀ X).card
  by_cases hX : X.Nonempty
  ·
    have h_main : X.card * D.card ≤ S * (D.card + X.card) :=
      double_counting_ineq p X D hX S ht₀max

    have h_min : min X.card D.card ≤ 2 * S := by
      obtain hab | hab := Nat.le_or_le X.card D.card
      · simp only [Nat.min_eq_left hab]
        by_cases hDz : D.card = 0; · omega
        have : X.card * D.card ≤ 2 * S * D.card := by nlinarith
        exact Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero hDz)
      · simp only [Nat.min_eq_right hab]
        by_cases hXz : X.card = 0; · omega
        have : D.card * X.card ≤ 2 * S * X.card := by nlinarith
        exact Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero hXz)

    have hcast : min (X.card : ℚ) (D.card : ℚ) = ((min X.card D.card : ℕ) : ℚ) :=
      (Nat.cast_min X.card D.card).symm
    rw [hcast]
    have : (min X.card D.card : ℚ) ≤ 2 * (S : ℚ) := by exact_mod_cast h_min
    linarith
  ·
    have hXe : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    subst hXe; simp

end ProjectionTheory
