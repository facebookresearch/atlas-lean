/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
set_option maxHeartbeats 400000

namespace LoomisWhitney

open Finset BigOperators

/-- Combinatorial fiber inequality used in the proof of Loomis-Whitney for $n = 3$.
Writing $f(b,c)$ for the size of the fiber of the $\beta\gamma$-projection at $(b,c)$ and
$g(b)$ for the size of the fiber of the $\alpha\beta$-projection at $b$,
$\sum_{(b,c) \in \pi_{\beta\gamma}} f(b,c)\, g(b) \le |\pi_{\alpha\beta}| \cdot |\pi_{\alpha\gamma}|$. -/
lemma sum_fiber_mul_le {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset (α × β × γ)) :
    let π_αβ := S.image (fun p => (p.1, p.2.1))
    let π_αγ := S.image (fun p => (p.1, p.2.2))
    let π_βγ := S.image (fun p => (p.2.1, p.2.2))
    let f : β × γ → ℕ := fun p => (S.filter (fun x => (x.2.1, x.2.2) = p)).card
    let g : β → ℕ := fun b => (π_αβ.filter (fun q => q.2 = b)).card
    ∑ p ∈ π_βγ, f p * g p.1 ≤ π_αβ.card * π_αγ.card := by
  intro π_αβ π_αγ π_βγ f g

  let h : γ → ℕ := fun c => (π_αγ.filter (fun q => q.2 = c)).card
  have hf_le_h : ∀ p ∈ π_βγ, f p ≤ h p.2 := by
    intro ⟨b, c⟩ _
    apply Finset.card_le_card_of_injOn (fun (x : α × β × γ) => (x.1, x.2.2))
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_image.mpr ⟨x, hx.1, rfl⟩, (Prod.ext_iff.mp hx.2).2⟩
    · intro x₁ hx₁ x₂ hx₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at hx₁ hx₂
      have h1 := Prod.ext_iff.mp hx₁.2
      have h2 := Prod.ext_iff.mp hx₂.2
      have heq' := Prod.ext_iff.mp heq
      ext1; exact heq'.1
      ext1; exact h1.1.trans h2.1.symm
      exact heq'.2

  have hg_sum : ∑ b ∈ π_βγ.image Prod.fst, g b ≤ π_αβ.card := by
    calc ∑ b ∈ π_βγ.image Prod.fst, g b
        ≤ ∑ b ∈ π_αβ.image Prod.snd, g b := by
          apply Finset.sum_le_sum_of_subset
          intro b hb
          simp only [Finset.mem_image] at hb ⊢
          obtain ⟨⟨b', c'⟩, hbc, rfl⟩ := hb
          obtain ⟨x, hx, hproj⟩ := Finset.mem_image.mp hbc
          exact ⟨(x.1, x.2.1), Finset.mem_image.mpr ⟨x, hx, rfl⟩,
                 (Prod.ext_iff.mp hproj).1⟩
      _ = π_αβ.card := by
          symm
          exact Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
            (fun q _ => Finset.mem_image.mpr ⟨q, ‹_›, rfl⟩)

  have hh_sum : ∑ c ∈ π_βγ.image Prod.snd, h c ≤ π_αγ.card := by
    calc ∑ c ∈ π_βγ.image Prod.snd, h c
        ≤ ∑ c ∈ π_αγ.image Prod.snd, h c := by
          apply Finset.sum_le_sum_of_subset
          intro c hc
          simp only [Finset.mem_image] at hc ⊢
          obtain ⟨⟨b', c'⟩, hbc, rfl⟩ := hc
          obtain ⟨x, hx, hproj⟩ := Finset.mem_image.mp hbc
          exact ⟨(x.1, x.2.2), Finset.mem_image.mpr ⟨x, hx, rfl⟩,
                 (Prod.ext_iff.mp hproj).2⟩
      _ = π_αγ.card := by
          symm
          exact Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
            (fun q _ => Finset.mem_image.mpr ⟨q, ‹_›, rfl⟩)

  calc ∑ p ∈ π_βγ, f p * g p.1
      ≤ ∑ p ∈ π_βγ, h p.2 * g p.1 := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.mul_le_mul_right _ (hf_le_h p hp)
    _ ≤ ∑ p ∈ (π_βγ.image Prod.fst) ×ˢ (π_βγ.image Prod.snd), h p.2 * g p.1 := by
        apply Finset.sum_le_sum_of_subset
        intro ⟨b, c⟩ hbc
        exact Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨(b, c), hbc, rfl⟩,
           Finset.mem_image.mpr ⟨(b, c), hbc, rfl⟩⟩
    _ = (∑ b ∈ π_βγ.image Prod.fst, g b) * (∑ c ∈ π_βγ.image Prod.snd, h c) := by
        rw [Finset.sum_product, Finset.sum_mul_sum]
        simp_rw [mul_comm (g _) (h _)]
    _ ≤ π_αβ.card * π_αγ.card := Nat.mul_le_mul hg_sum hh_sum

/-- Corollary 10.4.6 (discrete Loomis-Whitney for $n = 3$). For any finite set
$S \subseteq \alpha \times \beta \times \gamma$,
$$ |S|^2 \le |\pi_{\alpha\beta}(S)| \cdot |\pi_{\alpha\gamma}(S)| \cdot |\pi_{\beta\gamma}(S)|, $$
where $\pi_{ij}$ denotes the coordinate projection. -/
theorem loomis_whitney {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset (α × β × γ)) :
    S.card ^ 2 ≤
      (S.image (fun p => (p.1, p.2.1))).card *
      (S.image (fun p => (p.1, p.2.2))).card *
      (S.image (fun p => (p.2.1, p.2.2))).card := by
  suffices h : (S.card : ℤ) ^ 2 ≤
      ((S.image (fun p => (p.1, p.2.1))).card : ℤ) *
      ((S.image (fun p => (p.1, p.2.2))).card : ℤ) *
      ((S.image (fun p => (p.2.1, p.2.2))).card : ℤ) by exact_mod_cast h
  set π_αβ := S.image (fun p => (p.1, p.2.1))
  set π_αγ := S.image (fun p => (p.1, p.2.2))
  set π_βγ := S.image (fun p => (p.2.1, p.2.2))
  let proj_βγ : α × β × γ → β × γ := fun x => (x.2.1, x.2.2)
  let f : β × γ → ℕ := fun p => (S.filter (fun x => proj_βγ x = p)).card

  have hS_fiber : S.card = ∑ p ∈ π_βγ, f p :=
    Finset.card_eq_sum_card_fiberwise (f := proj_βγ)
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)

  have hCS : (S.card : ℤ) ^ 2 ≤ (π_βγ.card : ℤ) * ∑ p ∈ π_βγ, (f p : ℤ) ^ 2 := by
    calc (S.card : ℤ) ^ 2 = (∑ p ∈ π_βγ, (f p : ℤ)) ^ 2 := by
            congr 1; exact_mod_cast hS_fiber
      _ ≤ (π_βγ.card : ℤ) * ∑ p ∈ π_βγ, (f p : ℤ) ^ 2 := sq_sum_le_card_mul_sum_sq

  have hSumSq : (∑ p ∈ π_βγ, (f p : ℤ) ^ 2) ≤ (π_αβ.card : ℤ) * (π_αγ.card : ℤ) := by
    suffices h_nat : ∑ p ∈ π_βγ, f p ^ 2 ≤ π_αβ.card * π_αγ.card by exact_mod_cast h_nat
    let g : β → ℕ := fun b => (π_αβ.filter (fun q => q.2 = b)).card
    have hf_le_g : ∀ p ∈ π_βγ, f p ≤ g p.1 := by
      intro ⟨b, c⟩ _
      apply Finset.card_le_card_of_injOn (fun (x : α × β × γ) => (x.1, x.2.1))
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_filter] at hx
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_image.mpr ⟨x, hx.1, rfl⟩, (Prod.ext_iff.mp hx.2).1⟩
      · intro x₁ hx₁ x₂ hx₂ heq
        rw [Finset.mem_coe, Finset.mem_filter] at hx₁ hx₂
        have h1 := Prod.ext_iff.mp hx₁.2
        have h2 := Prod.ext_iff.mp hx₂.2
        have heq' := Prod.ext_iff.mp heq
        ext1; exact heq'.1
        ext1; exact heq'.2
        exact h1.2.trans h2.2.symm
    have h_sq_le : ∀ p ∈ π_βγ, f p ^ 2 ≤ f p * g p.1 := by
      intro p hp
      rw [sq]
      exact Nat.mul_le_mul_left _ (hf_le_g p hp)
    calc ∑ p ∈ π_βγ, f p ^ 2
        ≤ ∑ p ∈ π_βγ, f p * g p.1 := Finset.sum_le_sum h_sq_le
      _ ≤ π_αβ.card * π_αγ.card := sum_fiber_mul_le S

  calc (S.card : ℤ) ^ 2
      ≤ (π_βγ.card : ℤ) * ∑ p ∈ π_βγ, (f p : ℤ) ^ 2 := hCS
    _ ≤ (π_βγ.card : ℤ) * ((π_αβ.card : ℤ) * (π_αγ.card : ℤ)) :=
        mul_le_mul_of_nonneg_left hSumSq (Nat.cast_nonneg _)
    _ = ↑π_αβ.card * ↑π_αγ.card * ↑π_βγ.card := by ring


end LoomisWhitney
