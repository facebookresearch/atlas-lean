/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset

namespace OrthogonalityLines

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The high-frequency part of the characteristic function $\mathbf{1}_L$ of a (would-be)
line $L \subseteq \mathbb{F}_p^2$: $L_h(x) = \mathbf{1}_L(x) - 1/p$. For an actual affine line
of cardinality $p$, this subtracts the average value $|L|/p^2 = 1/p$. -/
noncomputable def lineHighFreq (L : Finset (ZMod p × ZMod p)) (x : ZMod p × ZMod p) : ℝ :=
  (if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹

/-- The affine line $\{(x, y) \in \mathbb{F}_p^2 \mid a x + b y = c\}$. -/
noncomputable def affineLine (a b c : ZMod p) : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun xy => a * xy.1 + b * xy.2 = c)

/-- A finite subset $L \subseteq \mathbb{F}_p^2$ is an *affine line* if there exist
coefficients $(a, b) \ne (0, 0)$ and $c \in \mathbb{F}_p$ with $L = \{a x + b y = c\}$. -/
def IsAffineLine (L : Finset (ZMod p × ZMod p)) : Prop :=
  ∃ a b c : ZMod p, (a, b) ≠ (0, 0) ∧ L = affineLine a b c

/-- An affine line $\{a x + b y = c\}$ in $\mathbb{F}_p^2$ (with $(a, b) \ne 0$) has
exactly $p$ points. -/
lemma affineLine_card (a b c : ZMod p) (hab : (a, b) ≠ (0, 0)) :
    (affineLine a b c).card = p := by
  unfold affineLine
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by intro ha; exact hab (Prod.ext ha hb)
    subst hb; simp only [zero_mul, add_zero]
    have h_eq : Finset.univ.filter (fun xy : ZMod p × ZMod p => a * xy.1 = c) =
      (Finset.univ : Finset (ZMod p)).image (fun y => (a⁻¹ * c, y)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro h
        exact ⟨y, (mul_left_cancel₀ ha (by
          rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]; exact h.symm)), rfl⟩
      · rintro ⟨y', hx, hy⟩
        rw [← hx, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    rw [h_eq, Finset.card_image_of_injective _ (fun y₁ y₂ h => by
      simp only [Prod.mk.injEq] at h; exact h.2), Finset.card_univ, ZMod.card]
  · have h_eq : Finset.univ.filter (fun xy : ZMod p × ZMod p => a * xy.1 + b * xy.2 = c) =
      (Finset.univ : Finset (ZMod p)).image (fun x => (x, b⁻¹ * (c - a * x))) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro h
        refine ⟨x, rfl, ?_⟩
        have key : b * y = c - a * x := by linear_combination h
        calc b⁻¹ * (c - a * x) = b⁻¹ * (b * y) := by rw [key]
          _ = y := inv_mul_cancel_left₀ hb y
      · rintro ⟨x', hx, hy⟩
        rw [← hx, ← hy]
        have : b * (b⁻¹ * (c - a * x')) = c - a * x' := mul_inv_cancel_left₀ hb _
        linear_combination this
    rw [h_eq, Finset.card_image_of_injective _ (fun x₁ x₂ h => by
      simp only [Prod.mk.injEq] at h; exact h.1), Finset.card_univ, ZMod.card]

/-- Every affine line in $\mathbb{F}_p^2$ has $|L| = p$. -/
lemma IsAffineLine.card_eq {L : Finset (ZMod p × ZMod p)} (hL : IsAffineLine L) :
    L.card = p := by
  obtain ⟨a, b, c, hab, rfl⟩ := hL
  exact affineLine_card a b c hab

/-- A homogeneous $2 \times 2$ linear system over $\mathbb{F}_p$ with nonzero determinant
$a_1 b_2 - a_2 b_1 \ne 0$ has only the trivial solution $dx = dy = 0$. -/
lemma linear_system_unique (a₁ b₁ a₂ b₂ dx dy : ZMod p)
    (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (heq1 : a₁ * dx + b₁ * dy = 0) (heq2 : a₂ * dx + b₂ * dy = 0) :
    dx = 0 ∧ dy = 0 := by
  have hdx : (a₁ * b₂ - a₂ * b₁) * dx = 0 := by linear_combination b₂ * heq1 - b₁ * heq2
  have hdy : (a₁ * b₂ - a₂ * b₁) * dy = 0 := by linear_combination -(a₂ * heq1 - a₁ * heq2)
  exact ⟨(mul_eq_zero.mp hdx).resolve_left hdet, (mul_eq_zero.mp hdy).resolve_left hdet⟩

/-- If two line equations $(a_1, b_1; c_1)$ and $(a_2, b_2; c_2)$ over $\mathbb{F}_p^2$ have
proportional coefficients (cross ratios all vanish), then they define the same line: every
point satisfies one iff it satisfies the other. -/
lemma affineLine_mem_iff_of_proportional (a₁ b₁ c₁ a₂ b₂ c₂ : ZMod p)
    (hab₁ : (a₁, b₁) ≠ (0, 0)) (hab₂ : (a₂, b₂) ≠ (0, 0))
    (hsub : a₁ * b₂ = a₂ * b₁)
    (hcross_b : c₁ * b₂ = c₂ * b₁)
    (hcross_a : c₁ * a₂ = c₂ * a₁)
    (x' y' : ZMod p) :
    a₁ * x' + b₁ * y' = c₁ ↔ a₂ * x' + b₂ * y' = c₂ := by
  constructor
  · intro h'
    by_cases ha₁ : a₁ = 0
    · have hb₁ : b₁ ≠ 0 := by intro hb₁; exact hab₁ (Prod.ext ha₁ hb₁)
      have ha₂ : a₂ = 0 := by
        have : a₂ * b₁ = 0 := by rw [← hsub, ha₁, zero_mul]
        exact (mul_eq_zero.mp this).resolve_right hb₁
      simp only [ha₁, ha₂, zero_mul, zero_add] at h' ⊢
      exact mul_left_cancel₀ hb₁ (by
        calc b₁ * (b₂ * y') = b₂ * (b₁ * y') := by ring
          _ = b₂ * c₁ := by rw [h']
          _ = c₁ * b₂ := by ring
          _ = c₂ * b₁ := hcross_b
          _ = b₁ * c₂ := by ring)
    · exact mul_left_cancel₀ ha₁ (by
        calc a₁ * (a₂ * x' + b₂ * y')
            = a₂ * (a₁ * x' + b₁ * y') + (a₁ * b₂ - a₂ * b₁) * y' := by ring
          _ = a₂ * c₁ + (a₁ * b₂ - a₂ * b₁) * y' := by rw [h']
          _ = a₂ * c₁ + 0 := by rw [sub_eq_zero.mpr hsub, zero_mul]
          _ = c₁ * a₂ := by ring
          _ = c₂ * a₁ := hcross_a
          _ = a₁ * c₂ := by ring)
  · intro h'
    by_cases ha₂ : a₂ = 0
    · have hb₂ : b₂ ≠ 0 := by intro hb₂; exact hab₂ (Prod.ext ha₂ hb₂)
      have ha₁' : a₁ = 0 := by
        have : a₁ * b₂ = 0 := by rw [hsub, ha₂, zero_mul]
        exact (mul_eq_zero.mp this).resolve_right hb₂
      simp only [ha₂, ha₁', zero_mul, zero_add] at h' ⊢
      exact mul_left_cancel₀ hb₂ (by
        calc b₂ * (b₁ * y') = b₁ * (b₂ * y') := by ring
          _ = b₁ * c₂ := by rw [h']
          _ = c₂ * b₁ := by ring
          _ = c₁ * b₂ := hcross_b.symm
          _ = b₂ * c₁ := by ring)
    · exact mul_left_cancel₀ ha₂ (by
        calc a₂ * (a₁ * x' + b₁ * y')
            = a₁ * (a₂ * x' + b₂ * y') + (a₂ * b₁ - a₁ * b₂) * y' := by ring
          _ = a₁ * c₂ + (a₂ * b₁ - a₁ * b₂) * y' := by rw [h']
          _ = a₁ * c₂ + 0 := by rw [sub_eq_zero.mpr hsub.symm, zero_mul]
          _ = c₂ * a₁ := by ring
          _ = c₁ * a₂ := hcross_a.symm
          _ = a₂ * c₁ := by ring)

/-- Two distinct affine lines in $\mathbb{F}_p^2$ intersect in at most one point. -/
lemma affineLine_inter_card (a₁ b₁ c₁ a₂ b₂ c₂ : ZMod p)
    (hab₁ : (a₁, b₁) ≠ (0, 0)) (hab₂ : (a₂, b₂) ≠ (0, 0))
    (hdist : affineLine a₁ b₁ c₁ ≠ affineLine a₂ b₂ c₂) :
    (affineLine a₁ b₁ c₁ ∩ affineLine a₂ b₂ c₂).card ≤ 1 := by
  unfold affineLine at hdist ⊢
  have hinter_eq : Finset.univ.filter (fun xy : ZMod p × ZMod p => a₁ * xy.1 + b₁ * xy.2 = c₁) ∩
    Finset.univ.filter (fun xy => a₂ * xy.1 + b₂ * xy.2 = c₂) =
    Finset.univ.filter (fun xy => a₁ * xy.1 + b₁ * xy.2 = c₁ ∧ a₂ * xy.1 + b₂ * xy.2 = c₂) := by
    ext x; simp [Finset.mem_filter, Finset.mem_inter]
  rw [hinter_eq, Finset.card_le_one]
  intro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
  obtain ⟨h1a, h1b⟩ := h₁
  obtain ⟨h2a, h2b⟩ := h₂
  have heq1 : a₁ * (x₁ - x₂) + b₁ * (y₁ - y₂) = 0 := by linear_combination h1a - h2a
  have heq2 : a₂ * (x₁ - x₂) + b₂ * (y₁ - y₂) = 0 := by linear_combination h1b - h2b
  by_cases hdet : a₁ * b₂ - a₂ * b₁ ≠ 0
  ·
    obtain ⟨hdx, hdy⟩ := linear_system_unique a₁ b₁ a₂ b₂ _ _ hdet heq1 heq2
    exact Prod.ext (sub_eq_zero.mp hdx) (sub_eq_zero.mp hdy)
  ·
    simp only [not_not] at hdet
    exfalso; apply hdist
    have hsub : a₁ * b₂ = a₂ * b₁ := sub_eq_zero.mp hdet
    have hcross_b : c₁ * b₂ = c₂ * b₁ := by
      calc c₁ * b₂ = (a₁ * x₁ + b₁ * y₁) * b₂ := by rw [h1a]
        _ = a₁ * b₂ * x₁ + b₁ * b₂ * y₁ := by ring
        _ = a₂ * b₁ * x₁ + b₂ * b₁ * y₁ := by rw [hsub, mul_comm b₁ b₂]
        _ = (a₂ * x₁ + b₂ * y₁) * b₁ := by ring
        _ = c₂ * b₁ := by rw [h1b]
    have hcross_a : c₁ * a₂ = c₂ * a₁ := by
      calc c₁ * a₂ = (a₁ * x₁ + b₁ * y₁) * a₂ := by rw [h1a]
        _ = a₁ * a₂ * x₁ + b₁ * a₂ * y₁ := by ring
        _ = a₁ * a₂ * x₁ + a₁ * b₂ * y₁ := by
            congr 1
            calc b₁ * a₂ * y₁ = a₂ * b₁ * y₁ := by ring
              _ = a₁ * b₂ * y₁ := by rw [hsub.symm]
        _ = a₁ * (a₂ * x₁ + b₂ * y₁) := by ring
        _ = a₁ * c₂ := by rw [h1b]
        _ = c₂ * a₁ := by ring
    ext ⟨x', y'⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact affineLine_mem_iff_of_proportional a₁ b₁ c₁ a₂ b₂ c₂ hab₁ hab₂ hsub hcross_b hcross_a x' y'

/-- Two distinct affine lines in $\mathbb{F}_p^2$ meet in at most one point. -/
lemma IsAffineLine.inter_card_le_one {L₁ L₂ : Finset (ZMod p × ZMod p)}
    (hL₁ : IsAffineLine L₁) (hL₂ : IsAffineLine L₂) (hdist : L₁ ≠ L₂) :
    (L₁ ∩ L₂).card ≤ 1 := by
  obtain ⟨a₁, b₁, c₁, hab₁, rfl⟩ := hL₁
  obtain ⟨a₂, b₂, c₂, hab₂, rfl⟩ := hL₂
  exact affineLine_inter_card a₁ b₁ c₁ a₂ b₂ c₂ hab₁ hab₂ hdist

/-- Inner product of the high-frequency parts of two finite sets of size $p$ in
$\mathbb{F}_p^2$:
$\sum_{x \in \mathbb{F}_p^2} L_{1, h}(x) L_{2, h}(x) = |L_1 \cap L_2| - 1$. -/
lemma innerProduct_highFreq_eq (L₁ L₂ : Finset (ZMod p × ZMod p))
    (hL₁ : L₁.card = p) (hL₂ : L₂.card = p) :
    ∑ x : ZMod p × ZMod p, lineHighFreq L₁ x * lineHighFreq L₂ x =
    ((L₁ ∩ L₂).card : ℝ) - 1 := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out))
  unfold lineHighFreq

  have hexpand : ∀ x : ZMod p × ZMod p,
    ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
    ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) =
    (if x ∈ L₁ then (1 : ℝ) else 0) * (if x ∈ L₂ then (1 : ℝ) else 0)
    - (p : ℝ)⁻¹ * (if x ∈ L₁ then (1 : ℝ) else 0)
    - (p : ℝ)⁻¹ * (if x ∈ L₂ then (1 : ℝ) else 0)
    + (p : ℝ)⁻¹ ^ 2 := by intro x; ring
  simp_rw [hexpand]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib]

  have hS1 : ∑ x : ZMod p × ZMod p,
    (if x ∈ L₁ then (1 : ℝ) else 0) * (if x ∈ L₂ then (1 : ℝ) else 0) =
    ((L₁ ∩ L₂).card : ℝ) := by
    have h1 : ∀ x, (if x ∈ L₁ then (1 : ℝ) else 0) * (if x ∈ L₂ then (1 : ℝ) else 0) =
        if (x ∈ L₁ ∧ x ∈ L₂) then 1 else 0 := by intro x; split_ifs <;> simp_all
    simp_rw [h1, show (fun x => if x ∈ L₁ ∧ x ∈ L₂ then (1:ℝ) else 0) =
      fun x => if x ∈ L₁ ∩ L₂ then 1 else 0 from by ext x; simp [mem_inter]]
    rw [sum_boole]
    exact_mod_cast show (univ.filter (· ∈ L₁ ∩ L₂)).card = (L₁ ∩ L₂).card from by
      congr 1; ext x; simp

  have hS2 : ∑ x : ZMod p × ZMod p,
    (p : ℝ)⁻¹ * (if x ∈ L₁ then (1 : ℝ) else 0) = 1 := by
    rw [← mul_sum, sum_boole]
    rw [show ((univ.filter (· ∈ L₁)).card : ℝ) = (p : ℝ) from by
      have : (univ.filter (· ∈ L₁)).card = L₁.card := by congr 1; ext x; simp
      exact_mod_cast (this ▸ hL₁)]
    exact inv_mul_cancel₀ hp

  have hS3 : ∑ x : ZMod p × ZMod p,
    (p : ℝ)⁻¹ * (if x ∈ L₂ then (1 : ℝ) else 0) = 1 := by
    rw [← mul_sum, sum_boole]
    rw [show ((univ.filter (· ∈ L₂)).card : ℝ) = (p : ℝ) from by
      have : (univ.filter (· ∈ L₂)).card = L₂.card := by congr 1; ext x; simp
      exact_mod_cast (this ▸ hL₂)]
    exact inv_mul_cancel₀ hp

  have hS4 : ∑ x : ZMod p × ZMod p, (p : ℝ)⁻¹ ^ 2 = 1 := by
    rw [sum_const, card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul, inv_pow]
    push_cast
    field_simp

  rw [hS1, hS2, hS3, hS4]
  ring

/-- **Lemma 2.4 (Orthogonality of lines).** If $L_1, L_2$ are two distinct affine lines in
$\mathbb{F}_q^2$, then
$\sum_{x \in \mathbb{F}_q^2} L_{1, h}(x) L_{2, h}(x) \le 0$.
This follows from $|L_1 \cap L_2| \le 1$ for distinct lines. -/
theorem orthogonality_lines (L₁ L₂ : Finset (ZMod p × ZMod p))
    (hL₁ : IsAffineLine L₁) (hL₂ : IsAffineLine L₂) (hdist : L₁ ≠ L₂) :
    ∑ x : ZMod p × ZMod p, lineHighFreq L₁ x * lineHighFreq L₂ x ≤ 0 := by
  rw [innerProduct_highFreq_eq L₁ L₂ hL₁.card_eq hL₂.card_eq]
  have hinter := hL₁.inter_card_le_one hL₂ hdist
  have hcard : ((L₁ ∩ L₂).card : ℝ) ≤ 1 := by exact_mod_cast hinter
  linarith

end OrthogonalityLines
