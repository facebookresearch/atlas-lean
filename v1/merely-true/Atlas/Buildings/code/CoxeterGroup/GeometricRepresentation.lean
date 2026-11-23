/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.Basic

open Finset BigOperators

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The bilinear form $B_M$ on $\mathbb{R}^B$ is additive in its left argument. -/
theorem bilinForm_add_left (M : CoxeterMatrix B) (v₁ v₂ w : B → ℝ) :
    bilinForm M (v₁ + v₂) w = bilinForm M v₁ w + bilinForm M v₂ w := by
  simp only [bilinForm, Pi.add_apply, add_mul]
  simp_rw [Finset.sum_add_distrib]

/-- The bilinear form $B_M$ is $\mathbb{R}$-linear in its left argument. -/
theorem bilinForm_smul_left (M : CoxeterMatrix B) (c : ℝ) (v w : B → ℝ) :
    bilinForm M (c • v) w = c * bilinForm M v w := by
  simp only [bilinForm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t _
  ring

/-- Additivity: $\sigma_s(v_1 + v_2) = \sigma_s v_1 + \sigma_s v_2$. -/
theorem sigma_add (M : CoxeterMatrix B) (s : B) (v₁ v₂ : B → ℝ) :
    sigma M s (v₁ + v₂) = sigma M s v₁ + sigma M s v₂ := by
  ext t
  simp only [sigma, Pi.add_apply, bilinForm_add_left]
  ring

/-- Homogeneity: $\sigma_s(c \cdot v) = c \cdot \sigma_s v$ for $c \in \mathbb{R}$. -/
theorem sigma_smul (M : CoxeterMatrix B) (s : B) (c : ℝ) (v : B → ℝ) :
    sigma M s (c • v) = c • sigma M s v := by
  ext t
  simp only [sigma, Pi.smul_apply, smul_eq_mul, bilinForm_smul_left]
  ring

/-- The geometric reflection $\sigma_s : \mathbb{R}^B \to \mathbb{R}^B$ associated to
$s \in S$, packaged as an $\mathbb{R}$-linear map. -/
noncomputable def sigmaLinearMap (M : CoxeterMatrix B) (s : B) : (B → ℝ) →ₗ[ℝ] (B → ℝ) where
  toFun := sigma M s
  map_add' := sigma_add M s
  map_smul' := sigma_smul M s

/-- Sign flip on the simple root: $\langle \sigma_s v, \alpha_s \rangle = -\langle v, \alpha_s\rangle$. -/
theorem bilinForm_sigma_e (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    bilinForm M (sigma M s v) (e s) = -(bilinForm M v (e s)) := by

  have sigma_eq : sigma M s v = v + (-2 * bilinForm M v (e s)) • e s := by
    ext t; simp only [sigma, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [sigma_eq, bilinForm_add_left, bilinForm_smul_left, bilinForm_e_e, formVal_diag]
  ring

/-- Involution: $\sigma_s \circ \sigma_s = \mathrm{id}$ on $\mathbb{R}^B$. -/
theorem sigma_involution (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    sigma M s (sigma M s v) = v := by
  ext t
  simp only [sigma]
  rw [bilinForm_sigma_e]
  ring

/-- $\sigma_s$ as a linear automorphism of $\mathbb{R}^B$, built from the involution
property. -/
noncomputable def sigmaLinearEquiv (M : CoxeterMatrix B) (s : B) : (B → ℝ) ≃ₗ[ℝ] (B → ℝ) :=
  LinearEquiv.ofInvolutive (sigmaLinearMap M s) (sigma_involution M s)

/-- Unfolding lemma: `sigmaLinearEquiv` acts as `sigma`. -/
@[simp]
theorem sigmaLinearEquiv_apply (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    sigmaLinearEquiv M s v = sigma M s v := rfl


/-- Additivity of $B_M$ in the right argument. -/
theorem bilinForm_add_right (M : CoxeterMatrix B) (v w₁ w₂ : B → ℝ) :
    bilinForm M v (w₁ + w₂) = bilinForm M v w₁ + bilinForm M v w₂ := by
  simp only [bilinForm, Pi.add_apply, mul_add]
  simp_rw [Finset.sum_add_distrib]

/-- $\mathbb{R}$-linearity of $B_M$ in the right argument. -/
theorem bilinForm_smul_right (M : CoxeterMatrix B) (v : B → ℝ) (c : ℝ) (w : B → ℝ) :
    bilinForm M v (c • w) = c * bilinForm M v w := by
  simp only [bilinForm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t _
  ring

/-- Symmetry: $B_M(v, w) = B_M(w, v)$. -/
theorem bilinForm_symm (M : CoxeterMatrix B) (v w : B → ℝ) :
    bilinForm M v w = bilinForm M w v := by
  simp only [bilinForm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro t _
  rw [formVal_symm]
  ring

/-- Each geometric reflection preserves the bilinear form:
$B_M(\sigma_s v, \sigma_s w) = B_M(v, w)$. -/
theorem sigma_preserves_form (M : CoxeterMatrix B) (s : B) (v w : B → ℝ) :
    bilinForm M (sigma M s v) (sigma M s w) = bilinForm M v w := by


  have hv := bilinForm_sigma_e M s v
  have hw := bilinForm_sigma_e M s w


  have sigma_as_sum : ∀ u : B → ℝ,
      sigma M s u = u + (-2 * bilinForm M u (e s)) • e s := by
    intro u; ext t
    simp only [sigma, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [sigma_as_sum v, sigma_as_sum w]
  rw [bilinForm_add_left, bilinForm_add_right, bilinForm_add_right]
  rw [bilinForm_smul_left, bilinForm_smul_right]
  rw [bilinForm_smul_left, bilinForm_smul_right]
  rw [bilinForm_e_e, formVal_diag, bilinForm_symm M (e s) w]
  ring


/-- Action of a word $s_1 \cdots s_k$ on $\mathbb{R}^B$ by the composition of geometric
reflections $\sigma_{s_1} \circ \cdots \circ \sigma_{s_k}$. -/
noncomputable def wordSigma (M : CoxeterMatrix B) : List B → (B → ℝ) → (B → ℝ)
  | [], v => v
  | s :: rest, v => sigma M s (wordSigma M rest v)

/-- The empty word acts as the identity. -/
@[simp]
theorem wordSigma_nil (M : CoxeterMatrix B) (v : B → ℝ) :
    wordSigma M [] v = v := rfl

/-- A length-one word acts via a single reflection. -/
@[simp]
theorem wordSigma_singleton (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    wordSigma M [s] v = sigma M s v := rfl

/-- Cons unfolding: $(s :: w) \cdot v = \sigma_s (w \cdot v)$. -/
@[simp]
theorem wordSigma_cons (M : CoxeterMatrix B) (s : B) (rest : List B) (v : B → ℝ) :
    wordSigma M (s :: rest) v = sigma M s (wordSigma M rest v) := rfl

/-- Concatenation respects composition: $(w_1 \!+\!\!+\, w_2) \cdot v = w_1 \cdot (w_2 \cdot v)$. -/
theorem wordSigma_append (M : CoxeterMatrix B) (w₁ w₂ : List B) (v : B → ℝ) :
    wordSigma M (w₁ ++ w₂) v = wordSigma M w₁ (wordSigma M w₂ v) := by
  induction w₁ with
  | nil => simp
  | cons s rest ih => simp [ih]

/-- Additivity of the word action on vectors. -/
theorem wordSigma_add (M : CoxeterMatrix B) (word : List B) (v₁ v₂ : B → ℝ) :
    wordSigma M word (v₁ + v₂) = wordSigma M word v₁ + wordSigma M word v₂ := by
  induction word with
  | nil => simp [wordSigma]
  | cons s rest ih =>
    simp only [wordSigma]
    rw [ih, sigma_add]

/-- Homogeneity of the word action with respect to scalar multiplication. -/
theorem wordSigma_smul (M : CoxeterMatrix B) (word : List B) (c : ℝ) (v : B → ℝ) :
    wordSigma M word (c • v) = c • wordSigma M word v := by
  induction word with
  | nil => simp [wordSigma]
  | cons s rest ih =>
    simp only [wordSigma]
    rw [ih, sigma_smul]

/-- Every word acts by isometries of $B_M$:
$B_M(\sigma_w v, \sigma_w w') = B_M(v, w')$. -/
theorem wordSigma_preserves_form (M : CoxeterMatrix B) (word : List B) (v w : B → ℝ) :
    bilinForm M (wordSigma M word v) (wordSigma M word w) = bilinForm M v w := by
  induction word with
  | nil => simp
  | cons s rest ih => simp [sigma_preserves_form, ih]


/-- Action on a different basis vector: $\sigma_s(\alpha_t) = \alpha_t - 2\,B_M(\alpha_t,\alpha_s)\,\alpha_s$. -/
theorem sigma_e_other (M : CoxeterMatrix B) (s t : B) :
    sigma M s (e t) = fun u => e t u - 2 * formVal M t s * e s u := by
  ext u
  simp only [sigma, bilinForm_e_e]

end CoxeterGroup
