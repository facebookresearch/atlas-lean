/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.FourierFF
import Atlas.ProjectionTheory.code.ParsevalFF
import Atlas.ProjectionTheory.code.OrthogonalityLines

open Finset

namespace LineSumDecomposition

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The line counting function $f(x) = \sum_{L \in \mathcal{L}} \mathbf{1}_L(x)$,
counting how many lines from $\mathcal{L}$ pass through the point $x \in \mathbb{F}_p^2$. -/
noncomputable def lineSumFn (ℒ : Finset (Finset (ZMod p × ZMod p)))
    (x : ZMod p × ZMod p) : ℝ :=
  ∑ L ∈ ℒ, if x ∈ L then 1 else 0

/-- The constant (zero-frequency) part $f_0 = |\mathcal{L}| / p$ in the Fourier
decomposition $f = f_0 + f_h$ of the line counting function. -/
noncomputable def lineSumConst (ℒ : Finset (Finset (ZMod p × ZMod p))) : ℝ :=
  (ℒ.card : ℝ) / (p : ℝ)

/-- The high-frequency part $f_h = f - f_0$ of the line counting function, i.e. the
mean-zero remainder after subtracting the constant component. -/
noncomputable def lineSumHighFreq (ℒ : Finset (Finset (ZMod p × ZMod p)))
    (x : ZMod p × ZMod p) : ℝ :=
  lineSumFn ℒ x - lineSumConst ℒ

/-- The decomposition $f(x) = f_0 + f_h(x)$: the line counting function equals the
sum of its constant and high-frequency parts. -/
lemma decomposition (ℒ : Finset (Finset (ZMod p × ZMod p)))
    (x : ZMod p × ZMod p) :
    lineSumFn ℒ x = lineSumConst ℒ + lineSumHighFreq ℒ x := by
  simp [lineSumHighFreq]

/-- Rewrites $f_h(x) = \sum_{L \in \mathcal{L}} (\mathbf{1}_L(x) - p^{-1})$ as a sum
of individual mean-zero indicator residues. -/
lemma lineSumHighFreq_eq_sum (ℒ : Finset (Finset (ZMod p × ZMod p)))
    (x : ZMod p × ZMod p) :
    lineSumHighFreq ℒ x =
      ∑ L ∈ ℒ, ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) := by
  simp only [lineSumHighFreq, lineSumFn, lineSumConst, div_eq_mul_inv,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

/-- Total mass of the line counting function: $\sum_{x \in \mathbb{F}_p^2} f(x) =
|\mathcal{L}| \cdot p$, since each line has exactly $p$ points. -/
lemma sum_lineSumFn (ℒ : Finset (Finset (ZMod p × ZMod p)))
    (hlines : ∀ L ∈ ℒ, L.card = p) :
    ∑ x : ZMod p × ZMod p, lineSumFn ℒ x = (ℒ.card : ℝ) * (p : ℝ) := by
  unfold lineSumFn
  rw [Finset.sum_comm]
  have h : ∀ L ∈ ℒ, ∑ x : ZMod p × ZMod p, (if x ∈ L then (1 : ℝ) else 0) = (p : ℝ) := by
    intro L hL
    rw [sum_boole]
    rw [show ((Finset.univ.filter (· ∈ L)).card : ℝ) = (p : ℝ) from by
      have hfilt : (Finset.univ.filter (· ∈ L)).card = L.card := by
        congr 1; ext x; simp
      exact_mod_cast (hfilt ▸ hlines L hL)]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

/-- Orthogonality of the constant and high-frequency parts:
$\sum_{x \in \mathbb{F}_p^2} f_0 \cdot f_h(x) = 0$. -/
theorem orthogonal_const_highFreq (ℒ : Finset (Finset (ZMod p × ZMod p)))
    (hlines : ∀ L ∈ ℒ, L.card = p) :
    ∑ x : ZMod p × ZMod p, lineSumConst ℒ * lineSumHighFreq ℒ x = 0 := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out))
  simp only [lineSumHighFreq]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have hsum : ∑ x : ZMod p × ZMod p, lineSumFn ℒ x = (ℒ.card : ℝ) * (p : ℝ) :=
    sum_lineSumFn ℒ hlines
  have hconst : ∑ x : ZMod p × ZMod p, lineSumConst ℒ =
      (ℒ.card : ℝ) * (p : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
        nsmul_eq_mul, lineSumConst]
    field_simp
    push_cast; ring
  rw [hsum, hconst, sub_self, mul_zero]

/-- $L^2$ norm of the constant part: $\sum_x f_0^2 = |\mathcal{L}|^2$. -/
theorem norm_sq_const_eq (ℒ : Finset (Finset (ZMod p × ZMod p))) :
    ∑ _x : ZMod p × ZMod p, (lineSumConst ℒ) ^ 2 = (ℒ.card : ℝ) ^ 2 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
      nsmul_eq_mul, lineSumConst]
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out))
  field_simp
  push_cast; ring

/-- Exact inner product of the mean-zero indicator residues of two lines
$L_1, L_2$ (each of size $p$):
$\sum_x (\mathbf{1}_{L_1}(x) - p^{-1})(\mathbf{1}_{L_2}(x) - p^{-1}) = |L_1 \cap L_2| - 1$. -/
lemma cross_term_eq (L₁ L₂ : Finset (ZMod p × ZMod p))
    (hL₁ : L₁.card = p) (hL₂ : L₂.card = p) :
    ∑ x : ZMod p × ZMod p,
      ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
      ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) =
    ((L₁ ∩ L₂).card : ℝ) - 1 := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out))
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
    push_cast; field_simp
  rw [hS1, hS2, hS3, hS4]; ring

/-- If two distinct lines $L_1, L_2$ in $\mathbb{F}_p^2$ intersect in at most one point
then the cross-term inner product of their mean-zero indicator residues is $\leq 0$. -/
lemma cross_term_nonpos (L₁ L₂ : Finset (ZMod p × ZMod p))
    (hL₁ : L₁.card = p) (hL₂ : L₂.card = p)
    (_hne : L₁ ≠ L₂) (hinter : (L₁ ∩ L₂).card ≤ 1) :
    ∑ x : ZMod p × ZMod p,
      ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
      ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) ≤ 0 := by
  rw [cross_term_eq L₁ L₂ hL₁ hL₂]
  have hcard : ((L₁ ∩ L₂).card : ℝ) ≤ 1 := by exact_mod_cast hinter
  linarith

/-- $L^2$ bound on the high-frequency part: if every pair of distinct lines in
$\mathcal{L}$ meets in at most one point, then
$\sum_{x \in \mathbb{F}_p^2} f_h(x)^2 \leq |\mathcal{L}| \cdot p$. -/
theorem norm_sq_highFreq_le (ℒ : Finset (Finset (ZMod p × ZMod p)))
    (hlines : ∀ L ∈ ℒ, L.card = p)
    (hinter : ∀ L₁ ∈ ℒ, ∀ L₂ ∈ ℒ, L₁ ≠ L₂ → (L₁ ∩ L₂).card ≤ 1) :
    ∑ x : ZMod p × ZMod p, (lineSumHighFreq ℒ x) ^ 2 ≤
    (ℒ.card : ℝ) * (p : ℝ) := by

  have hrw : ∀ x : ZMod p × ZMod p, (lineSumHighFreq ℒ x) ^ 2 =
      (∑ L ∈ ℒ, ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹)) ^ 2 := by
    intro x; rw [lineSumHighFreq_eq_sum]
  simp_rw [hrw]

  have hexpand : ∑ x : ZMod p × ZMod p,
      (∑ L ∈ ℒ, ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹)) ^ 2 =
      ∑ L₁ ∈ ℒ, ∑ L₂ ∈ ℒ, ∑ x : ZMod p × ZMod p,
        ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
        ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) := by
    simp_rw [sq, Finset.sum_mul, Finset.mul_sum, Finset.sum_comm (s := ℒ) (t := univ)]
  rw [hexpand]

  have step1 : ∑ L₁ ∈ ℒ, ∑ L₂ ∈ ℒ, ∑ x : ZMod p × ZMod p,
      ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
      ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) ≤
      ∑ L ∈ ℒ, ∑ x : ZMod p × ZMod p,
        ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
        ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) := by
    apply Finset.sum_le_sum
    intro L₁ hL₁
    have hsplit : ∑ L₂ ∈ ℒ, ∑ x : ZMod p × ZMod p,
        ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
        ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) =
      (∑ x : ZMod p × ZMod p,
        ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
        ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹)) +
      ∑ L₂ ∈ ℒ.erase L₁, ∑ x : ZMod p × ZMod p,
        ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
        ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) := by
      rw [← Finset.add_sum_erase _ _ hL₁]
    rw [hsplit]
    linarith [Finset.sum_nonpos (fun L₂ (hL₂ : L₂ ∈ ℒ.erase L₁) =>
      cross_term_nonpos L₁ L₂ (hlines L₁ hL₁) (hlines L₂ (Finset.mem_of_mem_erase hL₂))
        (Finset.ne_of_mem_erase hL₂).symm
        (hinter L₁ hL₁ L₂ (Finset.mem_of_mem_erase hL₂) (Finset.ne_of_mem_erase hL₂).symm))]

  have step2 : ∑ L ∈ ℒ, ∑ x : ZMod p × ZMod p,
      ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
      ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) ≤ (ℒ.card : ℝ) * (p : ℝ) := by
    have hdiag : ∀ L ∈ ℒ, ∑ x : ZMod p × ZMod p,
        ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
        ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) ≤ (p : ℝ) := by
      intro L hL
      have heq : ∑ x : ZMod p × ZMod p,
          ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
          ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) = (p : ℝ) - 1 := by
        rw [cross_term_eq L L (hlines L hL) (hlines L hL)]
        simp [Finset.inter_self, hlines L hL]
      rw [heq]
      linarith [show (1 : ℝ) ≤ (p : ℝ) from by
        exact_mod_cast Nat.Prime.one_le (Fact.out)]
    calc ∑ L ∈ ℒ, ∑ x : ZMod p × ZMod p,
          ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
          ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹)
        ≤ ∑ L ∈ ℒ, (p : ℝ) := Finset.sum_le_sum hdiag
      _ = (ℒ.card : ℝ) * (p : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- **Main Lemma 2F** (finite field Fourier line decomposition). For a collection
$\mathcal{L}$ of lines in $\mathbb{F}_p^2$ (each of size $p$, pairwise intersecting in
at most one point), the line-counting function $f = \sum_{L \in \mathcal{L}} \mathbf{1}_L$
admits a decomposition $f = f_0 + f_h$ into a constant part $f_0 = |\mathcal{L}|/p$ and
a mean-zero high-frequency part $f_h$ with: (i) orthogonality $\sum_x f_0 f_h = 0$,
(ii) $\sum_x f_0^2 = |\mathcal{L}|^2$, and (iii) the $L^2$ bound
$\sum_x f_h^2 \leq |\mathcal{L}| \cdot p$. -/
theorem main_lemma_2F (ℒ : Finset (Finset (ZMod p × ZMod p)))
    (hlines : ∀ L ∈ ℒ, L.card = p)
    (hinter : ∀ L₁ ∈ ℒ, ∀ L₂ ∈ ℒ, L₁ ≠ L₂ → (L₁ ∩ L₂).card ≤ 1) :
    (∀ x : ZMod p × ZMod p,
      lineSumFn ℒ x = lineSumConst ℒ + lineSumHighFreq ℒ x) ∧
    (∑ x : ZMod p × ZMod p, lineSumConst ℒ * lineSumHighFreq ℒ x = 0) ∧
    (∑ _x : ZMod p × ZMod p, (lineSumConst ℒ) ^ 2 = (ℒ.card : ℝ) ^ 2) ∧
    (∑ x : ZMod p × ZMod p, (lineSumHighFreq ℒ x) ^ 2 ≤ (ℒ.card : ℝ) * (p : ℝ)) :=
  ⟨decomposition ℒ, orthogonal_const_highFreq ℒ hlines, norm_sq_const_eq ℒ,
   norm_sq_highFreq_le ℒ hlines hinter⟩

end LineSumDecomposition
