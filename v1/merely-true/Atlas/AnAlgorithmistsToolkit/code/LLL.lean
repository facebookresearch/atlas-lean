/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

noncomputable section

open InnerProductSpace Finset

namespace LLL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gramSchmidtVec (b : Fin n → E) : Fin n → E :=
  gramSchmidt ℝ b

def gramSchmidtCoeff (b : Fin n → E) (i j : Fin n) : ℝ :=
  @inner ℝ E _ (gramSchmidtVec b j) (b i) / (‖gramSchmidtVec b j‖ ^ 2)

def IsSizeReduced (b : Fin n → E) : Prop :=
  ∀ i j : Fin n, j < i → |gramSchmidtCoeff b i j| ≤ 1 / 2

def SatisfiesLovász (b : Fin n → E) : Prop :=
  ∀ i : Fin n, ∀ hi : (i : ℕ) + 1 < n,
    ‖gramSchmidtVec b ⟨i + 1, hi⟩ +
      gramSchmidtCoeff b ⟨i + 1, hi⟩ i • gramSchmidtVec b i‖ ^ 2 ≥
    3 / 4 * ‖gramSchmidtVec b i‖ ^ 2

structure IsLLLReduced (b : Fin n → E) : Prop where
  size_reduced : IsSizeReduced b
  lovász : SatisfiesLovász b

theorem gramSchmidtVec_norm_sq_half (b : Fin n → E) (hred : IsLLLReduced b)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    ‖gramSchmidtVec b ⟨i + 1, hi⟩‖ ^ 2 ≥ 1 / 2 * ‖gramSchmidtVec b i‖ ^ 2 := by
  have hlov := hred.lovász i hi
  set bstar_i := gramSchmidtVec b i
  set bstar_next := gramSchmidtVec b ⟨i + 1, hi⟩
  set μ := gramSchmidtCoeff b ⟨i + 1, hi⟩ i

  have hne : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ≠ i := by
    intro h; have := congr_arg Fin.val h; simp at this
  have hortho : ⟪bstar_next, bstar_i⟫_ℝ = 0 :=
    gramSchmidt_orthogonal ℝ b hne

  have hexpand : ‖bstar_next + μ • bstar_i‖ ^ 2 =
      ‖bstar_next‖ ^ 2 + μ ^ 2 * ‖bstar_i‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, hortho, mul_zero, mul_zero, add_zero,
        norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

  have hsize : |μ| ≤ 1 / 2 :=
    hred.size_reduced _ _ (Fin.mk_lt_mk.mpr (Nat.lt_succ_of_le le_rfl))
  have hmu_sq : μ ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs μ, abs_nonneg μ]

  rw [hexpand] at hlov

  nlinarith [sq_nonneg (‖bstar_i‖)]

theorem gramSchmidtVec_norm_sq_geometric {n : ℕ} (b : Fin (n + 1) → E)
    (hred : IsLLLReduced b) (j : ℕ) (hj : j < n + 1) :
    ‖gramSchmidtVec b ⟨j, hj⟩‖ ^ 2 ≥
      (1 / 2 : ℝ) ^ j * ‖gramSchmidtVec b 0‖ ^ 2 := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hk : k < n + 1 := by omega
    have h_half := gramSchmidtVec_norm_sq_half b hred ⟨k, hk⟩ (by omega)
    have h_ih := ih hk
    calc ‖gramSchmidtVec b ⟨k + 1, hj⟩‖ ^ 2
        ≥ 1 / 2 * ‖gramSchmidtVec b ⟨k, hk⟩‖ ^ 2 := h_half
      _ ≥ 1 / 2 * ((1 / 2 : ℝ) ^ k * ‖gramSchmidtVec b 0‖ ^ 2) := by gcongr
      _ = (1 / 2 : ℝ) ^ (k + 1) * ‖gramSchmidtVec b 0‖ ^ 2 := by rw [pow_succ]; ring

lemma gramSchmidtVec_zero {n : ℕ} (b : Fin (n + 1) → E) :
    gramSchmidtVec b 0 = b 0 := by
  unfold gramSchmidtVec
  exact gramSchmidt_bot ℝ b







def SatisfiesLovászOriginal (b : Fin n → E) : Prop :=
  ∀ i : Fin n, ∀ hi : (i : ℕ) + 1 < n,
    ‖gramSchmidtVec b i‖ ^ 2 ≤
    4 / 3 * ‖gramSchmidtVec b ⟨i + 1, hi⟩ +
      gramSchmidtCoeff b ⟨i + 1, hi⟩ i • gramSchmidtVec b i‖ ^ 2

structure IsReducedBasis (b : Fin n → E) : Prop where
  size_reduced : IsSizeReduced b
  lovász_original : SatisfiesLovászOriginal b

end LLL

end
