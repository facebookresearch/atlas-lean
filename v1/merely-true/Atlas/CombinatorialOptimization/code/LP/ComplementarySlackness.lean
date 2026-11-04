/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.LP.WeakDuality

open Matrix Finset

theorem complementary_slackness {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hAx : A *ᵥ x ≤ b) (hx : 0 ≤ x)
    (hATy : Aᵀ *ᵥ y ≥ c) (hy : 0 ≤ y) :
    dotProduct c x = dotProduct b y ↔
      (∀ i, (b i - (A *ᵥ x) i) * y i = 0) ∧
      (∀ j, ((Aᵀ *ᵥ y) j - c j) * x j = 0) := by

  have key : dotProduct b y - dotProduct c x =
      ∑ i : Fin m, (b i - (A *ᵥ x) i) * y i +
      ∑ j : Fin n, ((Aᵀ *ᵥ y) j - c j) * x j := by
    have h1 : dotProduct b y - dotProduct c x =
        dotProduct (b - A *ᵥ x) y + dotProduct (Aᵀ *ᵥ y - c) x := by
      simp only [sub_dotProduct]
      have h : dotProduct (A *ᵥ x) y = dotProduct (Aᵀ *ᵥ y) x := by
        rw [dotProduct_comm (A *ᵥ x) y, Matrix.dotProduct_mulVec]
        congr 1
        rw [← Matrix.vecMul_transpose]
        simp [transpose_transpose]
      linarith
    rw [h1]
    simp only [dotProduct, Pi.sub_apply]

  have hpos1 : ∀ i ∈ (univ : Finset (Fin m)), 0 ≤ (b i - (A *ᵥ x) i) * y i :=
    fun i _ => mul_nonneg (sub_nonneg.mpr (hAx i)) (hy i)
  have hpos2 : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ ((Aᵀ *ᵥ y) j - c j) * x j :=
    fun j _ => mul_nonneg (sub_nonneg.mpr (hATy j)) (hx j)
  have hs1_nonneg : (0 : ℝ) ≤ ∑ i : Fin m, (b i - (A *ᵥ x) i) * y i :=
    Finset.sum_nonneg hpos1
  have hs2_nonneg : (0 : ℝ) ≤ ∑ j : Fin n, ((Aᵀ *ᵥ y) j - c j) * x j :=
    Finset.sum_nonneg hpos2
  constructor
  ·
    intro heq
    have hzero : ∑ i : Fin m, (b i - (A *ᵥ x) i) * y i +
        ∑ j : Fin n, ((Aᵀ *ᵥ y) j - c j) * x j = 0 := by linarith
    have h_s1_zero : ∑ i : Fin m, (b i - (A *ᵥ x) i) * y i = 0 := by linarith
    have h_s2_zero : ∑ j : Fin n, ((Aᵀ *ᵥ y) j - c j) * x j = 0 := by linarith
    exact ⟨fun i => (Finset.sum_eq_zero_iff_of_nonneg hpos1).mp h_s1_zero i (mem_univ i),
           fun j => (Finset.sum_eq_zero_iff_of_nonneg hpos2).mp h_s2_zero j (mem_univ j)⟩
  ·
    intro ⟨h1, h2⟩
    have hsum1 : ∑ i : Fin m, (b i - (A *ᵥ x) i) * y i = 0 :=
      Finset.sum_eq_zero (fun i _ => h1 i)
    have hsum2 : ∑ j : Fin n, ((Aᵀ *ᵥ y) j - c j) * x j = 0 :=
      Finset.sum_eq_zero (fun j _ => h2 j)
    linarith
