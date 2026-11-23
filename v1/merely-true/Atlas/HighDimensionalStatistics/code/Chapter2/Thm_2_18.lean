/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter2.Lemma_2_17
import Atlas.HighDimensionalStatistics.code.Chapter2.Def_2_12
import Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_15
import Mathlib

open Matrix Finset BigOperators Rigollet MeasureTheory

/-- The squared L² norm equals the self dot product: `‖v‖² = ⟨v, v⟩`. -/
lemma sqL2norm_eq_dotProduct {n : ℕ} (v : Fin n → ℝ) :
    sqL2norm v = dotProduct v v := by
  simp only [sqL2norm, dotProduct, sq]

/-- Cauchy–Schwarz applied to `f` and the constant `1` on a finite set `S`:
`(∑_{j∈S} |f j|)² ≤ |S| · ∑_{j∈S} f j²`. -/
lemma cauchy_schwarz_subset {d : ℕ} (S : Finset (Fin d)) (f : Fin d → ℝ) :
    (∑ j ∈ S, |f j|) ^ 2 ≤ (S.card : ℝ) * ∑ j ∈ S, f j ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun j => |f j|)
  simp only [one_mul, one_pow, sq_abs] at h
  have hcard : (∑ _j ∈ S, (1:ℝ)) = (S.card : ℝ) := by simp
  rw [hcard] at h; linarith

/-- Basic Lasso inequality (Eq. 2.18 in the book): under `|Xᵀε|_∞ ≤ nτ` and a support
hypothesis, the MSE is bounded in terms of the on-support component of `θ̂ - θ*`:
`(1/n) ‖X(θ̂ - θ*)‖² ≤ 4 τ ∑_{j∈S} |θ̂_j - θ*_j|`. -/
lemma eq_2_18_lasso_basic_inequality
    {n d : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ) (eps : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ)
    (θhat : Fin d → ℝ)
    (hLasso : IsLassoEstimatorL2 X (X.mulVec θstar + eps) τ θhat)
    (hXeps : ∀ j : Fin d, |∑ i, X i j * eps i| ≤ ↑n * τ)
    (S : Finset (Fin d))
    (hS : ∀ j, j ∉ S → θstar j = 0) :
    (1 / (n : ℝ)) * sqL2norm (X.mulVec (θhat - θstar)) ≤
      4 * τ * ∑ j ∈ S, |θhat j - θstar j| := by
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn

  have h1 := hLasso.2 θstar

  have hres : (X.mulVec θstar + eps) - X.mulVec θhat = eps - X.mulVec (θhat - θstar) := by
    simp [Matrix.mulVec_sub]; ext i; simp [Pi.sub_apply, Pi.add_apply]; ring
  have hres_star : (X.mulVec θstar + eps) - X.mulVec θstar = eps := by
    ext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [hres, hres_star] at h1
  set v := θhat - θstar with hv_def
  set δ := X.mulVec v with hδ_def

  have hexpand : sqL2norm (eps - δ) = sqL2norm eps - 2 * ∑ i, eps i * δ i + sqL2norm δ := by
    simp only [sqL2norm, Pi.sub_apply]
    simp_rw [fun i : Fin n => show (eps i - δ i) ^ 2 =
      eps i ^ 2 - 2 * (eps i * δ i) + δ i ^ 2 from by ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexpand] at h1

  set B := ∑ i, eps i * δ i
  set C := sqL2norm δ
  have h2 : C ≤ 2 * B + ↑n * (2 * τ * l1norm θstar - 2 * τ * l1norm θhat) := by
    have key : 1 / ↑n * C ≤ 1 / ↑n * (2 * B) + (2 * τ * l1norm θstar - 2 * τ * l1norm θhat) := by
      linarith [show 1 / (↑n : ℝ) * (sqL2norm eps - 2 * B + C) =
        1 / ↑n * sqL2norm eps - 1 / ↑n * (2 * B) + 1 / ↑n * C from by ring]
    calc C = ↑n * (1 / ↑n * C) := by field_simp
      _ ≤ ↑n * (1 / ↑n * (2 * B) + (2 * τ * l1norm θstar - 2 * τ * l1norm θhat)) := by
          apply mul_le_mul_of_nonneg_left key (le_of_lt hn')
      _ = 2 * B + ↑n * (2 * τ * l1norm θstar - 2 * τ * l1norm θhat) := by field_simp

  have hdot : B = ∑ j, (∑ i, X i j * eps i) * v j := by
    simp only [B, Matrix.mulVec, dotProduct, hδ_def]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext j; rw [Finset.sum_mul]; congr 1; ext i; ring
  have hHolder : B ≤ ↑n * τ * l1norm v := by
    rw [hdot]
    calc ∑ j, (∑ i, X i j * eps i) * v j
        ≤ ∑ j, |(∑ i, X i j * eps i) * v j| :=
          Finset.sum_le_sum (fun j _ => le_abs_self _)
      _ = ∑ j, |∑ i, X i j * eps i| * |v j| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, (↑n * τ) * |v j| := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_right (hXeps j) (abs_nonneg _)
      _ = ↑n * τ * l1norm v := by rw [← Finset.mul_sum]; rfl

  have hl1_diff : l1norm θstar - l1norm θhat ≤
      ∑ j ∈ S, |v j| - ∑ j ∈ univ \ S, |v j| := by
    simp only [l1norm]
    have hfull : ∀ (f : Fin d → ℝ), ∑ j, |f j| =
        ∑ j ∈ S, |f j| + ∑ j ∈ univ \ S, |f j| := by
      intro f
      have := Finset.sum_add_sum_compl S (fun j => |f j|)
      simp only [Finset.compl_eq_univ_sdiff] at this; linarith
    rw [hfull θstar, hfull θhat]
    have hSc_star : ∑ j ∈ univ \ S, |θstar j| = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
      simp [hS j hj]
    have hSc_hat : ∑ j ∈ univ \ S, |θhat j| = ∑ j ∈ univ \ S, |v j| := by
      apply Finset.sum_congr rfl; intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
      simp only [v, Pi.sub_apply, hS j hj, sub_zero]
    rw [hSc_star, hSc_hat]
    have hS_bound : ∑ j ∈ S, |θstar j| - ∑ j ∈ S, |θhat j| ≤ ∑ j ∈ S, |v j| := by
      have : ∀ j, |θstar j| - |θhat j| ≤ |v j| := by
        intro j
        calc |θstar j| - |θhat j| ≤ |θstar j - θhat j| := abs_sub_abs_le_abs_sub _ _
          _ = |(-(θhat j - θstar j))| := by ring_nf
          _ = |v j| := by rw [abs_neg]; rfl
      calc ∑ j ∈ S, |θstar j| - ∑ j ∈ S, |θhat j|
          = ∑ j ∈ S, (|θstar j| - |θhat j|) := by rw [Finset.sum_sub_distrib]
        _ ≤ ∑ j ∈ S, |v j| := Finset.sum_le_sum (fun j _ => this j)
    linarith

  have hl1_decomp : l1norm v = ∑ j ∈ S, |v j| + ∑ j ∈ univ \ S, |v j| := by
    simp only [l1norm]
    have := Finset.sum_add_sum_compl S (fun j => |v j|)
    simp only [Finset.compl_eq_univ_sdiff] at this; linarith

  have hfinal : C ≤ 4 * ↑n * τ * ∑ j ∈ S, |v j| := by
    calc C ≤ 2 * B + ↑n * (2 * τ * l1norm θstar - 2 * τ * l1norm θhat) := h2
      _ = 2 * B + ↑n * (2 * τ * (l1norm θstar - l1norm θhat)) := by ring
      _ ≤ 2 * (↑n * τ * l1norm v) +
          ↑n * (2 * τ * (∑ j ∈ S, |v j| - ∑ j ∈ univ \ S, |v j|)) := by
          have hB : 2 * B ≤ 2 * (↑n * τ * l1norm v) := by linarith
          have hD : ↑n * (2 * τ * (l1norm θstar - l1norm θhat)) ≤
              ↑n * (2 * τ * (∑ j ∈ S, |v j| - ∑ j ∈ univ \ S, |v j|)) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hn')
            apply mul_le_mul_of_nonneg_left hl1_diff; linarith
          linarith
      _ = 2 * ↑n * τ * (∑ j ∈ S, |v j| + ∑ j ∈ univ \ S, |v j|) +
          2 * ↑n * τ * (∑ j ∈ S, |v j| - ∑ j ∈ univ \ S, |v j|) := by
          rw [hl1_decomp]; ring
      _ = 4 * ↑n * τ * ∑ j ∈ S, |v j| := by ring

  have hv_eq : ∀ j, |v j| = |θhat j - θstar j| := by
    intro j; simp [v, Pi.sub_apply]
  simp_rw [hv_eq] at hfinal
  calc 1 / (↑n : ℝ) * sqL2norm (X.mulVec v) =
      1 / ↑n * C := by rfl
    _ ≤ 1 / ↑n * (4 * ↑n * τ * ∑ j ∈ S, |θhat j - θstar j|) := by
        apply mul_le_mul_of_nonneg_left hfinal; positivity
    _ = 4 * τ * ∑ j ∈ S, |θhat j - θstar j| := by field_simp

/-- Cone condition for the Lasso error: under `|Xᵀε|_∞ ≤ nτ/2` and the support assumption
on `θ*`, the off-support error is at most three times the on-support error:
`∑_{j∉S} |θ̂_j - θ*_j| ≤ 3 ∑_{j∈S} |θ̂_j - θ*_j|`. -/
lemma cone_condition_from_lasso
    {n d : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ) (eps : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ)
    (θhat : Fin d → ℝ)
    (hLasso : IsLassoEstimatorL2 X (X.mulVec θstar + eps) τ θhat)
    (hXeps : ∀ j : Fin d, |∑ i, X i j * eps i| ≤ ↑n * τ / 2)
    (S : Finset (Fin d))
    (hS : ∀ j, j ∉ S → θstar j = 0) :
    ∑ j ∈ univ \ S, |(θhat - θstar) j| ≤
      3 * ∑ j ∈ S, |(θhat - θstar) j| := by
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h1 := hLasso.2 θstar
  have hres : (X.mulVec θstar + eps) - X.mulVec θhat = eps - X.mulVec (θhat - θstar) := by
    simp [Matrix.mulVec_sub]; ext i; simp [Pi.sub_apply, Pi.add_apply]; ring
  have hres_star : (X.mulVec θstar + eps) - X.mulVec θstar = eps := by
    ext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [hres, hres_star] at h1
  set v := θhat - θstar with hv_def
  set δ := X.mulVec v with hδ_def
  have hexpand : sqL2norm (eps - δ) = sqL2norm eps - 2 * ∑ i, eps i * δ i + sqL2norm δ := by
    simp only [sqL2norm, Pi.sub_apply]
    simp_rw [fun i : Fin n => show (eps i - δ i) ^ 2 =
      eps i ^ 2 - 2 * (eps i * δ i) + δ i ^ 2 from by ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexpand] at h1
  set B := ∑ i, eps i * δ i


  have h_ineq : 2 * τ * (l1norm θhat - l1norm θstar) ≤ 2 / ↑n * B := by
    have hC_nn : 0 ≤ sqL2norm δ := sqL2norm_nonneg _
    have key : 1 / ↑n * sqL2norm δ + 2 * τ * l1norm θhat ≤
        1 / ↑n * (2 * B) + 2 * τ * l1norm θstar := by
      linarith [show 1 / (↑n : ℝ) * (sqL2norm eps - 2 * B + sqL2norm δ) =
        1 / ↑n * sqL2norm eps - 1 / ↑n * (2 * B) + 1 / ↑n * sqL2norm δ from by ring]
    have hpos : 0 ≤ 1 / ↑n * sqL2norm δ := mul_nonneg (by positivity) hC_nn
    have heq : 1 / ↑n * (2 * B) = 2 / ↑n * B := by ring
    linarith

  have hdot : B = ∑ j, (∑ i, X i j * eps i) * v j := by
    simp only [B, Matrix.mulVec, dotProduct, hδ_def]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext j; rw [Finset.sum_mul]; congr 1; ext i; ring
  have hB_bound : 2 / ↑n * B ≤ τ * l1norm v := by
    have hB_abs : B ≤ (↑n * τ / 2) * l1norm v := by
      rw [hdot]
      calc ∑ j, (∑ i, X i j * eps i) * v j
          ≤ ∑ j, |(∑ i, X i j * eps i) * v j| :=
            Finset.sum_le_sum (fun j _ => le_abs_self _)
        _ = ∑ j, |∑ i, X i j * eps i| * |v j| := by
            congr 1; ext j; exact abs_mul _ _
        _ ≤ ∑ j, (↑n * τ / 2) * |v j| := by
            apply Finset.sum_le_sum; intro j _
            exact mul_le_mul_of_nonneg_right (hXeps j) (abs_nonneg _)
        _ = (↑n * τ / 2) * l1norm v := by rw [← Finset.mul_sum]; rfl
    calc 2 / ↑n * B ≤ 2 / ↑n * ((↑n * τ / 2) * l1norm v) := by
          apply mul_le_mul_of_nonneg_left hB_abs; positivity
      _ = τ * l1norm v := by field_simp

  have h_l1_half : l1norm θhat - l1norm θstar ≤ (1 / 2) * l1norm v := by
    have h2τ : 0 < 2 * τ := by linarith
    have : 2 * τ * (l1norm θhat - l1norm θstar) ≤ τ * l1norm v := by linarith
    nlinarith

  set sumS := ∑ j ∈ S, |v j|
  set sumSc := ∑ j ∈ univ \ S, |v j|
  have h_l1_decomp : l1norm v = sumS + sumSc := by
    simp only [l1norm]
    have := Finset.sum_add_sum_compl S (fun j => |v j|)
    simp only [Finset.compl_eq_univ_sdiff] at this; linarith

  have h_l1_lb : sumSc - sumS ≤ l1norm θhat - l1norm θstar := by
    simp only [l1norm]
    have hfull : ∀ (f : Fin d → ℝ), ∑ j, |f j| =
        ∑ j ∈ S, |f j| + ∑ j ∈ univ \ S, |f j| := by
      intro f
      have := Finset.sum_add_sum_compl S (fun j => |f j|)
      simp only [Finset.compl_eq_univ_sdiff] at this; linarith
    rw [hfull θhat, hfull θstar]
    have hSc_star : ∑ j ∈ univ \ S, |θstar j| = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
      simp [hS j hj]
    rw [hSc_star]
    have hSc_hat : ∑ j ∈ univ \ S, |θhat j| = sumSc := by
      apply Finset.sum_congr rfl; intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
      simp only [v, Pi.sub_apply, hS j hj, sub_zero]
    rw [hSc_hat]
    have hS_bound : ∑ j ∈ S, |θhat j| - ∑ j ∈ S, |θstar j| ≥ -sumS := by
      have hrev : ∀ j, |θhat j| - |θstar j| ≥ -|v j| := by
        intro j
        have := abs_sub_abs_le_abs_sub (θstar j) (θhat j)
        have hv : |θhat j - θstar j| = |v j| := by simp [v, Pi.sub_apply]
        linarith [abs_sub_comm (θstar j) (θhat j)]
      calc ∑ j ∈ S, |θhat j| - ∑ j ∈ S, |θstar j|
          = ∑ j ∈ S, (|θhat j| - |θstar j|) := by rw [Finset.sum_sub_distrib]
        _ ≥ ∑ j ∈ S, (-|v j|) := Finset.sum_le_sum (fun j _ => hrev j)
        _ = -sumS := by rw [Finset.sum_neg_distrib]
    linarith


  have h_combine : sumSc ≤ 3 * sumS := by
    have : sumSc - sumS ≤ (1 / 2) * (sumS + sumSc) := by
      calc sumSc - sumS ≤ l1norm θhat - l1norm θstar := h_l1_lb
        _ ≤ (1 / 2) * l1norm v := h_l1_half
        _ = (1 / 2) * (sumS + sumSc) := by rw [h_l1_decomp]
    nlinarith

  exact h_combine

/-- If `A ≥ 0`, `c ≥ 0`, and `A² ≤ c · A`, then `A ≤ c`. -/
lemma le_of_sq_le_mul_self {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (h : A ^ 2 ≤ c * A) :
    A ≤ c := by
  rcases eq_or_lt_of_le hA with rfl | hApos
  · exact hc
  · have hA' : A * A ≤ c * A := by rwa [sq] at h
    exact le_of_mul_le_mul_right hA' hApos

/-- Deterministic fast-rate MSE bound (Theorem 2.18, MSE part): under `INC(k)`, a
`k`-sparse `θ*`, and `|Xᵀε|_∞ ≤ nτ/2`, the Lasso satisfies
`(1/n) ‖X(θ̂ - θ*)‖² ≤ 576 k τ²`. -/
theorem thm_2_18_lasso_fast_rate_mse
    {n d : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (θstar : Fin d → ℝ) (eps : Fin n → ℝ)
    (hY : Y = X.mulVec θstar + eps)
    (k : ℕ) (hk : 0 < k)
    (hINC : AssumptionINC X k)
    (hstar_sparse : (univ.filter (fun j => θstar j ≠ 0)).card ≤ k)
    (τ : ℝ) (hτ : 0 < τ)
    (θhat : Fin d → ℝ)
    (hLasso : IsLassoEstimatorL2 X Y τ θhat)
    (hXeps : ∀ j : Fin d, |∑ i, X i j * eps i| ≤ ↑n * τ / 2) :
    (1 / (n : ℝ)) * Rigollet.sqL2norm (X.mulVec (θhat - θstar)) ≤
      576 * (k : ℝ) * τ ^ 2 := by

  set v := θhat - θstar with hv_def
  set S := univ.filter (fun j => θstar j ≠ 0) with hS_def
  set A := (1 / (n : ℝ)) * Rigollet.sqL2norm (X.mulVec v) with hA_def
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hA_nn : 0 ≤ A := by apply mul_nonneg; positivity; exact sqL2norm_nonneg _
  have hS_mem : ∀ j, j ∉ S → θstar j = 0 := by
    intro j hj; simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    push Not at hj; exact hj
  rw [hY] at hLasso

  have hXeps_weak : ∀ j : Fin d, |∑ i, X i j * eps i| ≤ ↑n * τ := by
    intro j; calc |∑ i, X i j * eps i| ≤ ↑n * τ / 2 := hXeps j
      _ ≤ ↑n * τ := by nlinarith

  have h_eq218 : A ≤ 4 * τ * ∑ j ∈ S, |v j| :=
    eq_2_18_lasso_basic_inequality hn X θstar eps τ hτ θhat hLasso hXeps_weak S hS_mem

  have h_cone : ∑ j ∈ univ \ S, |v j| ≤ 3 * ∑ j ∈ S, |v j| :=
    cone_condition_from_lasso hn X θstar eps τ hτ θhat hLasso hXeps S hS_mem

  have h_l217 : ∑ j ∈ S, v j ^ 2 ≤ 2 * A := by
    rw [hA_def, sqL2norm_eq_dotProduct]
    exact lemma_2_17_norm_equivalence hn X k hk hINC S hstar_sparse v h_cone

  have h_cs : (∑ j ∈ S, |v j|) ^ 2 ≤ (S.card : ℝ) * ∑ j ∈ S, v j ^ 2 :=
    cauchy_schwarz_subset S v

  have h_sumS_sq_le : (∑ j ∈ S, |v j|) ^ 2 ≤ 2 * ↑k * A := by
    calc (∑ j ∈ S, |v j|) ^ 2
        ≤ (S.card : ℝ) * ∑ j ∈ S, v j ^ 2 := h_cs
      _ ≤ ↑k * (2 * A) := by
          apply mul_le_mul (Nat.cast_le.mpr hstar_sparse) h_l217
            (Finset.sum_nonneg fun j _ => sq_nonneg _) (by positivity)
      _ = 2 * ↑k * A := by ring

  have h_sumS_nn : 0 ≤ ∑ j ∈ S, |v j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg _)


  have h_A_le : A ≤ 32 * ↑k * τ ^ 2 := by
    set s := ∑ j ∈ S, |v j| with hs_def
    have h_Asq : A ^ 2 ≤ 32 * ↑k * τ ^ 2 * A := by
      calc A ^ 2 ≤ (4 * τ * s) ^ 2 := by
              apply sq_le_sq' <;> linarith
        _ = 16 * τ ^ 2 * s ^ 2 := by ring
        _ ≤ 16 * τ ^ 2 * (2 * ↑k * A) := by nlinarith [sq_nonneg τ]
        _ = 32 * ↑k * τ ^ 2 * A := by ring
    exact le_of_sq_le_mul_self hA_nn (by positivity) h_Asq

  calc A ≤ 32 * ↑k * τ ^ 2 := h_A_le
    _ ≤ 576 * ↑k * τ ^ 2 := by nlinarith [sq_nonneg τ]

/-- Deterministic fast-rate ℓ¹ bound (Theorem 2.18, ℓ¹ part): under the same hypotheses
as the MSE bound, `‖θ̂ - θ*‖₁ ≤ 32 k τ`. -/
theorem thm_2_18_lasso_fast_rate_l1
    {n d : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (θstar : Fin d → ℝ) (eps : Fin n → ℝ)
    (hY : Y = X.mulVec θstar + eps)
    (k : ℕ) (hk : 0 < k)
    (hINC : AssumptionINC X k)
    (hstar_sparse : (univ.filter (fun j => θstar j ≠ 0)).card ≤ k)
    (τ : ℝ) (hτ : 0 < τ)
    (θhat : Fin d → ℝ)
    (hLasso : IsLassoEstimatorL2 X Y τ θhat)
    (hXeps : ∀ j : Fin d, |∑ i, X i j * eps i| ≤ ↑n * τ / 2) :
    Rigollet.l1norm (θhat - θstar) ≤ 32 * (k : ℝ) * τ := by
  set v := θhat - θstar with hv_def
  set S := univ.filter (fun j => θstar j ≠ 0) with hS_def
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hS_mem : ∀ j, j ∉ S → θstar j = 0 := by
    intro j hj; simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    push Not at hj; exact hj

  rw [hY] at hLasso
  have hXeps_weak : ∀ j : Fin d, |∑ i, X i j * eps i| ≤ ↑n * τ := by
    intro j; calc |∑ i, X i j * eps i| ≤ ↑n * τ / 2 := hXeps j
      _ ≤ ↑n * τ := by nlinarith


  have h_cone : ∑ j ∈ univ \ S, |v j| ≤ 3 * ∑ j ∈ S, |v j| :=
    cone_condition_from_lasso hn X θstar eps τ hτ θhat hLasso hXeps S hS_mem
  have hl1_cone : l1norm v ≤ 4 * ∑ j ∈ S, |v j| := by
    simp only [l1norm]
    have hdecomp : ∑ j : Fin d, |v j| =
        ∑ j ∈ S, |v j| + ∑ j ∈ univ \ S, |v j| := by
      have := Finset.sum_add_sum_compl S (fun j => |v j|)
      simp only [Finset.compl_eq_univ_sdiff] at this; linarith
    rw [hdecomp]; linarith

  have h_cs : (∑ j ∈ S, |v j|) ^ 2 ≤ (S.card : ℝ) * ∑ j ∈ S, v j ^ 2 :=
    cauchy_schwarz_subset S v

  set A := (1 / (n : ℝ)) * sqL2norm (X.mulVec v) with hA_def
  have hA_nn : 0 ≤ A := by apply mul_nonneg; positivity; exact sqL2norm_nonneg _
  have h_l217 : ∑ j ∈ S, v j ^ 2 ≤ 2 * A := by
    rw [hA_def, sqL2norm_eq_dotProduct]
    exact lemma_2_17_norm_equivalence hn X k hk hINC S hstar_sparse v h_cone

  have h_eq218 : A ≤ 4 * τ * ∑ j ∈ S, |v j| :=
    eq_2_18_lasso_basic_inequality hn X θstar eps τ hτ θhat hLasso hXeps_weak S hS_mem
  have h_sumS_sq_le : (∑ j ∈ S, |v j|) ^ 2 ≤ 2 * ↑k * A := by
    calc (∑ j ∈ S, |v j|) ^ 2
        ≤ (S.card : ℝ) * ∑ j ∈ S, v j ^ 2 := h_cs
      _ ≤ ↑k * (2 * A) := by
          apply mul_le_mul (Nat.cast_le.mpr hstar_sparse) h_l217
            (Finset.sum_nonneg fun j _ => sq_nonneg _) (by positivity)
      _ = 2 * ↑k * A := by ring
  have h_A_le : A ≤ 32 * ↑k * τ ^ 2 := by
    set s := ∑ j ∈ S, |v j|
    have h_Asq : A ^ 2 ≤ 32 * ↑k * τ ^ 2 * A := by
      calc A ^ 2 ≤ (4 * τ * s) ^ 2 := by apply sq_le_sq' <;> linarith
        _ = 16 * τ ^ 2 * s ^ 2 := by ring
        _ ≤ 16 * τ ^ 2 * (2 * ↑k * A) := by nlinarith [sq_nonneg τ]
        _ = 32 * ↑k * τ ^ 2 * A := by ring
    exact le_of_sq_le_mul_self hA_nn (by positivity) h_Asq


  have h_sumS_le : ∑ j ∈ S, |v j| ≤ 8 * ↑k * τ := by
    have h_sumS_nn : 0 ≤ ∑ j ∈ S, |v j| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have h8kτ_nn : (0 : ℝ) ≤ 8 * ↑k * τ := by positivity
    have h_sq_bound : (∑ j ∈ S, |v j|) ^ 2 ≤ (8 * ↑k * τ) ^ 2 := by
      calc (∑ j ∈ S, |v j|) ^ 2
          ≤ 2 * ↑k * A := h_sumS_sq_le
        _ ≤ 2 * ↑k * (32 * ↑k * τ ^ 2) := by
            apply mul_le_mul_of_nonneg_left h_A_le; positivity
        _ = (8 * ↑k * τ) ^ 2 := by ring
    by_contra h_neg
    push Not at h_neg

    have : (8 * ↑k * τ) ^ 2 < (∑ j ∈ S, |v j|) ^ 2 :=
      sq_lt_sq' (by linarith) h_neg
    linarith
  calc l1norm v ≤ 4 * ∑ j ∈ S, |v j| := hl1_cone
    _ ≤ 4 * (8 * ↑k * τ) := by linarith
    _ = 32 * ↑k * τ := by ring

/-- Combined deterministic fast-rate bounds (Theorem 2.18, conjunction): under `INC(k)`,
a `k`-sparse `θ*`, and `|Xᵀε|_∞ ≤ nτ/2`, both `MSE(Xθ̂) ≤ 576 k τ²` and
`‖θ̂ - θ*‖₁ ≤ 32 k τ` hold. -/
theorem thm_2_18_lasso_probabilistic
    {n d : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (θstar : Fin d → ℝ) (eps : Fin n → ℝ)
    (hY : Y = X.mulVec θstar + eps)
    (k : ℕ) (hk : 0 < k)
    (hINC : AssumptionINC X k)
    (hstar_sparse : (univ.filter (fun j => θstar j ≠ 0)).card ≤ k)
    (τ : ℝ) (hτ : 0 < τ)
    (θhat : Fin d → ℝ)
    (hLasso : IsLassoEstimatorL2 X Y τ θhat)
    (hXeps : ∀ j : Fin d, |∑ i, X i j * eps i| ≤ ↑n * τ / 2) :
    (1 / (n : ℝ)) * Rigollet.sqL2norm (X.mulVec (θhat - θstar)) ≤
      576 * (k : ℝ) * τ ^ 2
    ∧ Rigollet.l1norm (θhat - θstar) ≤ 32 * (k : ℝ) * τ :=
  ⟨thm_2_18_lasso_fast_rate_mse hn X Y θstar eps hY k hk hINC hstar_sparse τ hτ θhat hLasso hXeps,
   thm_2_18_lasso_fast_rate_l1 hn X Y θstar eps hY k hk hINC hstar_sparse τ hτ θhat hLasso hXeps⟩



