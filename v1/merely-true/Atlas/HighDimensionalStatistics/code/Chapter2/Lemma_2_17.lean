/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter2.Prop_2_16
import Mathlib

set_option maxHeartbeats 4800000

open Finset Matrix BigOperators

noncomputable section

/-- Cauchy-Schwarz consequence: `(∑_{j∈S} |f_j|)² ≤ |S| · ∑_{j∈S} f_j²`. -/
lemma sq_sum_abs_le' {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    (∑ j ∈ S, |f j|) ^ 2 ≤ (S.card : ℝ) * ∑ j ∈ S, f j ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun j => |f j|)
  simp only [one_mul, one_pow, sq_abs] at h
  have hcard : (∑ _j ∈ S, (1:ℝ)) = (S.card : ℝ) := by simp
  rw [hcard] at h; linarith

/-- Quadratic-form identity: `(1/n) ‖Xθ‖² = ∑_{j1,j2} θ_{j1} · (XᵀX/n)_{j1 j2} · θ_{j2}`. -/
lemma quad_form_identity' {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (θ : Fin d → ℝ)
    (hn : (0:ℝ) < n) :
    (1 / (n : ℝ)) * ∑ i : Fin n, (∑ j : Fin d, X i j * θ j) ^ 2 =
    ∑ j1 : Fin d, ∑ j2 : Fin d,
      θ j1 * ((X.transpose * X) j1 j2 / (n : ℝ)) * θ j2 := by
  have hnn : (n : ℝ) ≠ 0 := ne_of_gt hn
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  rw [one_div, inv_mul_eq_div]
  have hrw : ∀ j1 j2 : Fin d,
      θ j1 * ((∑ x, X x j1 * X x j2) / ↑n) * θ j2 =
      (θ j1 * (∑ x, X x j1 * X x j2) * θ j2) / ↑n := fun j1 j2 => by ring
  simp_rw [hrw, ← Finset.sum_div]
  congr 1
  conv_lhs =>
    arg 2; ext i; rw [sq]
    rw [show (∑ j, X i j * θ j) * (∑ j, X i j * θ j) =
      ∑ j1 : Fin d, ∑ j2 : Fin d, (X i j1 * θ j1) * (X i j2 * θ j2) from
      Finset.sum_mul_sum Finset.univ Finset.univ _ _]
  have hrw2 : ∀ j1 j2 : Fin d,
      θ j1 * (∑ x, X x j1 * X x j2) * θ j2 =
      ∑ i : Fin n, (X i j1 * θ j1) * (X i j2 * θ j2) := fun j1 j2 => by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _; ring
  simp_rw [hrw2]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  apply Finset.sum_congr rfl; intro j1 _
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]

/-- Positive semidefiniteness of `XᵀX/n` restricted to any index subset `T`. -/
lemma psd_restricted' {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (θ : Fin d → ℝ)
    (hn : (0:ℝ) < n) (T : Finset (Fin d)) :
    0 ≤ ∑ j1 ∈ T, ∑ j2 ∈ T,
      θ j1 * ((X.transpose * X) j1 j2 / (n : ℝ)) * θ j2 := by
  have hnn : (n : ℝ) ≠ 0 := ne_of_gt hn
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  have hrw : ∀ j1 j2 : Fin d,
      θ j1 * ((∑ x : Fin n, X x j1 * X x j2) / (n : ℝ)) * θ j2 =
      (θ j1 * (∑ x : Fin n, X x j1 * X x j2) * θ j2) / (n : ℝ) := fun j1 j2 => by ring
  simp_rw [hrw, ← Finset.sum_div]
  apply div_nonneg _ (le_of_lt hn)
  have hrw2 : ∀ j1 j2 : Fin d,
      θ j1 * (∑ x : Fin n, X x j1 * X x j2) * θ j2 =
      ∑ i : Fin n, θ j1 * X i j1 * (X i j2 * θ j2) := fun j1 j2 => by
    simp_rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
  simp_rw [hrw2]
  rw [Finset.sum_comm (s := T)]
  simp_rw [Finset.sum_comm (s := T) (t := Finset.univ)]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  apply Finset.sum_nonneg; intro i _
  have : (∑ j ∈ T, X i j * θ j) = (∑ j ∈ T, θ j * X i j) := by
    apply Finset.sum_congr rfl; intro j _; ring
  rw [this]
  exact mul_self_nonneg _

/-- Factorisation of a separable double sum: `∑_{j1,j2} f(j1) · c · g(j2) =
c · (∑ f) · (∑ g)`. -/
lemma sum_sum_const_mul_eq' {ι₁ ι₂ : Type*} (S₁ : Finset ι₁) (S₂ : Finset ι₂)
    (f : ι₁ → ℝ) (g : ι₂ → ℝ) (c : ℝ) :
    ∑ j1 ∈ S₁, ∑ j2 ∈ S₂, f j1 * c * g j2 =
    c * (∑ j1 ∈ S₁, f j1) * (∑ j2 ∈ S₂, g j2) := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := S₁)]
  apply Finset.sum_congr rfl; intro j2 _
  apply Finset.sum_congr rfl; intro j1 _; ring

/-- Core inequality of Lemma 2.17: under an incoherence-type bound on the off-diagonal
entries of `XᵀX/n` and a cone condition on `θ`, the restricted sum of squares
`(1/2) · ∑_{j∈S} θ_j²` is bounded by the empirical Gram quadratic form. -/
theorem lemma_2_17_core {n d : ℕ} {k : ℝ}
    (X : Matrix (Fin n) (Fin d) ℝ) (θ : Fin d → ℝ)
    (S : Finset (Fin d))
    (hn : (0 : ℝ) < (n : ℝ))
    (hk : (0 : ℝ) < k)
    (hSk : (S.card : ℝ) ≤ k)
    (hINC : ∀ i j : Fin d,
      |((X.transpose * X) i j : ℝ) / (n : ℝ) - if i = j then 1 else 0| ≤ 1 / (14 * k))
    (hcone : ∑ j ∈ Finset.univ \ S, |θ j| ≤ 3 * ∑ j ∈ S, |θ j|) :
    (1 / 2) * ∑ j ∈ S, θ j ^ 2 ≤
      (1 / (n : ℝ)) * ∑ i : Fin n, (∑ j : Fin d, X i j * θ j) ^ 2 := by
  set G : Fin d → Fin d → ℝ := fun j1 j2 => (X.transpose * X) j1 j2 / (n : ℝ) with hG_def
  rw [quad_form_identity' X θ hn]
  have hpart : ∀ f : Fin d → Fin d → ℝ,
      ∑ j1 : Fin d, ∑ j2 : Fin d, f j1 j2 =
      ∑ j1 ∈ S, ∑ j2 ∈ S, f j1 j2 +
      ∑ j1 ∈ S, ∑ j2 ∈ Finset.univ \ S, f j1 j2 +
      ∑ j1 ∈ Finset.univ \ S, ∑ j2 ∈ S, f j1 j2 +
      ∑ j1 ∈ Finset.univ \ S, ∑ j2 ∈ Finset.univ \ S, f j1 j2 := by
    intro f
    have h1 : ∀ j1, ∑ j2 : Fin d, f j1 j2 =
        ∑ j2 ∈ S, f j1 j2 + ∑ j2 ∈ Finset.univ \ S, f j1 j2 := by
      intro j1
      have := Finset.sum_add_sum_compl S (fun j2 => f j1 j2)
      simp only [Finset.compl_eq_univ_sdiff] at this; linarith
    simp_rw [h1, Finset.sum_add_distrib]
    have h2a := Finset.sum_add_sum_compl S (fun j1 => ∑ j2 ∈ S, f j1 j2)
    have h2b := Finset.sum_add_sum_compl S (fun j1 => ∑ j2 ∈ Finset.univ \ S, f j1 j2)
    simp only [Finset.compl_eq_univ_sdiff] at h2a h2b; linarith
  rw [hpart]
  set sumSq := ∑ j ∈ S, θ j ^ 2
  set sumAbs := ∑ j ∈ S, |θ j|
  set sumAbsSc := ∑ j ∈ Finset.univ \ S, |θ j|
  set QSS := ∑ j1 ∈ S, ∑ j2 ∈ S, θ j1 * G j1 j2 * θ j2
  set QSSc := ∑ j1 ∈ S, ∑ j2 ∈ Finset.univ \ S, θ j1 * G j1 j2 * θ j2
  set QScS := ∑ j1 ∈ Finset.univ \ S, ∑ j2 ∈ S, θ j1 * G j1 j2 * θ j2
  set QScSc := ∑ j1 ∈ Finset.univ \ S, ∑ j2 ∈ Finset.univ \ S, θ j1 * G j1 j2 * θ j2
  have hSS_decomp : QSS = sumSq + ∑ j1 ∈ S, ∑ j2 ∈ S,
      θ j1 * (G j1 j2 - if j1 = j2 then 1 else 0) * θ j2 := by
    simp only [QSS, sumSq]
    have hspl : ∀ j1 j2 : Fin d,
        θ j1 * G j1 j2 * θ j2 =
        θ j1 * (if j1 = j2 then 1 else 0) * θ j2 +
        θ j1 * (G j1 j2 - if j1 = j2 then 1 else 0) * θ j2 := by intros; ring
    simp_rw [hspl, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro j hj
    rw [Finset.sum_eq_single j]
    · simp only [ite_true, mul_one, sq]
    · intro b _ hbj; simp only [Ne.symm hbj, ite_false, mul_zero, zero_mul]
    · intro habs; exact absurd hj habs
  set err := ∑ j1 ∈ S, ∑ j2 ∈ S,
      θ j1 * (G j1 j2 - if j1 = j2 then 1 else 0) * θ j2
  have herr : |err| ≤ 1 / (14 * k) * sumAbs ^ 2 := by
    calc |err|
        ≤ ∑ j1 ∈ S, ∑ j2 ∈ S, |θ j1 * (G j1 j2 - if j1 = j2 then 1 else 0) * θ j2| :=
          (abs_sum_le_sum_abs _ S).trans (Finset.sum_le_sum fun j1 _ => abs_sum_le_sum_abs _ S)
      _ = ∑ j1 ∈ S, ∑ j2 ∈ S, |θ j1| * |G j1 j2 - if j1 = j2 then 1 else 0| * |θ j2| := by
          apply Finset.sum_congr rfl; intro j1 _
          apply Finset.sum_congr rfl; intro j2 _
          rw [abs_mul, abs_mul]
      _ ≤ ∑ j1 ∈ S, ∑ j2 ∈ S, |θ j1| * (1 / (14 * k)) * |θ j2| := by
          gcongr with j1 _ j2 _; exact hINC j1 j2
      _ = 1 / (14 * k) * sumAbs ^ 2 := by
          rw [sum_sum_const_mul_eq' S S (fun j => |θ j|) (fun j => |θ j|) (1 / (14 * k))]
          simp only [sumAbs, sq]; ring
  have hSS_lb : QSS ≥ sumSq - 1 / (14 * k) * sumAbs ^ 2 := by
    rw [hSS_decomp]; linarith [neg_abs_le err]
  have hScSc_lb : QScSc ≥ 0 := psd_restricted' X θ hn (Finset.univ \ S)
  have hcross_abs_bound : ∀ (T1 T2 : Finset (Fin d)),
      (∀ j1 ∈ T1, ∀ j2 ∈ T2, j1 ≠ j2) →
      |∑ j1 ∈ T1, ∑ j2 ∈ T2, θ j1 * G j1 j2 * θ j2| ≤
      1 / (14 * k) * (∑ j1 ∈ T1, |θ j1|) * (∑ j2 ∈ T2, |θ j2|) := by
    intro T1 T2 hne
    calc |∑ j1 ∈ T1, ∑ j2 ∈ T2, θ j1 * G j1 j2 * θ j2|
        ≤ ∑ j1 ∈ T1, ∑ j2 ∈ T2, |θ j1 * G j1 j2 * θ j2| :=
          (abs_sum_le_sum_abs _ T1).trans (Finset.sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)
      _ = ∑ j1 ∈ T1, ∑ j2 ∈ T2, |θ j1| * |G j1 j2| * |θ j2| := by
          apply Finset.sum_congr rfl; intro j1 _
          apply Finset.sum_congr rfl; intro j2 _; rw [abs_mul, abs_mul]
      _ ≤ ∑ j1 ∈ T1, ∑ j2 ∈ T2, |θ j1| * (1 / (14 * k)) * |θ j2| := by
          gcongr with j1 hj1 j2 hj2
          have hneij := hne j1 hj1 j2 hj2
          have h := hINC j1 j2
          simp only [hneij, ite_false, sub_zero] at h
          rw [hG_def]; exact h
      _ = 1 / (14 * k) * (∑ j1 ∈ T1, |θ j1|) * (∑ j2 ∈ T2, |θ j2|) :=
          sum_sum_const_mul_eq' T1 T2 (fun j => |θ j|) (fun j => |θ j|) (1 / (14 * k))
  have hSSc : |QSSc| ≤ 1 / (14 * k) * sumAbs * sumAbsSc :=
    hcross_abs_bound S (Finset.univ \ S)
      (fun j1 hj1 j2 hj2 h => (Finset.mem_sdiff.mp hj2).2 (h ▸ hj1))
  have hScS : |QScS| ≤ 1 / (14 * k) * sumAbsSc * sumAbs :=
    hcross_abs_bound (Finset.univ \ S) S
      (fun j1 hj1 j2 hj2 h => (Finset.mem_sdiff.mp hj1).2 (h ▸ hj2))
  have h_abs_nn : 0 ≤ sumAbs := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have h_absSc_nn : 0 ≤ sumAbsSc := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have h_inv_nn : 0 ≤ 1 / (14 * k) := by positivity
  have hcross : QSSc + QScS ≥ -6 / (14 * k) * sumAbs ^ 2 := by
    have hQSSc_lb : QSSc ≥ -(1 / (14 * k) * sumAbs * sumAbsSc) := by linarith [neg_abs_le QSSc]
    have hQScS_lb : QScS ≥ -(1 / (14 * k) * sumAbsSc * sumAbs) := by linarith [neg_abs_le QScS]
    have hsc_bound : sumAbsSc ≤ 3 * sumAbs := hcone
    have hcomm : 1 / (14 * k) * sumAbsSc * sumAbs = 1 / (14 * k) * sumAbs * sumAbsSc := by ring
    rw [hcomm] at hQScS_lb
    have hsum_lb : QSSc + QScS ≥ -(2 * (1 / (14 * k) * sumAbs * sumAbsSc)) := by linarith
    have step2 : sumAbs * sumAbsSc ≤ 3 * sumAbs ^ 2 := by
      calc sumAbs * sumAbsSc ≤ sumAbs * (3 * sumAbs) :=
            mul_le_mul_of_nonneg_left hsc_bound h_abs_nn
        _ = 3 * sumAbs ^ 2 := by ring
    have h2bound : 2 * (1 / (14 * k) * sumAbs * sumAbsSc) ≤
        2 * (1 / (14 * k) * (3 * sumAbs ^ 2)) := by
      nlinarith [mul_le_mul_of_nonneg_left step2 h_inv_nn]
    have hsimp : -6 / (14 * k) * sumAbs ^ 2 = -(2 * (1 / (14 * k) * (3 * sumAbs ^ 2))) := by ring
    linarith
  have hCS : sumAbs ^ 2 ≤ (S.card : ℝ) * sumSq := sq_sum_abs_le' S θ
  have hSq_nn : 0 ≤ sumSq := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hk14 : 0 < 14 * k := by positivity
  have hkey : sumAbs ^ 2 ≤ k * sumSq := by nlinarith
  have h7 : 7 / (14 * k) * sumAbs ^ 2 ≤ 1 / 2 * sumSq := by
    have h7a : 7 / (14 * k) * (k * sumSq) = 1 / 2 * sumSq := by
      rw [show 7 / (14 * k) * (k * sumSq) = 7 * k / (14 * k) * sumSq from by ring]
      congr 1
      rw [mul_div_mul_right _ _ (ne_of_gt hk)]
      norm_num
    have h7step : 7 / (14 * k) * sumAbs ^ 2 ≤ 7 / (14 * k) * (k * sumSq) := by
      apply mul_le_mul_of_nonneg_left hkey; positivity
    linarith
  have h_total : QSS + QSSc + QScS + QScSc ≥
      sumSq - 1 / (14 * k) * sumAbs ^ 2 + (-6 / (14 * k) * sumAbs ^ 2) + 0 := by linarith
  have hcombine : sumSq - 1 / (14 * k) * sumAbs ^ 2 + (-6 / (14 * k) * sumAbs ^ 2) + 0 =
      sumSq - 7 / (14 * k) * sumAbs ^ 2 := by ring
  linarith

/-- **Lemma 2.17** (restricted-eigenvalue / norm-equivalence inequality): under the
incoherence assumption `INC(k)` and the cone condition, the support-restricted
`ℓ_2` norm of `θ` is comparable to `(1/n)‖Xθ‖²`. -/
theorem lemma_2_17_norm_equivalence
    {n d : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin d) ℝ) (k : ℕ) (hk : 0 < k)
    (hINC : AssumptionINC X k)
    (S : Finset (Fin d)) (hS : S.card ≤ k)
    (θ : Fin d → ℝ)
    (hcone : ∑ j ∈ univ \ S, |θ j| ≤ 3 * ∑ j ∈ S, |θ j|) :
    ∑ j ∈ S, θ j ^ 2 ≤
      2 * ((1 / (n : ℝ)) * dotProduct (X.mulVec θ) (X.mulVec θ)) := by
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hSk' : (S.card : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hS

  have hdot : dotProduct (X.mulVec θ) (X.mulVec θ) =
      ∑ i : Fin n, (∑ j : Fin d, X i j * θ j) ^ 2 := by
    simp [dotProduct, mulVec, sq]
  rw [hdot]
  have h := lemma_2_17_core X θ S hn' hk' hSk' hINC hcone
  linarith
