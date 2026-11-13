/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.SelbergExpansion

open Matrix Finset BigOperators

noncomputable section

namespace SelbergExpansion

section L2Mixing

variable {G : Type*} [Fintype G] [DecidableEq G] [Group G]

omit [DecidableEq G] in
/-- If `μ` is a probability distribution on `G` (i.e. `∑ g, μ g = 1`), then the convolution
operator `convOp μ` fixes constant functions: `convOp μ (fun _ => c) = fun _ => c`. -/
lemma convOp_const (μ : G → ℂ) (c : ℂ) (hμ_sum : ∑ g : G, μ g = 1) :
    convOp μ (fun _ => c) = (fun _ => c) := by
  ext g
  simp only [convOp, groupConv]
  have h : (∑ g₁ : G, μ (g₁⁻¹ * g)) = ∑ g₁ : G, μ g₁ := by
    refine Fintype.sum_equiv ((Equiv.mulLeft g⁻¹).trans (Equiv.inv G)) _ _ (fun h => ?_)
    simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.inv_apply]; congr 1; group
  rw [show (∑ g₁ : G, c * μ (g₁⁻¹ * g)) = c * ∑ g₁ : G, μ (g₁⁻¹ * g) from by
    rw [Finset.mul_sum]]
  rw [h, hμ_sum, mul_one]

omit [DecidableEq G] in
/-- The convolution operator `convOp μ` is additive in its second argument:
`convOp μ (f₁ + f₂) = convOp μ f₁ + convOp μ f₂`. -/
lemma convOp_add (μ f₁ f₂ : G → ℂ) :
    convOp μ (f₁ + f₂) = convOp μ f₁ + convOp μ f₂ := by
  ext g
  simp only [convOp, groupConv, Pi.add_apply]
  rw [← Finset.sum_add_distrib]; congr 1; ext g₁; ring

omit [DecidableEq G] in
/-- If `f : G → ℂ` has mean zero (i.e. `∑ g, f g = 0`), then so does `convOp μ f`. -/
lemma convOp_meanZero (μ f : G → ℂ) (hf : IsMeanZero f) :
    IsMeanZero (convOp μ f) := by
  simp only [IsMeanZero, convOp, groupConv] at *
  rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
  have hshift : ∀ g₁ : G, (∑ g : G, μ (g₁⁻¹ * g)) = ∑ g : G, μ g := fun g₁ => by
    exact Fintype.sum_equiv (Equiv.mulLeft g₁⁻¹) _ _ (fun g => rfl)
  conv_lhs => arg 2; ext g₁; rw [hshift g₁]
  rw [← Finset.sum_mul, hf, zero_mul]

omit [DecidableEq G] in
/-- Iterating the convolution operator `convOp μ` preserves the mean-zero property of `f`. -/
lemma iterate_convOp_meanZero (μ : G → ℂ) (f : G → ℂ) (hf : IsMeanZero f) (n : ℕ) :
    IsMeanZero ((convOp μ)^[n] f) := by
  induction n with
  | zero => simpa
  | succ k ih => rw [Function.iterate_succ', Function.comp_apply]; exact convOp_meanZero μ _ ih

/-- For a probability measure `μ`, the $K$-fold convolution `convPow μ K` minus the constant `c`
equals the $K$-fold iterate of `convOp μ` applied to `δ_{1_G} - c`. -/
lemma convPow_sub_const (μ : G → ℂ) (c : ℂ) (hμ_sum : ∑ g : G, μ g = 1) (K : ℕ) :
    (fun g => convPow μ K g - c) =
      (convOp μ)^[K] (fun g => (if g = (1 : G) then 1 else 0) - c) := by
  induction K with
  | zero => simp [convPow]
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, ← ih]
    ext g
    show convPow μ (n + 1) g - c = convOp μ (fun g => convPow μ n g - c) g
    have hsub : (fun g => convPow μ n g - c) = (convPow μ n) + (fun _ => -c) := by
      ext g; simp [sub_eq_add_neg]
    rw [hsub, convOp_add]; simp only [Pi.add_apply]
    have := congr_fun (convOp_const μ (-c) hμ_sum) g
    rw [this]; show groupConv (convPow μ n) μ g - c = convOp μ (convPow μ n) g + -c
    simp [sub_eq_add_neg, convOp]

/-- The set of operator-norm ratios `‖convOp μ f‖₂ / ‖f‖₂` over nonzero mean-zero functions
`f : G → ℂ` is bounded above (so the supremum `σ₁(T_μ)` is well-defined). -/
lemma sigma1_bddAbove_general (μ : G → ℂ) :
    BddAbove {r : ℝ | ∃ f : G → ℂ, IsMeanZero f ∧ l2NormSq f ≠ 0 ∧
      r = Real.sqrt (l2NormSq (convOp μ f)) / Real.sqrt (l2NormSq f)} := by
  refine ⟨Real.sqrt ((Fintype.card G : ℝ) * l2NormSq μ), fun r ⟨f, _, hf_ne, hr⟩ => ?_⟩
  rw [hr]
  have hf_pos : 0 < l2NormSq f := lt_of_le_of_ne
    (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)) (Ne.symm hf_ne)
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hf_pos)]
  have hmul_nn : (0 : ℝ) ≤ (Fintype.card G : ℝ) * l2NormSq μ :=
    mul_nonneg (Nat.cast_nonneg' (Fintype.card G))
      (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2))
  rw [← Real.sqrt_mul hmul_nn]
  apply Real.sqrt_le_sqrt
  simp only [l2NormSq, convOp, groupConv]
  have hpw : ∀ g : G, ‖∑ g₁ : G, f g₁ * μ (g₁⁻¹ * g)‖ ^ 2 ≤
      (∑ h : G, ‖f h‖ ^ 2) * (∑ h : G, ‖μ h‖ ^ 2) := by
    intro g
    have hrhs : (∑ h : G, ‖μ (h⁻¹ * g)‖ ^ 2) = ∑ h : G, ‖μ h‖ ^ 2 :=
      Fintype.sum_equiv ((Equiv.mulLeft g⁻¹).trans (Equiv.inv G)) _ _ (fun h => by
        simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.inv_apply]; congr 1; congr 1; group)
    calc ‖∑ g₁ : G, f g₁ * μ (g₁⁻¹ * g)‖ ^ 2
        ≤ (∑ h : G, ‖f h‖ * ‖μ (h⁻¹ * g)‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_mul_le _ _))
      _ ≤ (∑ h : G, ‖f h‖ ^ 2) * (∑ h : G, ‖μ (h⁻¹ * g)‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = _ := by rw [hrhs]
  calc ∑ g : G, ‖∑ g₁, f g₁ * μ (g₁⁻¹ * g)‖ ^ 2
      ≤ ∑ _ : G, ((∑ h : G, ‖f h‖ ^ 2) * (∑ h : G, ‖μ h‖ ^ 2)) :=
        Finset.sum_le_sum (fun g _ => hpw g)
    _ = _ := by rw [Finset.sum_const, Fintype.card, nsmul_eq_mul]; ring

/-- Operator-norm bound: for any mean-zero `f : G → ℂ` with nonzero $L^2$ norm,
`‖convOp μ f‖₂² ≤ σ₁(T_μ)² · ‖f‖₂²`. -/
lemma l2NormSq_convOp_le_sigma1_sq (μ : G → ℂ) (f : G → ℂ)
    (hf_mz : IsMeanZero f) (hf_ne : l2NormSq f ≠ 0) :
    l2NormSq (convOp μ f) ≤ sigma1 μ ^ 2 * l2NormSq f := by
  have hf_pos : 0 < l2NormSq f := lt_of_le_of_ne
    (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)) (Ne.symm hf_ne)
  have h_in_set : Real.sqrt (l2NormSq (convOp μ f)) / Real.sqrt (l2NormSq f) ∈
      {r : ℝ | ∃ f : G → ℂ, IsMeanZero f ∧ l2NormSq f ≠ 0 ∧
        r = Real.sqrt (l2NormSq (convOp μ f)) / Real.sqrt (l2NormSq f)} :=
    ⟨f, hf_mz, hf_ne, rfl⟩
  have h_le : Real.sqrt (l2NormSq (convOp μ f)) / Real.sqrt (l2NormSq f) ≤ sigma1 μ :=
    le_csSup (sigma1_bddAbove_general μ) h_in_set
  have h_sqrt_le : Real.sqrt (l2NormSq (convOp μ f)) ≤ sigma1 μ * Real.sqrt (l2NormSq f) := by
    rwa [div_le_iff₀ (Real.sqrt_pos.mpr hf_pos)] at h_le
  have h_lhs_nn : (0 : ℝ) ≤ l2NormSq (convOp μ f) :=
    Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)
  calc l2NormSq (convOp μ f)
      = Real.sqrt (l2NormSq (convOp μ f)) ^ 2 := (Real.sq_sqrt h_lhs_nn).symm
    _ ≤ (sigma1 μ * Real.sqrt (l2NormSq f)) ^ 2 :=
        sq_le_sq' (by linarith [Real.sqrt_nonneg (l2NormSq (convOp μ f))]) h_sqrt_le
    _ = sigma1 μ ^ 2 * (Real.sqrt (l2NormSq f)) ^ 2 := by ring
    _ = sigma1 μ ^ 2 * l2NormSq f := by rw [Real.sq_sqrt hf_pos.le]

/-- Iterated operator-norm bound: for any mean-zero `f`, the $K$-fold convolution satisfies
`‖(T_μ)^K f‖₂² ≤ σ₁(T_μ)^{2K} · ‖f‖₂²`. -/
lemma l2NormSq_iterate_convOp_le (μ : G → ℂ) (f : G → ℂ)
    (hf_mz : IsMeanZero f) (K : ℕ) :
    l2NormSq ((convOp μ)^[K] f) ≤ sigma1 μ ^ (2 * K) * l2NormSq f := by
  induction K with
  | zero => simp [pow_zero, one_mul]
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, show 2 * (n + 1) = 2 * n + 2 from by ring,
        pow_add]
    have hmz_n : IsMeanZero ((convOp μ)^[n] f) := iterate_convOp_meanZero μ f hf_mz n
    by_cases hfn : l2NormSq ((convOp μ)^[n] f) = 0
    ·
      have h_zero : ∀ g : G, (convOp μ)^[n] f g = 0 := by
        intro g
        have hle : ‖(convOp μ)^[n] f g‖ ^ 2 ≤ l2NormSq ((convOp μ)^[n] f) :=
          Finset.single_le_sum (fun _ _ => pow_nonneg (norm_nonneg _) 2) (Finset.mem_univ g)
        have h0 : ‖(convOp μ)^[n] f g‖ = 0 := by nlinarith [hfn, norm_nonneg ((convOp μ)^[n] f g)]
        exact norm_eq_zero.mp h0
      have hconv_zero : l2NormSq (convOp μ ((convOp μ)^[n] f)) = 0 := by
        simp only [l2NormSq, convOp, groupConv]
        apply Finset.sum_eq_zero; intro g _; simp [h_zero, norm_zero]
      linarith [hconv_zero,
        show (0 : ℝ) ≤ sigma1 μ ^ (2 * n) * sigma1 μ ^ 2 * l2NormSq f from by
          apply mul_nonneg
          · apply mul_nonneg
            · have : sigma1 μ ^ (2 * n) = (sigma1 μ ^ 2) ^ n := by rw [← pow_mul]
              rw [this]; exact pow_nonneg (sq_nonneg (sigma1 μ)) n
            · exact sq_nonneg (sigma1 μ)
          · exact Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)]
    · calc l2NormSq (convOp μ ((convOp μ)^[n] f))
          ≤ sigma1 μ ^ 2 * l2NormSq ((convOp μ)^[n] f) :=
            l2NormSq_convOp_le_sigma1_sq μ _ hmz_n hfn
        _ ≤ sigma1 μ ^ 2 * (sigma1 μ ^ (2 * n) * l2NormSq f) := by gcongr
        _ = sigma1 μ ^ (2 * n) * sigma1 μ ^ 2 * l2NormSq f := by ring

/-- The function `δ_{1_G} - 1/|G|` (point mass at the identity minus the uniform
distribution) has total sum zero. -/
lemma delta_sub_uniform_meanZero :
    IsMeanZero (fun g : G => (if g = (1 : G) then 1 else 0) - (1 : ℂ) / (Fintype.card G : ℂ)) := by
  simp only [IsMeanZero]
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ g : G, (if g = (1 : G) then (1 : ℂ) else 0) = 1 := by
    rw [Fintype.sum_eq_single 1 (fun b hb => by simp [hb])]; simp
  have h2 : ∑ _ : G, (1 : ℂ) / (Fintype.card G : ℂ) = 1 := by
    rw [Finset.sum_const, Fintype.card, nsmul_eq_mul]; field_simp
  rw [h1, h2, sub_self]

/-- The squared $L^2$ norm of `δ_{1_G} - 1/|G|` is at most $1$ (in fact equals $1 - 1/|G|$). -/
lemma l2NormSq_delta_sub_uniform_le_one :
    l2NormSq (fun g : G => (if g = (1 : G) then 1 else 0) -
      (1 : ℂ) / (Fintype.card G : ℂ)) ≤ 1 := by
  simp only [l2NormSq]
  set n := Fintype.card G
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
  have hn_ge : 1 ≤ n := Fintype.card_pos
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))]
  have h1 : ‖(if (1 : G) = (1 : G) then (1 : ℂ) else 0) - 1 / (↑n : ℂ)‖ ^ 2 =
      (1 - 1 / (n : ℝ)) ^ 2 := by
    simp only [if_true]
    rw [show (1 : ℂ) - 1 / (↑n : ℂ) = ((1 - 1 / (n : ℝ) : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h2 : ∀ g ∈ Finset.univ.erase (1 : G),
      ‖(if g = (1 : G) then (1 : ℂ) else 0) - 1 / (↑n : ℂ)‖ ^ 2 = (1 / (n : ℝ)) ^ 2 := by
    intro g hg
    rw [Finset.mem_erase] at hg
    simp only [hg.1, ite_false]
    rw [show (0 : ℂ) - 1 / (↑n : ℂ) = ((-(1 / (n : ℝ)) : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, neg_sq]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_const]
  have hcard : (Finset.univ.erase (1 : G)).card = n - 1 :=
    Finset.card_erase_of_mem (Finset.mem_univ _)
  rw [hcard, nsmul_eq_mul]
  have hcast : (↑(n - 1) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn_ge]; simp
  rw [hcast]
  have key : (1 - 1 / (n : ℝ)) ^ 2 + ((n : ℝ) - 1) * (1 / (n : ℝ)) ^ 2 = 1 - 1 / (n : ℝ) := by
    field_simp; ring
  linarith [key, div_pos (one_pos) hn_pos]

/-- $L^2$ mixing for random walks on finite groups: if `μ` is a probability measure on a
finite group `G` with second-largest singular value `σ₁(T_μ)`, then after `K` steps the
distribution `convPow μ K` is close to uniform in $L^2$:
$$\|T_\mu^K \delta_{g_0} - 1/|G|\|_{L^2}^2 \le \sigma_1(T_\mu)^{2K}.$$ -/
theorem l2_mixing_sigma1 {G : Type*} [Fintype G] [DecidableEq G] [Group G]
    (μ : G → ℂ) (K : ℕ)
    (hμ_prob : ∑ g : G, μ g = 1) :
    l2NormSq (fun g => convPow μ K g - (1 : ℂ) / Fintype.card G)
    ≤ (sigma1 μ) ^ (2 * K) := by

  have h_eq := convPow_sub_const μ ((1 : ℂ) / Fintype.card G) hμ_prob K
  rw [h_eq]

  set φ := (fun g : G => (if g = (1 : G) then 1 else 0) - (1 : ℂ) / (Fintype.card G : ℂ))
  have hφ_mz : IsMeanZero φ := delta_sub_uniform_meanZero

  have h_iter := l2NormSq_iterate_convOp_le μ φ hφ_mz K

  have h_phi_le := l2NormSq_delta_sub_uniform_le_one (G := G)

  calc l2NormSq ((convOp μ)^[K] φ)
      ≤ sigma1 μ ^ (2 * K) * l2NormSq φ := h_iter
    _ ≤ sigma1 μ ^ (2 * K) * 1 := by
        apply mul_le_mul_of_nonneg_left h_phi_le
        have : sigma1 μ ^ (2 * K) = (sigma1 μ ^ 2) ^ K := by rw [← pow_mul]
        rw [this]; exact pow_nonneg (sq_nonneg _) K
    _ = sigma1 μ ^ (2 * K) := mul_one _

end L2Mixing

end SelbergExpansion
