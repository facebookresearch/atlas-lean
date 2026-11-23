/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Atlas.HighDimensionalStatistics.code.Chapter3.TrigOrtho
import Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_11

open Finset Real Set MeasureTheory

/-- The (infinite-dimensional) Sobolev ellipsoid `Θ(β, Q)`: the set of sequences `θ` such
that the weighted sum `∑ⱼ aⱼ² θⱼ²` (with Sobolev weights `aⱼ`) is summable and bounded by `Q`. -/
noncomputable def SobolevEllipsoidInf (β Q : ℝ) : Set (ℕ → ℝ) :=
  {θ | Summable (fun j : ℕ => (Chapter3.sobolevCoeff β (j + 1)) ^ 2 * (θ j) ^ 2) ∧
       ∑' j : ℕ, (Chapter3.sobolevCoeff β (j + 1)) ^ 2 * (θ j) ^ 2 ≤ Q}

/-- If two sequences are square-summable then their pointwise product is summable
(via the AM–GM bound `|fg| ≤ (f² + g²) / 2`). -/
lemma summable_mul_of_summable_sq {ι : Type*} {f g : ι → ℝ}
    (hf : Summable (fun j => f j ^ 2))
    (hg : Summable (fun j => g j ^ 2)) :
    Summable (fun j => f j * g j) := by
  apply Summable.of_norm_bounded (g := fun j => (f j ^ 2 + g j ^ 2) / 2)
  · exact (hf.add hg).div_const 2
  · intro j; rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (f j), sq_abs (g j), sq_nonneg (|f j| - |g j|)]

/-- Cauchy–Schwarz inequality for `tsum`: `(∑ⱼ fⱼ gⱼ)² ≤ (∑ⱼ fⱼ²)(∑ⱼ gⱼ²)`. -/
lemma tsum_inner_mul_le {ι : Type*} {f g : ι → ℝ}
    (hf : Summable (fun j => f j ^ 2))
    (hg : Summable (fun j => g j ^ 2))
    (hfg : Summable (fun j => f j * g j)) :
    (∑' j, f j * g j) ^ 2 ≤ (∑' j, f j ^ 2) * (∑' j, g j ^ 2) := by
  set A := ∑' j, f j ^ 2 with hA_def
  set B := ∑' j, f j * g j with hB_def
  set C := ∑' j, g j ^ 2 with hC_def
  have hA_nn : 0 ≤ A := tsum_nonneg (fun j => sq_nonneg _)

  have h_quad : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * B + C := by
    intro t
    calc 0 ≤ ∑' j, (t * f j - g j) ^ 2 := tsum_nonneg (fun j => sq_nonneg _)
      _ = ∑' j, (t ^ 2 * f j ^ 2 + (g j ^ 2 - 2 * t * (f j * g j))) := by
          congr 1; ext j; ring
      _ = t ^ 2 * A + (C - 2 * t * B) := by
          rw [(hf.mul_left _).tsum_add (hg.sub (hfg.mul_left _)),
              tsum_mul_left, hg.tsum_sub (hfg.mul_left _), tsum_mul_left]
      _ = t ^ 2 * A - 2 * t * B + C := by ring

  suffices h : 0 ≤ A * C - B ^ 2 by linarith
  by_cases hA0 : A = 0
  ·
    have hB0 : B = 0 := by
      by_contra hB
      have := h_quad ((C + 1) / (2 * B))
      have : -2 * ((C + 1) / (2 * B)) * B = -(C + 1) := by field_simp
      nlinarith [hA0]
    rw [hA0, hB0]; simp
  · have hA_pos : 0 < A := lt_of_le_of_ne hA_nn (Ne.symm hA0)
    have key : ∀ t, 0 ≤ (t * A - B) ^ 2 + (A * C - B ^ 2) := by
      intro t; nlinarith [h_quad t]
    have h1 := key (B / A)
    have h2 : B / A * A = B := div_mul_cancel₀ B (ne_of_gt hA_pos)
    nlinarith [sq_nonneg (B / A * A - B)]

/-- The Sobolev weight at index `j + 1` is at least `j^β`. -/
lemma sobolevCoeff_succ_ge (β : ℝ) (hβ : 0 < β) (j : ℕ) :
    (j : ℝ) ^ β ≤ Chapter3.sobolevCoeff β (j + 1) := by
  unfold Chapter3.sobolevCoeff
  split_ifs with h
  · apply rpow_le_rpow (Nat.cast_nonneg j) _ hβ.le
    push_cast; linarith
  · simp

/-- For `j ≥ M`, the Sobolev weight at index `j + 1` is at least `M^β`. -/
lemma sobolevCoeff_succ_ge_of_le (β : ℝ) (hβ : 0 < β) (M j : ℕ) (hj : M ≤ j) :
    (M : ℝ) ^ β ≤ Chapter3.sobolevCoeff β (j + 1) := by
  calc (M : ℝ) ^ β ≤ (j : ℝ) ^ β := by
        apply rpow_le_rpow (Nat.cast_nonneg M) (by exact_mod_cast hj) hβ.le
    _ ≤ Chapter3.sobolevCoeff β (j + 1) := sobolevCoeff_succ_ge β hβ j

/-- The Sobolev weight at index `j + 1` is positive whenever `j ≥ 1`. -/
lemma sobolevCoeff_succ_pos (β : ℝ) (_hβ : 0 < β) (j : ℕ) (hj : 1 ≤ j) :
    0 < Chapter3.sobolevCoeff β (j + 1) := by
  unfold Chapter3.sobolevCoeff
  split_ifs
  · exact rpow_pos_of_pos (by exact_mod_cast show 0 < j + 1 by omega) _
  · simp only [Nat.add_sub_cancel]
    exact rpow_pos_of_pos (by exact_mod_cast show 0 < j by omega) _

/-- The Sobolev weight at index `j + 1` is nonzero whenever `j ≥ 1`. -/
lemma sobolevCoeff_succ_ne_zero (β : ℝ) (hβ : 0 < β) (j : ℕ) (hj : 1 ≤ j) :
    Chapter3.sobolevCoeff β (j + 1) ≠ 0 :=
  ne_of_gt (sobolevCoeff_succ_pos β hβ j hj)

/-- For `j ≥ 1`, the squared Sobolev weight is at least `1`. -/
lemma sobolev_weight_ge_one (β : ℝ) (hβ : 0 < β) (j : ℕ) (hj : 1 ≤ j) :
    (1 : ℝ) ≤ (Chapter3.sobolevCoeff β (j + 1)) ^ 2 := by
  have h1 : (1 : ℝ) ≤ (j : ℝ) ^ β := one_le_rpow (by exact_mod_cast hj) hβ.le
  have h2 := sobolevCoeff_succ_ge β hβ j
  have h3 : (1 : ℝ) ≤ Chapter3.sobolevCoeff β (j + 1) := le_trans h1 h2
  nlinarith [sq_nonneg (Chapter3.sobolevCoeff β (j + 1) - 1)]

/-- For `j ≥ M`, the squared Sobolev weight at index `j + 1` is at least `M^{2β}`. -/
lemma sobolev_weight_ge_rpow (β : ℝ) (hβ : 0 < β) (M j : ℕ) (hj : M ≤ j) :
    (M : ℝ) ^ (2 * β) ≤ (Chapter3.sobolevCoeff β (j + 1)) ^ 2 := by
  have hcoeff := sobolevCoeff_succ_ge_of_le β hβ M j hj
  have hM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hcoeff_nn : (0 : ℝ) ≤ Chapter3.sobolevCoeff β (j + 1) :=
    le_trans (rpow_nonneg hM_nn _) hcoeff
  have hM_rpow_nn : (0 : ℝ) ≤ (M : ℝ) ^ β := rpow_nonneg hM_nn _
  calc (M : ℝ) ^ (2 * β)
      = ((M : ℝ) ^ β) ^ 2 := by
        rw [← rpow_natCast ((M : ℝ) ^ β) 2, ← rpow_mul hM_nn]; ring_nf
    _ ≤ (Chapter3.sobolevCoeff β (j + 1)) ^ 2 := by
        exact pow_le_pow_left₀ hM_rpow_nn hcoeff 2

/-- A sequence in the Sobolev ellipsoid with `β > 1/2` is square-summable. -/
lemma summable_sq_of_sobolev {β Q : ℝ} (hβ : 1/2 < β) (θ : ℕ → ℝ)
    (hθ : θ ∈ SobolevEllipsoidInf β Q) :
    Summable (fun j : ℕ => (θ j) ^ 2) := by
  obtain ⟨hsum, _⟩ := hθ
  have hβ_pos : (0 : ℝ) < β := by linarith

  have h_tail : Summable (fun j : ℕ => (θ (j + 1)) ^ 2) := by
    have hsumshift : Summable (fun j =>
        (Chapter3.sobolevCoeff β (j + 1 + 1)) ^ 2 * (θ (j + 1)) ^ 2) :=
      hsum.comp_injective (fun a b h => by omega)
    exact Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => by
        nlinarith [sq_nonneg (θ (j + 1)),
                   sobolev_weight_ge_one β hβ_pos (j + 1) (by omega)])
      hsumshift
  exact (summable_nat_add_iff 1).mp h_tail

/-- L²([0, 1]) orthonormality of the trigonometric basis indexed from `1`. -/
lemma trigBasis_L2_orthonormal (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    ∫ x in Icc (0 : ℝ) 1, Chapter3.trigBasis j x * Chapter3.trigBasis k x =
      if j = k then 1 else 0 := trigBasis_L2_orthonormal' j k hj hk

/-- A sequence in the Sobolev ellipsoid with `β > 1/2` is absolutely summable; this follows
from Cauchy–Schwarz applied to `(aⱼ θⱼ)` and `(aⱼ⁻¹)`. -/
lemma summable_of_sobolev {β Q : ℝ} (hβ : 1/2 < β) (θ : ℕ → ℝ)
    (hθ : θ ∈ SobolevEllipsoidInf β Q) :
    Summable θ := by
  obtain ⟨hsum, _hle⟩ := hθ
  have hβ_pos : (0 : ℝ) < β := by linarith

  suffices h_tail : Summable (fun j : ℕ => θ (j + 1)) by
    exact (summable_nat_add_iff 1).mp h_tail


  have ha_pos : ∀ j : ℕ, 0 < Chapter3.sobolevCoeff β (j + 1 + 1) :=
    fun j => sobolevCoeff_succ_pos β hβ_pos (j + 1) (by omega)
  have ha_ne : ∀ j : ℕ, Chapter3.sobolevCoeff β (j + 1 + 1) ≠ 0 :=
    fun j => ne_of_gt (ha_pos j)

  set f : ℕ → ℝ := fun j => Chapter3.sobolevCoeff β (j + 1 + 1) * |θ (j + 1)|
  set g : ℕ → ℝ := fun j => (Chapter3.sobolevCoeff β (j + 1 + 1))⁻¹

  have hfg_eq : (fun j => f j * g j) = (fun j => |θ (j + 1)|) := by
    ext j; simp only [f, g]
    rw [show Chapter3.sobolevCoeff β (j + 1 + 1) * |θ (j + 1)| *
        (Chapter3.sobolevCoeff β (j + 1 + 1))⁻¹ =
        |θ (j + 1)| * (Chapter3.sobolevCoeff β (j + 1 + 1) *
        (Chapter3.sobolevCoeff β (j + 1 + 1))⁻¹) from by ring]
    rw [mul_inv_cancel₀ (ha_ne j), mul_one]

  have hf_sq : Summable (fun j => f j ^ 2) := by
    have heq : (fun j => f j ^ 2) = (fun j =>
        (Chapter3.sobolevCoeff β (j + 1 + 1)) ^ 2 * (θ (j + 1)) ^ 2) := by
      ext j; simp only [f, mul_pow, sq_abs]
    rw [heq]
    exact hsum.comp_injective (fun a b h => by omega)

  have hg_sq : Summable (fun j => g j ^ 2) := by
    have h_pseries : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (-(2 * β))) := by
      have : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * β))) :=
        Real.summable_nat_rpow.mpr (by linarith)
      have h_eq : (fun j : ℕ => ((j : ℝ) + 1) ^ (-(2 * β))) =
          (fun n : ℕ => (n : ℝ) ^ (-(2 * β))) ∘ (· + 1) := by
        ext j; simp [Function.comp, Nat.cast_succ]
      rw [h_eq]
      exact this.comp_injective (fun a b h => by omega)
    apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) _ h_pseries
    intro j; simp only [g]
    have hj1_pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj1β_pos : (0 : ℝ) < ((j : ℝ) + 1) ^ β := rpow_pos_of_pos hj1_pos _
    have h_ge := sobolevCoeff_succ_ge β hβ_pos (j + 1)
    rw [show (↑(j + 1) : ℝ) = (j : ℝ) + 1 from by push_cast; ring] at h_ge
    calc (Chapter3.sobolevCoeff β (j + 1 + 1))⁻¹ ^ 2
        ≤ (((j : ℝ) + 1) ^ β)⁻¹ ^ 2 := by
          apply pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt (ha_pos j)))
          exact inv_anti₀ hj1β_pos h_ge
      _ = ((j : ℝ) + 1) ^ (-(2 * β)) := by
          rw [inv_pow, ← rpow_natCast (((j : ℝ) + 1) ^ β) 2,
              rpow_neg hj1_pos.le, ← rpow_mul hj1_pos.le]
          norm_num; ring_nf

  have hfg_sum := summable_mul_of_summable_sq hf_sq hg_sq

  rw [hfg_eq] at hfg_sum

  exact hfg_sum.of_abs

/-- If `θ` is summable then the series `∑ⱼ θⱼ φⱼ₊₁(x)` is summable at every point `x`
(using the uniform bound `|φⱼ(x)| ≤ √2`). -/
lemma summable_trigBasis_mul (θ : ℕ → ℝ) (x : ℝ)
    (h_abs_sum : Summable θ) :
    Summable (fun j : ℕ => θ j * Chapter3.trigBasis (j + 1) x) := by
  apply Summable.of_norm_bounded (g := fun j => Real.sqrt 2 * |θ j|)
  · exact h_abs_sum.abs.mul_left _
  · intro j
    simp only [Real.norm_eq_abs, abs_mul]
    calc |θ j| * |Chapter3.trigBasis (j + 1) x|
        ≤ |θ j| * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left (Chapter3.trigBasis_bounded _ _) (abs_nonneg _)
      _ = Real.sqrt 2 * |θ j| := mul_comm _ _

/-- The tail `∑' j, f j - ∑ j ∈ range M, f j` of a summable real series equals the
sum over indices `≥ M`. -/
lemma tsum_sub_sum_range {f : ℕ → ℝ} (hf : Summable f) (M : ℕ) :
    ∑' j, f j - ∑ j ∈ Finset.range M, f j = ∑' (j : ↑(Set.Ici M)), f ↑j := by

  have h_shift : HasSum (fun n => f (n + M)) (∑' j, f j - ∑ j ∈ Finset.range M, f j) := by
    rw [hasSum_nat_add_iff M, sub_add_cancel]
    exact hf.hasSum
  have h1 : ∑' n, f (n + M) = ∑' j, f j - ∑ j ∈ Finset.range M, f j := h_shift.tsum_eq

  let equiv : ℕ ≃ ↑(Set.Ici M) :=
    { toFun := fun k => ⟨k + M, by simp [Set.mem_Ici]⟩
      invFun := fun j => (↑j : ℕ) - M
      left_inv := by intro k; simp
      right_inv := by intro j; ext; exact Nat.sub_add_cancel j.prop }
  have h2 : ∑' (j : ↑(Set.Ici M)), f ↑j = ∑' n, f (n + M) := by
    rw [← Equiv.tsum_eq equiv]; rfl
  linarith

/-- Rewrites the integrand of the truncation error as the squared tail series
`(∑'_{j ≥ M} θⱼ φⱼ₊₁(x))²`. -/
lemma integrand_tsum_sub_finsum_sq (θ : ℕ → ℝ) (M : ℕ)
    (h_abs_sum : Summable θ) :
    ∫ x in Icc (0 : ℝ) 1,
      (∑' j, θ j * Chapter3.trigBasis (j + 1) x -
       ∑ j ∈ Finset.range M, θ j * Chapter3.trigBasis (j + 1) x) ^ 2 =
    ∫ x in Icc (0 : ℝ) 1,
      (∑' (j : ↑(Set.Ici M)), θ ↑j * Chapter3.trigBasis (↑(↑j : ℕ) + 1) x) ^ 2 := by
  congr 1
  ext x
  congr 1
  exact tsum_sub_sum_range (summable_trigBasis_mul θ x h_abs_sum) M

/-- Expands the integral of `(∑'_{j ≥ M} θⱼ φⱼ₊₁)²` into a double tsum of products
`θⱼ θₖ ∫ φⱼ₊₁ φₖ₊₁`, justified by dominated convergence. -/
theorem integral_sq_tsum_eq_double_sum (θ : ℕ → ℝ) (M : ℕ)
    (h_sq_sum : Summable (fun j : ℕ => (θ j) ^ 2))
    (h_sum : Summable θ) :
    ∫ x in Icc (0 : ℝ) 1,
      (∑' (j : ↑(Set.Ici M)), θ ↑j * Chapter3.trigBasis (↑(↑j : ℕ) + 1) x) ^ 2 =
    ∑' (j : ↑(Set.Ici M)), ∑' (k : ↑(Set.Ici M)),
      θ ↑j * θ ↑k * ∫ x in Icc (0 : ℝ) 1,
        Chapter3.trigBasis (↑(↑j : ℕ) + 1) x * Chapter3.trigBasis (↑(↑k : ℕ) + 1) x := by


  let iciEquiv : ℕ ≃ ↑(Set.Ici M) :=
    { toFun := fun k => ⟨k + M, by simp [Set.mem_Ici]⟩
      invFun := fun j => (↑j : ℕ) - M
      left_inv := by intro k; simp
      right_inv := by intro j; ext; exact Nat.sub_add_cancel j.prop }

  have h_tsum_convert : ∀ (f : ℕ → ℝ),
      ∑' (j : ↑(Set.Ici M)), f ↑j = ∑' (k : ℕ), f (k + M) := by
    intro f; rw [← Equiv.tsum_eq iciEquiv]; rfl
  suffices h_rhs : ∑' (j : ↑(Ici M)), ∑' (k : ↑(Ici M)),
      θ ↑j * θ ↑k * ∫ x in Icc (0 : ℝ) 1,
        Chapter3.trigBasis (↑(↑j : ℕ) + 1) x * Chapter3.trigBasis (↑(↑k : ℕ) + 1) x =
      ∑' (j : ↑(Ici M)), (θ ↑j) ^ 2 by
    suffices h_lhs : ∫ x in Icc (0 : ℝ) 1,
        (∑' (j : ↑(Ici M)), θ ↑j * Chapter3.trigBasis (↑(↑j : ℕ) + 1) x) ^ 2 =
        ∑' (j : ↑(Ici M)), (θ ↑j) ^ 2 by
      rw [h_lhs, h_rhs]


    have h_integrand_eq : ∀ x : ℝ,
        ∑' (j : ↑(Ici M)), θ ↑j * Chapter3.trigBasis (↑j + 1) x =
        ∑' (k : ℕ), θ (k + M) * Chapter3.trigBasis (k + M + 1) x := by
      intro x; exact h_tsum_convert (fun j => θ j * Chapter3.trigBasis (j + 1) x)
    have h_int_rw : ∫ x in Icc (0 : ℝ) 1,
        (∑' (j : ↑(Ici M)), θ ↑j * Chapter3.trigBasis (↑j + 1) x) ^ 2 =
        ∫ x in Icc (0 : ℝ) 1,
        (∑' (k : ℕ), θ (k + M) * Chapter3.trigBasis (k + M + 1) x) ^ 2 := by
      congr 1; ext x; congr 1; exact h_integrand_eq x
    rw [h_int_rw]
    rw [h_tsum_convert (fun j => (θ j) ^ 2)]

    set a : ℕ → ℝ := fun k => θ (k + M) with ha_def
    have ha_sum : Summable a := h_sum.comp_injective (fun x y h => by omega)
    have ha_abs : Summable (fun k => |a k|) := ha_sum.abs

    have h_ptwise : ∀ x, Summable (fun k => a k * Chapter3.trigBasis (k + M + 1) x) := by
      intro x
      apply Summable.of_norm_bounded (g := fun k => Real.sqrt 2 * |a k|)
      · exact ha_abs.mul_left _
      · intro k; simp only [Real.norm_eq_abs, abs_mul]
        calc |a k| * |Chapter3.trigBasis (k + M + 1) x|
            ≤ |a k| * Real.sqrt 2 :=
              mul_le_mul_of_nonneg_left (Chapter3.trigBasis_bounded _ _) (abs_nonneg _)
          _ = Real.sqrt 2 * |a k| := mul_comm _ _

    set C := Real.sqrt 2 * ∑' k, |a k| with hC_def
    have hC_nn : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg (fun k => abs_nonneg _))

    have h_ptwise_tendsto : ∀ x, Filter.Tendsto
        (fun N => ∑ k ∈ Finset.range N, a k * Chapter3.trigBasis (k + M + 1) x)
        Filter.atTop (nhds (∑' k, a k * Chapter3.trigBasis (k + M + 1) x)) := by
      intro x; exact (h_ptwise x).hasSum.tendsto_sum_nat

    have h_bound : ∀ N x, |∑ k ∈ Finset.range N, a k * Chapter3.trigBasis (k + M + 1) x| ≤ C := by
      intro N x
      calc |∑ k ∈ Finset.range N, a k * Chapter3.trigBasis (k + M + 1) x|
          ≤ ∑ k ∈ Finset.range N, |a k * Chapter3.trigBasis (k + M + 1) x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.range N, (|a k| * |Chapter3.trigBasis (k + M + 1) x|) := by
            congr 1; ext k; exact abs_mul _ _
        _ ≤ ∑ k ∈ Finset.range N, (|a k| * Real.sqrt 2) := by
            apply Finset.sum_le_sum; intro k _
            exact mul_le_mul_of_nonneg_left (Chapter3.trigBasis_bounded _ _) (abs_nonneg _)
        _ = Real.sqrt 2 * ∑ k ∈ Finset.range N, |a k| := by
            rw [Finset.sum_congr rfl (fun i _ => show |a i| * Real.sqrt 2 = Real.sqrt 2 * |a i| from mul_comm _ _)]
            rw [← Finset.mul_sum]
        _ ≤ Real.sqrt 2 * ∑' k, |a k| := by
            apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
            exact Summable.sum_le_tsum _ (fun k _ => abs_nonneg _) ha_abs

    have h_sq_tendsto : ∀ x, Filter.Tendsto
        (fun N => (∑ k ∈ Finset.range N, a k * Chapter3.trigBasis (k + M + 1) x) ^ 2)
        Filter.atTop (nhds ((∑' k, a k * Chapter3.trigBasis (k + M + 1) x) ^ 2)) := by
      intro x; exact (h_ptwise_tendsto x).pow 2

    have h_sq_bound : ∀ N x,
        (∑ k ∈ Finset.range N, a k * Chapter3.trigBasis (k + M + 1) x) ^ 2 ≤ C ^ 2 := by
      intro N x
      have hle := h_bound N x
      have habs := abs_le.mp hle
      exact sq_le_sq' habs.1 habs.2

    have hC2_integrable : IntegrableOn (fun _ : ℝ => C ^ 2) (Icc 0 1) :=
      integrableOn_const (hs := measure_Icc_lt_top.ne)


    have h_DCT := tendsto_integral_of_dominated_convergence
      (fun _ : ℝ => C ^ 2)
      (fun N => ((continuous_finset_sum _ (fun k _ =>
        (Chapter3.trigBasis_continuous (k + M + 1)).const_mul _)).pow _).aestronglyMeasurable)
      hC2_integrable
      (fun N => by
        apply Filter.Eventually.of_forall; intro x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact h_sq_bound N x)
      (by apply Filter.Eventually.of_forall; intro x; exact h_sq_tendsto x)


    have h_fin_parseval : ∀ N, ∫ x in Icc (0 : ℝ) 1,
        (∑ k ∈ Finset.range N, a k * Chapter3.trigBasis (k + M + 1) x) ^ 2 =
        ∑ k ∈ Finset.range N, a k ^ 2 := by
      intro N

      have h_expand : ∀ x, (∑ k ∈ Finset.range N, a k * Chapter3.trigBasis (k + M + 1) x) ^ 2 =
          ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
            (a k * a l * (Chapter3.trigBasis (k + M + 1) x * Chapter3.trigBasis (l + M + 1) x)) := by
        intro x; rw [sq, Finset.sum_mul]
        congr 1; ext k; rw [Finset.mul_sum]; congr 1; ext l; ring
      simp_rw [h_expand]

      have hint : ∀ k l, IntegrableOn
          (fun x => a k * a l * (Chapter3.trigBasis (k + M + 1) x * Chapter3.trigBasis (l + M + 1) x))
          (Icc (0:ℝ) 1) := by
        intro k l
        exact ContinuousOn.integrableOn_compact isCompact_Icc
          ((continuous_const.mul ((Chapter3.trigBasis_continuous _).mul
            (Chapter3.trigBasis_continuous _))).continuousOn)
      rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ => hint k l))]
      simp_rw [integral_finset_sum _ (fun l _ => hint _ l)]

      simp_rw [MeasureTheory.integral_const_mul,
        trigBasis_L2_orthonormal _ _ (Nat.succ_pos _) (Nat.succ_pos _)]

      simp_rw [show ∀ k l, k + M + 1 = l + M + 1 ↔ k = l from fun k l => by omega]
      apply Finset.sum_congr rfl; intro k hk
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq, if_pos hk]; ring

    have h_lim_lhs := h_DCT
    simp_rw [h_fin_parseval] at h_lim_lhs
    have h_lim_rhs : Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, a k ^ 2)
        Filter.atTop (nhds (∑' k, a k ^ 2)) :=
      (h_sq_sum.comp_injective (fun x y h => by omega)).hasSum.tendsto_sum_nat
    exact tendsto_nhds_unique h_lim_lhs h_lim_rhs

  congr 1
  ext ⟨j, hj⟩

  conv_lhs =>
    arg 1; ext k
    rw [show ∫ x in Icc (0 : ℝ) 1,
        Chapter3.trigBasis ((⟨j, hj⟩ : ↑(Ici M)).val + 1) x *
        Chapter3.trigBasis (k.val + 1) x =
      if j = k.val then 1 else 0 from by
        rw [trigBasis_L2_orthonormal (j + 1) (k.val + 1) (Nat.succ_pos j) (Nat.succ_pos k.val)]
        simp only [Nat.succ_inj]]
  rw [tsum_eq_single ⟨j, hj⟩]
  · simp [sq]
  · intro ⟨k, hk⟩ hjk
    have hne : j ≠ k := fun h => hjk (Subtype.ext h.symm)
    simp [hne]

/-- Parseval identity for the L²([0, 1]) truncation error: the squared error of the
truncated trigonometric series equals the tail `∑'_{j ≥ M} θⱼ²`. -/
theorem parseval_truncation_L2_error (θ : ℕ → ℝ) (M : ℕ)
    (h_sq_sum : Summable (fun j : ℕ => (θ j) ^ 2))
    (h_abs_sum : Summable θ) :
    ∫ x in Icc (0 : ℝ) 1,
      (∑' j, θ j * Chapter3.trigBasis (j + 1) x -
       ∑ j ∈ Finset.range M, θ j * Chapter3.trigBasis (j + 1) x) ^ 2 =
    ∑' (j : ↑(Set.Ici M)), (θ ↑j) ^ 2 := by

  rw [integrand_tsum_sub_finsum_sq θ M h_abs_sum]

  rw [integral_sq_tsum_eq_double_sum θ M h_sq_sum h_abs_sum]


  congr 1
  ext ⟨j, hj⟩


  conv_lhs =>
    arg 1; ext k
    rw [show ∫ x in Icc (0 : ℝ) 1,
        Chapter3.trigBasis ((⟨j, hj⟩ : ↑(Set.Ici M)).val + 1) x *
        Chapter3.trigBasis (k.val + 1) x =
      if j = k.val then 1 else 0 from by
        rw [trigBasis_L2_orthonormal (j + 1) (k.val + 1) (Nat.succ_pos j) (Nat.succ_pos k.val)]
        simp only [Nat.succ_inj]]


  rw [tsum_eq_single ⟨j, hj⟩]
  · simp [sq]
  · intro ⟨k, hk⟩ hjk
    have hne : j ≠ k := fun h => hjk (Subtype.ext h.symm)
    simp [hne]

/-- L² truncation error on the Sobolev ellipsoid: for `θ ∈ Θ(β, Q)` and `M ≥ 1`,
`∑'_{j ≥ M} θⱼ² ≤ Q M^{-2β}`. -/
theorem approx_error_sobolev (M : ℕ) (β Q : ℝ) (hβ : 1/2 < β) (hM : 0 < M)
    (θ : ℕ → ℝ) (hθ : θ ∈ SobolevEllipsoidInf β Q) :
    ∑' (j : ↑(Set.Ici M)), (θ ↑j) ^ 2 ≤ Q * (M : ℝ) ^ (-(2 * β)) := by
  obtain ⟨hsum, hle⟩ := hθ
  have hβ_pos : (0 : ℝ) < β := by linarith
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hMinv_pos : (0 : ℝ) < (M : ℝ) ^ (-(2 * β)) := rpow_pos_of_pos hM_pos _
  have hsq_sum := summable_sq_of_sobolev hβ θ ⟨hsum, hle⟩

  have h_term : ∀ (j : ↑(Set.Ici M)),
      (θ ↑j) ^ 2 ≤ (M : ℝ) ^ (-(2 * β)) *
        ((Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θ ↑j) ^ 2) := by
    intro ⟨j, hj⟩
    simp only [Set.mem_Ici] at hj
    suffices h1 : 1 ≤ (M : ℝ) ^ (-(2 * β)) *
        (Chapter3.sobolevCoeff β (j + 1)) ^ 2 by
      nlinarith [sq_nonneg (θ j)]
    rw [rpow_neg hM_pos.le, inv_mul_eq_div,
        le_div_iff₀ (rpow_pos_of_pos hM_pos _)]
    simp only [one_mul]
    exact sobolev_weight_ge_rpow β hβ_pos M j hj

  calc ∑' (j : ↑(Set.Ici M)), (θ ↑j) ^ 2
      _ ≤ ∑' (j : ↑(Set.Ici M)), (M : ℝ) ^ (-(2 * β)) *
          ((Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θ ↑j) ^ 2) :=
        Summable.tsum_le_tsum h_term (hsq_sum.subtype _)
          ((Summable.mul_left _ hsum).subtype _)
      _ = (M : ℝ) ^ (-(2 * β)) *
          ∑' (j : ↑(Set.Ici M)),
            ((Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θ ↑j) ^ 2) :=
        tsum_mul_left
      _ ≤ (M : ℝ) ^ (-(2 * β)) *
          ∑' j : ℕ, (Chapter3.sobolevCoeff β (j + 1)) ^ 2 * (θ j) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hMinv_pos.le
        exact Summable.tsum_subtype_le _ _
          (fun j => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsum
      _ ≤ (M : ℝ) ^ (-(2 * β)) * Q :=
        mul_le_mul_of_nonneg_left hle hMinv_pos.le
      _ = Q * (M : ℝ) ^ (-(2 * β)) := mul_comm ..

/-- If `θ` lies in a Sobolev ellipsoid `Θ(β, Q)` then `Q ≥ 0`. -/
lemma Q_nonneg_of_sobolev {β Q : ℝ} {θ : ℕ → ℝ} (hθ : θ ∈ SobolevEllipsoidInf β Q) :
    0 ≤ Q := by
  obtain ⟨hsum, hle⟩ := hθ
  calc (0 : ℝ) ≤ ∑' j : ℕ, (Chapter3.sobolevCoeff β (j + 1)) ^ 2 * (θ j) ^ 2 :=
    tsum_nonneg (fun j => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ Q := hle

/-- Cauchy–Schwarz bound on the squared ℓ¹ tail: `(∑'_{j ≥ M} |θⱼ|)² ≤ Q · ∑'_{j ≥ M} aⱼ⁻²`. -/
lemma tail_abs_sum_sq_le (M : ℕ) (β Q : ℝ) (hβ : 1/2 < β) (hM : 0 < M)
    (θ : ℕ → ℝ) (hθ : θ ∈ SobolevEllipsoidInf β Q)
    (h_inv_sum : Summable (fun j : ℕ =>
      if Chapter3.sobolevCoeff β (j + 1) = 0 then 0
      else (Chapter3.sobolevCoeff β (j + 1)) ^ (-(2 : ℝ)))) :
    (∑' (j : ↑(Set.Ici M)), |θ ↑j|) ^ 2 ≤
    Q * ∑' (j : ↑(Set.Ici M)),
      (if Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) = 0 then 0
       else (Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ (-(2 : ℝ))) := by
  obtain ⟨hsum, hle⟩ := hθ
  have hβ_pos : (0 : ℝ) < β := by linarith

  have ha_pos : ∀ (j : ↑(Set.Ici M)), 0 < Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) := by
    intro ⟨j, hj⟩
    simp only [Set.mem_Ici] at hj
    exact sobolevCoeff_succ_pos β hβ_pos j (by omega)
  have ha_ne : ∀ (j : ↑(Set.Ici M)), Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) ≠ 0 :=
    fun j => ne_of_gt (ha_pos j)

  set f' : ↑(Set.Ici M) → ℝ := fun j => Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) * |θ ↑j|
  set g' : ↑(Set.Ici M) → ℝ := fun j => (Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1))⁻¹

  have hfg_eq : (fun j : ↑(Set.Ici M) => f' j * g' j) =
      (fun j : ↑(Set.Ici M) => |θ ↑j|) := by
    ext j; simp only [f', g']
    rw [show Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) * |θ ↑j| *
        (Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1))⁻¹ =
        Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) * |θ ↑j| /
        Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) from by ring]
    rw [div_eq_iff (ha_ne j), mul_comm]

  have hf_sq_eq : (fun j : ↑(Set.Ici M) => f' j ^ 2) =
      (fun j : ↑(Set.Ici M) =>
        Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) ^ 2 * (θ ↑j) ^ 2) := by
    ext j; simp only [f', mul_pow, sq_abs]

  have hg_sq_eq : (fun j : ↑(Set.Ici M) => g' j ^ 2) =
      (fun j : ↑(Set.Ici M) =>
        if Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) = 0 then 0
        else (Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ (-(2 : ℝ))) := by
    ext j; simp only [g', if_neg (ha_ne j)]
    rw [inv_pow, ← rpow_natCast _ 2, rpow_neg (le_of_lt (ha_pos j))]
    norm_cast

  have hf_sq_sum : Summable (fun j : ↑(Set.Ici M) => f' j ^ 2) := by
    rw [hf_sq_eq]; exact hsum.subtype _
  have hg_sq_sum : Summable (fun j : ↑(Set.Ici M) => g' j ^ 2) := by
    rw [hg_sq_eq]; exact h_inv_sum.subtype _
  have hfg_sum : Summable (fun j : ↑(Set.Ici M) => f' j * g' j) :=
    summable_mul_of_summable_sq hf_sq_sum hg_sq_sum

  have hCS := tsum_inner_mul_le hf_sq_sum hg_sq_sum hfg_sum
  rw [hfg_eq, hf_sq_eq, hg_sq_eq] at hCS

  have h_sub_le : ∑' (j : ↑(Set.Ici M)),
      Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) ^ 2 * (θ ↑j) ^ 2 ≤ Q :=
    le_trans (Summable.tsum_subtype_le _ _
      (fun j => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsum) hle

  calc (∑' (j : ↑(Set.Ici M)), |θ ↑j|) ^ 2
      _ ≤ (∑' j : ↑(Set.Ici M),
            Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) ^ 2 * (θ ↑j) ^ 2) *
          (∑' j : ↑(Set.Ici M),
            if Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) = 0 then 0
            else (Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ (-(2 : ℝ))) := hCS
      _ ≤ Q * ∑' j : ↑(Set.Ici M),
            if Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) = 0 then 0
            else (Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ (-(2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right h_sub_le
        apply tsum_nonneg; intro j
        split_ifs <;> [exact le_refl 0; exact rpow_nonneg (le_of_lt (ha_pos j)) _]

/-- Equivalence between `ℕ` and the upper interval `Set.Ici n` via `k ↦ k + n`. -/
noncomputable def iciEquivNat (n : ℕ) : ℕ ≃ ↑(Set.Ici n) where
  toFun k := ⟨k + n, by simp [Set.mem_Ici]⟩
  invFun j := (↑j : ℕ) - n
  left_inv k := by simp
  right_inv j := by ext; exact Nat.sub_add_cancel j.prop

/-- A `tsum` over `Set.Ici n` equals the corresponding shifted `tsum` over `ℕ`. -/
lemma tsum_Ici_eq_tsum_add (f : ℕ → ℝ) (n : ℕ) :
    ∑' (j : ↑(Set.Ici n)), f (↑j : ℕ) = ∑' (k : ℕ), f (k + n) := by
  rw [← Equiv.tsum_eq (iciEquivNat n)]; rfl

/-- Integral test bound for partial sums of `(k + n + 1)^{-p}`: bounded by
`n^{1 - p} / (p - 1)` for `p > 1` and `n ≥ 1`. -/
lemma finite_sum_le_integral_bound (n N : ℕ) (p : ℝ) (hp : 1 < p) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range N, ((k + n + 1 : ℕ) : ℝ) ^ (-p) ≤ (n : ℝ) ^ (1 - p) / (p - 1) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Icc (n : ℝ) ((n : ℝ) + (N : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hn' hx.1) hxy (by linarith)
  have h_sum_le_int := AntitoneOn.sum_le_integral hanti
  have h_eq : ∀ k ∈ Finset.range N,
      ((k + n + 1 : ℕ) : ℝ) ^ (-p) = ((n : ℝ) + ↑(k + 1)) ^ (-p) := by
    intro k _; congr 1; push_cast; ring
  rw [Finset.sum_congr rfl h_eq]
  calc ∑ k ∈ Finset.range N, ((n : ℝ) + ↑(k + 1)) ^ (-p)
      ≤ ∫ x in (n : ℝ)..(n : ℝ) + (N : ℝ), x ^ (-p) := h_sum_le_int
    _ ≤ ∫ x in Set.Ioi (n : ℝ), x ^ (-p) := by
        rw [show (n : ℝ) + (N : ℝ) = ((n + N : ℕ) : ℝ) from by push_cast; ring]
        rw [intervalIntegral.integral_of_le (by exact_mod_cast Nat.le_add_right n N)]
        apply MeasureTheory.setIntegral_mono_set
        · exact integrableOn_Ioi_rpow_of_lt (by linarith) hn'
        · apply Filter.eventually_of_mem (MeasureTheory.self_mem_ae_restrict measurableSet_Ioi)
          intro x hx; exact Real.rpow_nonneg (le_of_lt (lt_trans hn' hx)) _
        · exact Filter.Eventually.of_forall (fun x hx => Set.Ioc_subset_Ioi_self hx)
    _ = (n : ℝ) ^ (1 - p) / (p - 1) := by
        have h := integral_Ioi_rpow_of_lt (a := -p) (by linarith) (c := (n : ℝ)) hn'
        rw [h, show (-p + 1 : ℝ) = 1 - p from by ring, neg_div, ← div_neg,
            show -(1 - p : ℝ) = p - 1 from by ring]

/-- The shifted `p`-series `∑ₖ (k + n)^{-p}` is summable for `p > 1`. -/
lemma summable_shifted_rpow_neg (n : ℕ) (p : ℝ) (hp : 1 < p) :
    Summable (fun k : ℕ => ((k + n : ℕ) : ℝ) ^ (-p)) := by
  have h : Summable (fun j : ℕ => ((j : ℝ)) ^ (-p)) := Real.summable_nat_rpow.mpr (by linarith)
  exact h.comp_injective (fun a b hab => by omega)

/-- Tail bound for the inverse-squared Sobolev weights via the integral test:
`∑'_{j ≥ n} aⱼ⁻² ≤ (2β / (2β - 1)) · n^{1 - 2β}`. -/
theorem sobolev_inv_weight_tail_bound (n : ℕ) (β : ℝ) (hβ : 1/2 < β) (hn : 0 < n) :
    ∑' (j : ↑(Set.Ici n)),
      (if Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) = 0 then 0
       else (Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ (-(2 : ℝ))) ≤
    2 * β / (2 * β - 1) * (n : ℝ) ^ (1 - 2 * β) := by
  have hβ_pos : (0 : ℝ) < β := by linarith
  have h2β : 1 < 2 * β := by linarith


  have h_term_bound : ∀ (j : ↑(Set.Ici n)),
      (if Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) = 0 then 0
       else (Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ (-(2 : ℝ))) ≤
      ((↑j : ℕ) : ℝ) ^ (-(2 * β)) := by
    intro ⟨j, hj⟩
    simp only [Set.mem_Ici] at hj
    have hj1 : 1 ≤ j := by omega
    have h_ne : Chapter3.sobolevCoeff β (j + 1) ≠ 0 :=
      sobolevCoeff_succ_ne_zero β hβ_pos j hj1
    simp only [h_ne, ite_false]


    have h_ge := sobolevCoeff_succ_ge β hβ_pos j
    have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast show 0 < j by omega
    have hj_rpow_pos : (0 : ℝ) < (j : ℝ) ^ β := rpow_pos_of_pos hj_pos _
    have h_coeff_pos := sobolevCoeff_succ_pos β hβ_pos j hj1

    have : (Chapter3.sobolevCoeff β (j + 1)) ^ (-(2 : ℝ)) ≤ ((j : ℝ) ^ β) ^ (-(2 : ℝ)) := by
      apply Real.rpow_le_rpow_of_nonpos hj_rpow_pos h_ge (by norm_num)
    calc (Chapter3.sobolevCoeff β (j + 1)) ^ (-(2 : ℝ))
        ≤ ((j : ℝ) ^ β) ^ (-(2 : ℝ)) := this
      _ = (j : ℝ) ^ (-(2 * β)) := by
          rw [← Real.rpow_mul (le_of_lt hj_pos)]
          congr 1; ring


  have h_rpow_bound : ∑' (j : ↑(Set.Ici n)), ((↑j : ℕ) : ℝ) ^ (-(2 * β)) ≤
      2 * β / (2 * β - 1) * (n : ℝ) ^ (1 - 2 * β) := by
    rw [tsum_Ici_eq_tsum_add (fun j => ((j : ℝ)) ^ (-(2 * β))) n]
    have hsum_shift : Summable (fun k : ℕ => ((k + n : ℕ) : ℝ) ^ (-(2 * β))) :=
      summable_shifted_rpow_neg n (2 * β) h2β
    rw [hsum_shift.tsum_eq_zero_add]
    simp only [Nat.zero_add]
    have h_eq : (fun k : ℕ => ((k + 1 + n : ℕ) : ℝ) ^ (-(2 * β))) =
        (fun k : ℕ => ((k + n + 1 : ℕ) : ℝ) ^ (-(2 * β))) := by
      ext k; congr 1; push_cast; ring
    rw [h_eq]

    have h_tail : ∑' (k : ℕ), ((k + n + 1 : ℕ) : ℝ) ^ (-(2 * β)) ≤
        (n : ℝ) ^ (1 - 2 * β) / (2 * β - 1) := by
      apply Real.tsum_le_of_sum_le
      · intro k; exact Real.rpow_nonneg (by positivity) _
      · intro u
        obtain ⟨M, hM⟩ : ∃ M : ℕ, u ⊆ Finset.range M :=
          ⟨u.sup id + 1, fun x hx => by
            simp only [Finset.mem_range]
            exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)⟩
        calc ∑ k ∈ u, ((k + n + 1 : ℕ) : ℝ) ^ (-(2 * β))
            ≤ ∑ k ∈ Finset.range M, ((k + n + 1 : ℕ) : ℝ) ^ (-(2 * β)) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hM
              intro k _ _; exact Real.rpow_nonneg (by positivity) _
          _ ≤ (n : ℝ) ^ (1 - 2 * β) / (2 * β - 1) :=
              finite_sum_le_integral_bound n M (2 * β) h2β (by omega)

    have h_npow : (n : ℝ) ^ (-(2 * β)) ≤ (n : ℝ) ^ (1 - 2 * β) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

    have h_split : 2 * β / (2 * β - 1) * (n : ℝ) ^ (1 - 2 * β) =
        (n : ℝ) ^ (1 - 2 * β) + (n : ℝ) ^ (1 - 2 * β) / (2 * β - 1) := by
      have h2β_ne : (2 : ℝ) * β - 1 ≠ 0 := by linarith
      field_simp; ring
    linarith

  calc ∑' (j : ↑(Set.Ici n)),
        (if Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) = 0 then 0
         else (Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ (-(2 : ℝ)))
      ≤ ∑' (j : ↑(Set.Ici n)), ((↑j : ℕ) : ℝ) ^ (-(2 * β)) := by
        have h_rpow_sum : Summable (fun (i : ↑(Set.Ici n)) => ((↑i : ℕ) : ℝ) ^ (-(2 * β))) :=
          (Real.summable_nat_rpow.mpr (show -(2 * β) < -1 by linarith)).subtype _
        apply Summable.tsum_le_tsum h_term_bound
        · apply Summable.of_nonneg_of_le
          · intro j
            split_ifs with h
            · exact le_refl 0
            · have hj_ge : 1 ≤ (↑j : ℕ) := le_trans hn j.2
              exact Real.rpow_nonneg (le_of_lt (sobolevCoeff_succ_pos β (by linarith) (↑j : ℕ) hj_ge)) _
          · exact h_term_bound
          · exact h_rpow_sum
        · exact h_rpow_sum
    _ ≤ 2 * β / (2 * β - 1) * (n : ℝ) ^ (1 - 2 * β) := h_rpow_bound

/-- Empirical (ℓ¹) tail bound on the Sobolev ellipsoid:
`2 n · (∑'_{j ≥ n} |θⱼ|)² ≤ (4β / (2β - 1)) · Q · n^{2 - 2β}`. -/
theorem approx_error_sobolev_empirical_bound (n : ℕ) (β Q : ℝ) (hβ : 1/2 < β)
    (hn : 0 < n) (θ : ℕ → ℝ) (hθ : θ ∈ SobolevEllipsoidInf β Q)
    (h_inv_sum : Summable (fun j : ℕ =>
      if Chapter3.sobolevCoeff β (j + 1) = 0 then 0
      else (Chapter3.sobolevCoeff β (j + 1)) ^ (-(2 : ℝ)))) :
    2 * (n : ℝ) * (∑' (j : ↑(Set.Ici n)), |θ ↑j|) ^ 2 ≤
    4 * β / (2 * β - 1) * Q * (n : ℝ) ^ (2 - 2 * β) := by

  have hCS := tail_abs_sum_sq_le n β Q hβ hn θ hθ h_inv_sum

  have hTail := sobolev_inv_weight_tail_bound n β hβ hn

  have hQ := Q_nonneg_of_sobolev hθ
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn

  calc 2 * (n : ℝ) * (∑' (j : ↑(Set.Ici n)), |θ ↑j|) ^ 2
      _ ≤ 2 * (n : ℝ) * (Q * ∑' (j : ↑(Set.Ici n)),
            (if Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1) = 0 then 0
             else (Chapter3.sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ (-(2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
      _ ≤ 2 * (n : ℝ) * (Q * (2 * β / (2 * β - 1) * (n : ℝ) ^ (1 - 2 * β))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hTail hQ
      _ = 4 * β / (2 * β - 1) * Q * (n : ℝ) ^ (2 - 2 * β) := by
        rw [show (2 : ℝ) - 2 * β = 1 + (1 - 2 * β) from by ring]
        rw [Real.rpow_add (by positivity : (0 : ℝ) < ↑n), rpow_one]
        ring

/-- Lemma 3.14 (Sobolev truncation bound): for `M ≥ 1` and `θ ∈ Θ(β, Q)` with `β > 1/2`,
the L² error of the truncated trigonometric series satisfies
`‖φ_{θ*}^M - f‖²_{L²} = ∑'_{j > M} |θⱼ*|² ≤ Q · M^{-2β}`, together with the empirical
ℓ¹ tail bound `2 n · (∑'_{j ≥ n} |θⱼ|)² ≤ (4β / (2β - 1)) · Q · n^{2 - 2β}`. -/
theorem lemma_3_14 (n : ℕ) (β Q : ℝ) (hβ : 1/2 < β) (hn : 0 < n)
    (θ : ℕ → ℝ) (hθ : θ ∈ SobolevEllipsoidInf β Q)
    (h_inv_sum : Summable (fun j : ℕ =>
      if Chapter3.sobolevCoeff β (j + 1) = 0 then 0
      else (Chapter3.sobolevCoeff β (j + 1)) ^ (-(2 : ℝ)))) :
    (∑' (j : ↑(Set.Ici n)), (θ ↑j) ^ 2 ≤ Q * (n : ℝ) ^ (-(2 * β))) ∧
    (2 * (n : ℝ) * (∑' (j : ↑(Set.Ici n)), |θ ↑j|) ^ 2 ≤
      4 * β / (2 * β - 1) * Q * (n : ℝ) ^ (2 - 2 * β)) :=
  ⟨approx_error_sobolev n β Q hβ hn θ hθ,
   approx_error_sobolev_empirical_bound n β Q hβ hn θ hθ h_inv_sum⟩
