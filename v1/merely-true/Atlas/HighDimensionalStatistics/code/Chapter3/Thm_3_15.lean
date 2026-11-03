/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter3.Remark_3_1
import Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_14
import Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_13
import Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_11

set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Real MeasureTheory

namespace Chapter3

/-- The squared `L²` norm of a real-valued function `g` over `[0,1]`,
defined as `∫₀¹ g(x)² dx`. -/
noncomputable def L2normSq (g : ℝ → ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, g x ^ 2

/-- The squared empirical norm of `g` evaluated on the uniform grid `{i/n : i = 0, …, n-1}`,
defined as `(1/n) ∑ g(i/n)²`. -/
noncomputable def empiricalNormSq (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, g ((i : ℝ) / (n : ℝ)) ^ 2

/-- Sub-Gaussian noise vector: the coordinates `ε ω i` of `ε : Ω → Fin n → ℝ` are
componentwise sub-Gaussian with variance proxy `σsq`, integrable, with integrable exponentials,
and satisfying the analogous bound for arbitrary linear combinations. -/
structure IsSubGaussianNoiseVec {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ε : Ω → Fin n → ℝ) (σsq : ℝ) (μ : Measure Ω) : Prop where
  bound : ∀ i : Fin n, ∀ s : ℝ,
    ∫ ω, Real.exp (s * ε ω i) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2)
  integ : ∀ i : Fin n, MeasureTheory.Integrable (fun ω => ε ω i) μ
  exp_integ : ∀ i : Fin n, ∀ s : ℝ,
    MeasureTheory.Integrable (fun ω => Real.exp (s * ε ω i)) μ
  weighted_sum_bound : ∀ (w : Fin n → ℝ), ∀ s : ℝ,
    ∫ ω, Real.exp (s * ∑ i, w i * ε ω i) ∂μ ≤
      Real.exp (σsq * (∑ i, w i ^ 2) * s ^ 2 / 2)

/-- Coerce an `IsSubGaussianNoiseVec` witness to its componentwise MGF bound. -/
instance {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {ε : Ω → Fin n → ℝ} {σsq : ℝ} {μ : Measure Ω} :
    CoeFun (IsSubGaussianNoiseVec ε σsq μ)
      (fun _ => ∀ i : Fin n, ∀ s : ℝ,
        ∫ ω, Real.exp (s * ε ω i) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2)) where
  coe := IsSubGaussianNoiseVec.bound

/-- The trigonometric linear combination `∑_{j=0}^{M-1} θ_j · φ_{j+1}(x)` where
`φ_k` denotes the `k`-th element of the trigonometric basis. -/
noncomputable def trigLinComb (M : ℕ) (θ : Fin M → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin M, θ j * trigBasis (j.val + 1) x

/-- `θhat` is a least-squares estimator for the trigonometric regression: for every
`ω` it minimizes the empirical squared error `∑ (Y_i - φ_θ(i/n))²` over all `θ`. -/
def IsLSEstimator {Ω : Type*} {n M : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin M → ℝ) : Prop :=
  ∀ ω θ,
    ∑ i : Fin n, (Y ω i - trigLinComb M (θhat ω) ((i : ℝ) / (n : ℝ))) ^ 2 ≤
    ∑ i : Fin n, (Y ω i - trigLinComb M θ ((i : ℝ) / (n : ℝ))) ^ 2

/-- The `(i,j)` entry of the trigonometric design matrix equals the basis function
`φ_{j+1}` evaluated at the grid point `i/n`. -/
lemma trigDesignMatrix_eq_trigBasis (n M : ℕ) (hn : 0 < n) (i : Fin n) (j : Fin M) :
    trigDesignMatrix n M i j = trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) := by
  simp only [trigDesignMatrix, trigBasis]
  have hj1 : j.val + 1 ≠ 0 := Nat.succ_ne_zero _
  simp only [hj1, ↓reduceIte]
  by_cases hj1eq : j.val + 1 = 1
  ·
    have hj0 : j.val = 0 := by omega
    simp [hj0]
  ·
    have hjge1 : j.val ≥ 1 := by omega
    simp only [hj1eq, ↓reduceIte]
    by_cases hjmod : j.val = 0
    · omega
    · simp only [show j.val ≠ 0 from hjmod]

      by_cases heven : (j.val + 1) % 2 = 0
      ·
        simp only [heven, ↓reduceIte]


        have hj_odd : j.val % 2 = 1 := by omega
        simp only [hj_odd, ↓reduceIte]


        congr 1
        have : (j.val + 1) / 2 = (j.val + 1) / 2 := rfl
        ring
      ·
        have hodd : (j.val + 1) % 2 = 1 := by omega
        simp only [show ¬((j.val + 1) % 2 = 0) from by omega, ↓reduceIte]


        have hj_even : j.val % 2 = 0 := by omega
        have hj_ne0 : ¬(j.val = 0) := hjmod
        simp only [hj_even]

        push_cast
        ring

/-- Empirical Parseval identity: the squared empirical norm of a trigonometric linear
combination on the uniform grid coincides with the sum of squared coefficients
(using orthonormality from Lemma 3.13). -/
lemma empirical_norm_eq_sum_sq (n M : ℕ) (hn : 0 < n) (hM : M ≤ n - 1)
    (θ : Fin M → ℝ) :
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (∑ j : Fin M, θ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 =
    ∑ j : Fin M, θ j ^ 2 := by

  have hΦ : ∀ i : Fin n,
      ∑ j : Fin M, θ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) =
      ∑ j : Fin M, trigDesignMatrix n M i j * θ j := by
    intro i
    congr 1; ext j
    rw [trigDesignMatrix_eq_trigBasis n M hn i j]; ring
  simp_rw [hΦ]


  set Φ := trigDesignMatrix n M
  have hmv : ∀ i, ∑ j : Fin M, Φ i j * θ j = (Φ.mulVec θ) i := by
    intro i; simp [Matrix.mulVec, dotProduct]
  simp_rw [hmv]

  have hdot_sum : ∑ i : Fin n, (Φ.mulVec θ i) ^ 2 =
      dotProduct (Φ.mulVec θ) (Φ.mulVec θ) := by
    simp [dotProduct, sq]
  rw [hdot_sum]

  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]

  rw [lemma_3_13 n M hn hM]

  rw [Matrix.vecMul_smul, Matrix.vecMul_one]

  rw [smul_dotProduct, smul_eq_mul]

  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  field_simp

  simp [dotProduct, sq]

/-- `L²([0,1])` orthonormality of the trigonometric basis `{φ_j}_{j≥1}`:
`∫₀¹ φ_j φ_{j'} dx = 1` if `j = j'` and `0` otherwise. -/
theorem trigBasis_L2_orthonormal (j j' : ℕ) (hj : 0 < j) (hj' : 0 < j') :
    ∫ x in Set.Icc (0 : ℝ) 1, trigBasis j x * trigBasis j' x =
    if j = j' then 1 else 0 :=
  trigBasis_orthonormal j j' hj hj'

/-- `L²([0,1])` Parseval identity for the trigonometric basis: the squared `L²`-norm of
a finite linear combination equals the sum of squared coefficients. -/
lemma L2_norm_eq_sum_sq (M : ℕ) (θ : Fin M → ℝ) :
    L2normSq (fun x => ∑ j : Fin M, θ j * trigBasis (j.val + 1) x) =
    ∑ j : Fin M, θ j ^ 2 := by
  unfold L2normSq


  have hcont : Continuous (fun x => ∑ j : Fin M, θ j * trigBasis (j.val + 1) x) :=
    continuous_finset_sum _ (fun j _ => continuous_const.mul
      (by unfold trigBasis; split_ifs <;> fun_prop))
  have hint : IntegrableOn (fun x =>
      (∑ j : Fin M, θ j * trigBasis (j.val + 1) x) ^ 2) (Set.Icc 0 1) :=
    (hcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc

  simp_rw [sq, Finset.sum_mul_sum]

  have hint_prod : ∀ j j' : Fin M,
      IntegrableOn (fun x => θ j * trigBasis (j.val + 1) x * (θ j' * trigBasis (j'.val + 1) x))
        (Set.Icc 0 1) :=
    fun j j' => ((continuous_const.mul
      (by unfold trigBasis; split_ifs <;> fun_prop)).mul
      (continuous_const.mul
      (by unfold trigBasis; split_ifs <;> fun_prop))).continuousOn.integrableOn_compact isCompact_Icc

  rw [integral_finset_sum _ (fun j _ =>
    integrable_finset_sum _ (fun j' _ => hint_prod j j'))]

  congr 1; ext j
  rw [integral_finset_sum _ (fun j' _ => hint_prod j j')]

  simp_rw [show ∀ (j' : Fin M) (x : ℝ),
    θ j * trigBasis (j.val + 1) x * (θ j' * trigBasis (j'.val + 1) x) =
    θ j * θ j' * (trigBasis (j.val + 1) x * trigBasis (j'.val + 1) x)
    from by intros; ring]
  simp_rw [integral_const_mul]
  simp_rw [trigBasis_L2_orthonormal _ _ (Nat.succ_pos _) (Nat.succ_pos _)]

  simp_rw [Nat.succ_inj, Fin.val_injective.eq_iff]
  simp

/-- Bridge between empirical and `L²` norms (Property ORT): for `M ≤ n - 1`, the squared
`L²`-norm of a trigonometric linear combination equals its squared empirical norm on the
uniform grid `{i/n}`. -/
theorem ORT_L2_eq_empirical_normSq
    (n M : ℕ) (hn : 0 < n) (hM : M ≤ n - 1) (θ : Fin M → ℝ) :
    L2normSq (fun x => ∑ j : Fin M, θ j * trigBasis (j.val + 1) x) =
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (∑ j : Fin M, θ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 := by

  rw [L2_norm_eq_sum_sq, empirical_norm_eq_sum_sq n M hn hM]

/-- The trigonometric linear combination evaluated on the uniform grid coincides with the
matrix-vector product of the design matrix and the coefficient vector. -/
lemma trigLinComb_eq_mulVec (n M : ℕ) (hn : 0 < n) (θ : Fin M → ℝ) (i : Fin n) :
    trigLinComb M θ ((i : ℝ) / (n : ℝ)) = (trigDesignMatrix n M).mulVec θ i := by
  simp only [trigLinComb, Matrix.mulVec, dotProduct]
  congr 1; ext j
  rw [trigDesignMatrix_eq_trigBasis n M hn i j]; ring

/-- Re-indexing a `Finset.range M` sum as a sum over `Fin M`. -/
lemma finset_range_eq_fin_sum (M : ℕ) (θstar : ℕ → ℝ) (x : ℝ) :
    ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x =
    ∑ j : Fin M, θstar j.val * trigBasis (j.val + 1) x := by
  rw [← Finset.sum_range (fun j => θstar j * trigBasis (j + 1) x)]

/-- The squared empirical norm of a difference of two trigonometric linear combinations
equals the sum of squared coefficient differences. -/
lemma empirical_diff_eq_coeff_sq
    (n M : ℕ) (hn : 0 < n) (hM : M ≤ n - 1)
    (θ₁ θ₂ : Fin M → ℝ) :
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (∑ j : Fin M, θ₁ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) -
       ∑ j : Fin M, θ₂ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 =
    ∑ j : Fin M, (θ₁ j - θ₂ j) ^ 2 := by

  have hdiff : ∀ i : Fin n,
      ∑ j : Fin M, θ₁ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) -
      ∑ j : Fin M, θ₂ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) =
      ∑ j : Fin M, (θ₁ j - θ₂ j) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    congr 1; ext j; ring
  simp_rw [hdiff]
  exact empirical_norm_eq_sum_sq n M hn hM (θ₁ - θ₂)

/-- Each column of the trigonometric design matrix has squared norm equal to `n` on the
uniform grid (follows from Lemma 3.13). -/
lemma trigBasis_col_sq_sum (n M : ℕ) (hn : 0 < n) (hM : M ≤ n - 1) (j : Fin M) :
    ∑ i : Fin n, (trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 = (n : ℝ) := by

  have h_eq : ∀ i : Fin n,
      trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) = trigDesignMatrix n M i j :=
    fun i => (trigDesignMatrix_eq_trigBasis n M hn i j).symm
  simp_rw [h_eq]


  have h_ort := lemma_3_13 n M hn hM
  have h_entry := congr_fun (congr_fun h_ort j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul] at h_entry
  simp only [if_true] at h_entry
  simp_rw [sq]
  linarith









/-- Truncation tail bound: for a Sobolev-class function with `β > 1/2`, the squared
`L²`-error from truncating the Fourier series at `M` terms is at most `Q · M^{-2β}`. -/
theorem fourier_tail_L2_bound
    (M : ℕ) (hM : 0 < M)
    (β Q : ℝ) (hβ : 1/2 < β) (hQ : 0 < Q)
    (θstar : ℕ → ℝ)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q) :
    L2normSq (fun x => (∑' j, θstar j * trigBasis (j + 1) x) -
      ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ≤
      Q * (M : ℝ) ^ (-(2 * β)) := by
  have hβ_pos : 0 < β := by linarith

  have hRange : ∀ K, ∑ i ∈ Finset.range K,
      (sobolevCoeff β (↑i + 1)) ^ 2 * (θstar ↑i) ^ 2 ≤ Q := by
    intro K
    rw [← Fin.sum_univ_eq_sum_range]
    exact hSobolev K

  have hnn : ∀ i, 0 ≤ (sobolevCoeff β (↑i + 1)) ^ 2 * (θstar ↑i) ^ 2 :=
    fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hSummable : Summable (fun j => (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar ↑j) ^ 2) :=
    summable_of_sum_range_le hnn hRange
  have hBound : ∑' j, (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar ↑j) ^ 2 ≤ Q :=
    tsum_le_of_sum_range_le hnn hRange


  have h_tail : Summable (fun j : ℕ => (θstar (j + 1)) ^ 2) := by
    have hsumshift : Summable (fun j =>
        (sobolevCoeff β (j + 1 + 1)) ^ 2 * (θstar (j + 1)) ^ 2) :=
      hSummable.comp_injective (fun a b h => by omega)
    exact Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => by
        nlinarith [sq_nonneg (θstar (j + 1)),
                   sobolev_weight_ge_one β hβ_pos (j + 1) (by omega)])
      hsumshift
  have hSqSum : Summable (fun j : ℕ => (θstar j) ^ 2) :=
    (summable_nat_add_iff 1).mp h_tail

  show L2normSq _ ≤ _
  simp only [L2normSq]
  have hAbsSum : Summable θstar := by
    exact summable_of_sobolev hβ θstar ⟨hSummable, hBound⟩
  rw [parseval_truncation_L2_error θstar M hSqSum hAbsSum]


  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hMinv_pos : (0 : ℝ) < (M : ℝ) ^ (-(2 * β)) := rpow_pos_of_pos hM_pos _

  have h_term : ∀ (j : ↑(Set.Ici M)),
      (θstar ↑j) ^ 2 ≤ (M : ℝ) ^ (-(2 * β)) *
        ((sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θstar ↑j) ^ 2) := by
    intro ⟨j, hj⟩
    simp only [Set.mem_Ici] at hj
    suffices h1 : 1 ≤ (M : ℝ) ^ (-(2 * β)) *
        (sobolevCoeff β (j + 1)) ^ 2 by
      nlinarith [sq_nonneg (θstar j)]
    rw [rpow_neg hM_pos.le, inv_mul_eq_div,
        le_div_iff₀ (rpow_pos_of_pos hM_pos _)]
    simp only [one_mul]
    exact sobolev_weight_ge_rpow β hβ_pos M j hj
  calc ∑' (j : ↑(Set.Ici M)), (θstar ↑j) ^ 2
      _ ≤ ∑' (j : ↑(Set.Ici M)), (M : ℝ) ^ (-(2 * β)) *
          ((sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θstar ↑j) ^ 2) :=
        Summable.tsum_le_tsum h_term (hSqSum.subtype _)
          ((Summable.mul_left _ hSummable).subtype _)
      _ = (M : ℝ) ^ (-(2 * β)) *
          ∑' (j : ↑(Set.Ici M)),
            ((sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θstar ↑j) ^ 2) :=
        tsum_mul_left
      _ ≤ (M : ℝ) ^ (-(2 * β)) *
          ∑' j : ℕ, (sobolevCoeff β (j + 1)) ^ 2 * (θstar j) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hMinv_pos.le
        exact Summable.tsum_subtype_le _ _
          (fun j => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hSummable
      _ ≤ (M : ℝ) ^ (-(2 * β)) * Q :=
        mul_le_mul_of_nonneg_left hBound hMinv_pos.le
      _ = Q * (M : ℝ) ^ (-(2 * β)) := mul_comm ..


/-- Square integrability of the approximation error: under mild regularity of `f`, the
squared difference between the truncated Fourier sum and `f` is integrable on `[0,1]`. -/
theorem approx_error_integrableOn
    (M : ℕ) (_hM : 0 < M)
    (β Q : ℝ) (_hβ : 0 < β) (_hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (_hθstar : ∀ j, θstar j = fourierCoeff f j)
    (_hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (hf_meas : Measurable f)
    (hf_sq_int : IntegrableOn (fun x => f x ^ 2) (Set.Icc 0 1)) :
    IntegrableOn (fun x =>
      ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) - f x) ^ 2)
      (Set.Icc 0 1) := by

  have continuous_trigBasis : ∀ j : ℕ, Continuous (trigBasis j) := by
    intro j; unfold trigBasis; split_ifs <;> fun_prop
  have hsum_cont : Continuous (fun x =>
      ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) :=
    continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_trigBasis _))
  have hdiff_meas : Measurable (fun x =>
      (∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) - f x) :=
    hsum_cont.measurable.sub hf_meas
  have hbound : ∀ x : ℝ,
      ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) - f x) ^ 2 ≤
      2 * ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ^ 2 + f x ^ 2) := by
    intro x; nlinarith [sq_nonneg ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) + f x)]
  have hsum_sq_int : IntegrableOn (fun x =>
      (∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ^ 2) (Set.Icc 0 1) :=
    (hsum_cont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hbnd_int : IntegrableOn (fun x =>
      2 * ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ^ 2 + f x ^ 2))
      (Set.Icc 0 1) := (hsum_sq_int.add hf_sq_int).const_mul 2
  exact Integrable.mono' hbnd_int
    ((hdiff_meas.pow_const 2).aestronglyMeasurable.restrict)
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound x))

/-- Triangle-like inequality for the squared `L²`-norm: `‖g+h‖² ≤ 2(‖g‖² + ‖h‖²)`. -/
lemma L2normSq_add_le (g h : ℝ → ℝ)
    (hg : IntegrableOn (fun x => g x ^ 2) (Set.Icc 0 1))
    (hh : IntegrableOn (fun x => h x ^ 2) (Set.Icc 0 1)) :
    L2normSq (fun x => g x + h x) ≤ 2 * (L2normSq g + L2normSq h) := by
  unfold L2normSq; simp only
  have key : ∀ x : ℝ, (g x + h x) ^ 2 ≤ 2 * (g x ^ 2 + h x ^ 2) := by
    intro x; nlinarith [sq_nonneg (g x - h x)]
  have hgh_int : IntegrableOn (fun x => g x ^ 2 + h x ^ 2) (Set.Icc 0 1) := hg.add hh
  have step1 : ∫ x in Set.Icc (0:ℝ) 1, (g x + h x) ^ 2 ≤
      ∫ x in Set.Icc (0:ℝ) 1, 2 * (g x ^ 2 + h x ^ 2) := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun x => sq_nonneg (g x + h x))
    · exact hgh_int.const_mul 2
    · exact ae_of_all _ key
  have step2a : ∫ x in Set.Icc (0:ℝ) 1, 2 * (g x ^ 2 + h x ^ 2) =
      2 * (∫ x in Set.Icc (0:ℝ) 1, (g x ^ 2 + h x ^ 2)) := by
    rw [show (fun x => 2 * (g x ^ 2 + h x ^ 2)) = (fun x => (2 : ℝ) • (g x ^ 2 + h x ^ 2))
      from by ext x; simp [mul_comm]]
    rw [integral_smul (2 : ℝ)]
    simp [smul_eq_mul]
  have step2b : (∫ x in Set.Icc (0:ℝ) 1, (g x ^ 2 + h x ^ 2)) =
      (∫ x in Set.Icc (0:ℝ) 1, g x ^ 2) + (∫ x in Set.Icc (0:ℝ) 1, h x ^ 2) :=
    integral_add hg hh
  linarith


/-- Rate computation: for `β ≥ (1+√5)/4` and the optimal choice `M ≈ n^{1/(2β+1)}`,
the upper bound `M^{-2β} + n^{1-2β} + (M + σ² log(1/δ))/n` simplifies to the
minimax rate `n^{-2β/(2β+1)} + σ² log(1/δ)/n` up to constants. -/
lemma thm_3_15_rate_computation
    (n : ℕ) (hn : 0 < n)
    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (M : ℕ) (_hM_pos : 0 < M)
    (hM_choice : (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) ≤ (M : ℝ) ∧
                 (M : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) + 1)
    (σ : ℝ) (_hσ : 0 < σ) :
    ∃ (C' : ℝ), 0 < C' ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    (M : ℝ) ^ (-(2 * β)) + (n : ℝ) ^ (1 - 2 * β) +
      ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ) ≤
    C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
    C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := by

  refine ⟨4, by norm_num, ?_⟩
  intro δ hδ_pos hδ_le
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2β1_pos : (0 : ℝ) < 2 * β + 1 := by linarith
  have hMn_lb := hM_choice.1
  have hMn_ub := hM_choice.2
  set rate := (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) with rate_def
  set tail := σ ^ 2 * Real.log (1 / δ) / (n : ℝ) with tail_def

  have h1 : (M : ℝ) ^ (-(2 * β)) ≤ rate := by
    have hn1 : 0 < (n : ℝ) ^ ((1:ℝ) / (2*β+1)) := rpow_pos_of_pos hn_pos _
    calc (M : ℝ) ^ (-(2*β))
        ≤ ((n : ℝ) ^ ((1:ℝ) / (2*β+1))) ^ (-(2*β)) :=
          rpow_le_rpow_of_nonpos hn1 hMn_lb (by linarith)
      _ = rate := by rw [rate_def, ← rpow_mul hn_pos.le]; ring_nf


  have h2 : (n : ℝ) ^ (1 - 2 * β) ≤ rate := by
    rw [rate_def]
    apply rpow_le_rpow_of_exponent_le hn_ge1
    rw [le_div_iff₀ h2β1_pos]
    have h4β : 4 * β - 1 ≥ Real.sqrt 5 := by linarith
    have h4βsq : (4 * β - 1) ^ 2 ≥ (Real.sqrt 5) ^ 2 :=
      sq_le_sq' (by linarith [Real.sqrt_nonneg 5]) h4β
    rw [Real.sq_sqrt (show (5:ℝ) ≥ 0 by norm_num)] at h4βsq
    nlinarith [h4βsq]


  have h3 : (M : ℝ) / (n : ℝ) ≤ 2 * rate := by
    have step1 : (M : ℝ) / (n : ℝ) ≤ ((n : ℝ) ^ ((1:ℝ) / (2*β+1)) + 1) / (n : ℝ) :=
      div_le_div_of_nonneg_right hMn_ub hn_pos.le
    rw [add_div] at step1
    have key1 : (n : ℝ) ^ ((1:ℝ) / (2*β+1)) / (n : ℝ) = rate := by
      rw [rate_def, div_eq_mul_inv, ← rpow_neg_one (n : ℝ), ← rpow_add hn_pos]
      congr 1; field_simp; ring
    have key2 : 1 / (n : ℝ) ≤ rate := by
      rw [one_div, ← rpow_neg_one (n : ℝ), rate_def]
      apply rpow_le_rpow_of_exponent_le hn_ge1
      rw [neg_div, neg_le_neg_iff, div_le_one h2β1_pos]
      linarith
    linarith [step1, key1, key2]

  have hsplit : ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ) =
      (M : ℝ) / (n : ℝ) + tail := by rw [tail_def, add_div]
  rw [hsplit]
  have htail_nn : 0 ≤ tail := by
    rw [tail_def]
    exact div_nonneg (mul_nonneg (sq_nonneg σ)
      (Real.log_nonneg (by rw [le_div_iff₀ hδ_pos]; linarith))) hn_pos.le
  have hrhs : 4 * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
      4 * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) = 4 * rate + 4 * tail := by
    rw [rate_def, tail_def]; ring
  rw [hrhs]
  linarith


/-- Converting an exponential tail bound into an expectation bound: if
`P(X ≤ A + B log(1/δ)) ≥ 1 - δ` for all `δ ∈ (0,1]`, then `E[X] ≤ A + B`. -/
theorem expectation_from_exponential_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_meas : Measurable X) (_hX_nn : ∀ ω, 0 ≤ X ω)
    {A B : ℝ} (_hA : 0 ≤ A) (hB : 0 < B)
    (htail : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      μ {ω | X ω ≤ A + B * Real.log (1 / δ)} ≥ ENNReal.ofReal (1 - δ)) :
    ∫ ω, X ω ∂μ ≤ A + B := by
  by_cases hInt : Integrable X μ
  ·
    have step1 : ∫ ω, X ω ∂μ = ∫ ω, (X ω - A) ∂μ + A := by
      rw [integral_sub hInt (integrable_const A), integral_const]
      simp [Measure.real, measure_univ]
    rw [step1]
    suffices h : ∫ ω, (X ω - A) ∂μ ≤ B by linarith

    have hIntXA : Integrable (fun ω => X ω - A) μ := hInt.sub (integrable_const A)
    have hIntMax : Integrable (fun ω => max (X ω - A) 0) μ := hIntXA.pos_part

    have hMeasMax : AEStronglyMeasurable (fun ω => max (X ω - A) 0) μ :=
      ((hX_meas.sub measurable_const).max measurable_const).aestronglyMeasurable

    have hlint : ∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ ≤ ENNReal.ofReal B := by
      rw [lintegral_eq_lintegral_meas_lt μ
        (by filter_upwards with ω; exact le_max_right _ _)
        ((hX_meas.sub measurable_const).max measurable_const).aemeasurable]
      calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < max (X a - A) 0}
          ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, ENNReal.ofReal (Real.exp ((-1/B) * t)) := by
            apply lintegral_mono_ae
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
            simp only [Set.mem_Ioi] at ht
            have hset : {a | t < max (X a - A) 0} = {a | A + t < X a} := by
              ext a; simp only [Set.mem_setOf_eq, max_def]; split_ifs with h
              · constructor; intro h2; linarith; intro h2; linarith
              · push Not at h; constructor; intro h2; linarith; intro h2; linarith
            rw [hset]

            set δ := Real.exp ((-1/B) * t)
            have hδ_pos : 0 < δ := exp_pos _
            have hδ_le : δ ≤ 1 := exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg
                (div_nonpos_of_nonpos_of_nonneg (by norm_num) hB.le) ht.le)
            have hTail' := htail δ hδ_pos hδ_le
            have key : A + B * Real.log (1 / δ) = A + t := by
              congr 1; rw [one_div, Real.log_inv, Real.log_exp]; field_simp
            rw [key] at hTail'
            have hms : MeasurableSet {ω | X ω ≤ A + t} := hX_meas measurableSet_Iic
            rw [show {a | A + t < X a} = {ω | X ω ≤ A + t}ᶜ from by
              ext ω; simp [not_le]]
            rw [measure_compl hms (measure_ne_top μ _), measure_univ]
            calc (1 : ENNReal) - μ {ω | X ω ≤ A + t}
                ≤ 1 - ENNReal.ofReal (1 - δ) := tsub_le_tsub_left hTail' _
              _ = ENNReal.ofReal δ := by
                  rw [show (1:ENNReal) = ENNReal.ofReal 1 from by simp]
                  rw [← ENNReal.ofReal_sub 1 (by linarith)]
                  congr 1; ring
        _ = ENNReal.ofReal B := by
            rw [← ofReal_integral_eq_lintegral_ofReal
              (integrableOn_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB) 0)
              (by filter_upwards with t; exact (exp_pos _).le)]
            congr 1
            rw [integral_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB)]
            simp [mul_zero, exp_zero]

    calc ∫ ω, (X ω - A) ∂μ
        ≤ ∫ ω, max (X ω - A) 0 ∂μ := by
          exact integral_mono_ae hIntXA hIntMax
            (by filter_upwards with ω; exact le_max_left _ _)
      _ = (∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ).toReal := by
          exact integral_eq_lintegral_of_nonneg_ae
            (by filter_upwards with ω; exact le_max_right _ _) hMeasMax
      _ ≤ B := by
          rw [← ENNReal.toReal_ofReal hB.le]
          exact ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hlint
  · rw [integral_undef hInt]; linarith




end Chapter3
