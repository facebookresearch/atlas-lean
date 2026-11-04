/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter3.Remark_3_1
import Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_15
import Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_14
import Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_4
import Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_5
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6

set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Real MeasureTheory

namespace Chapter3

/-- `θhat` is a BIC estimator for the trigonometric model with penalty parameter `τ²`:
for every `ω` it minimizes empirical squared error plus `τ²` times the support size
of the coefficient vector. -/
def IsBICEstimatorTrig {Ω : Type*} {n : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ) (τsq : ℝ) : Prop :=
  ∀ ω θ,
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ))) ^ 2 +
      τsq * ↑((Finset.univ.filter (fun j => θhat ω j ≠ 0)).card) ≤
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ))) ^ 2 +
      τsq * ↑((Finset.univ.filter (fun j => θ j ≠ 0)).card)

/-- `θhat` is a Lasso estimator for the trigonometric model with regularization parameter
`τ`: for every `ω` it minimizes empirical squared error plus `2τ` times the `ℓ¹` norm of
the coefficient vector. -/
def IsLassoEstimatorTrig {Ω : Type*} {n : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ) (τ : ℝ) : Prop :=
  ∀ ω θ,
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ))) ^ 2 +
      2 * τ * ∑ j : Fin (n - 1), |θhat ω j| ≤
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ))) ^ 2 +
      2 * τ * ∑ j : Fin (n - 1), |θ j|

/-- `θhat` is either a BIC or Lasso estimator with some positive tuning parameter. -/
def IsBICOrLassoEstimator {Ω : Type*} {n : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ) : Prop :=
  (∃ τsq : ℝ, 0 < τsq ∧ IsBICEstimatorTrig Y θhat τsq) ∨
  (∃ τ : ℝ, 0 < τ ∧ IsLassoEstimatorTrig Y θhat τ)

/-- Reformulating BIC optimality in matrix form via the trigonometric design matrix. -/
lemma IsBICEstimatorTrig_to_matrix_optimality
    {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ)
    (τsq : ℝ)
    (hBIC : IsBICEstimatorTrig Y θhat τsq) :
    let Φ := trigDesignMatrix n (n - 1)
    ∀ ω θ,
      (1 / (n : ℝ)) * ∑ i : Fin n, (Y ω i - (Φ.mulVec (θhat ω)) i) ^ 2 +
        τsq * ↑((Finset.univ.filter (fun j => θhat ω j ≠ 0)).card) ≤
      (1 / (n : ℝ)) * ∑ i : Fin n, (Y ω i - (Φ.mulVec θ) i) ^ 2 +
        τsq * ↑((Finset.univ.filter (fun j => θ j ≠ 0)).card) := by
  intro Φ ω θ
  have h := hBIC ω θ

  have h_eq_hat : ∀ i : Fin n,
      trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ)) =
      (trigDesignMatrix n (n - 1)).mulVec (θhat ω) i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn (θhat ω) i
  have h_eq_θ : ∀ i : Fin n,
      trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ)) =
      (trigDesignMatrix n (n - 1)).mulVec θ i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn θ i
  simp_rw [h_eq_hat, h_eq_θ] at h
  exact h

/-- Reformulating Lasso optimality in matrix form via the trigonometric design matrix. -/
lemma IsLassoEstimatorTrig_to_matrix_optimality
    {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ)
    (τ : ℝ)
    (hLasso : IsLassoEstimatorTrig Y θhat τ) :
    let Φ := trigDesignMatrix n (n - 1)
    ∀ ω θ,
      (1 / (n : ℝ)) * ∑ i : Fin n, (Y ω i - (Φ.mulVec (θhat ω)) i) ^ 2 +
        2 * τ * ∑ j : Fin (n - 1), |θhat ω j| ≤
      (1 / (n : ℝ)) * ∑ i : Fin n, (Y ω i - (Φ.mulVec θ) i) ^ 2 +
        2 * τ * ∑ j : Fin (n - 1), |θ j| := by
  intro Φ ω θ
  have h := hLasso ω θ
  have h_eq_hat : ∀ i : Fin n,
      trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ)) =
      (trigDesignMatrix n (n - 1)).mulVec (θhat ω) i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn (θhat ω) i
  have h_eq_θ : ∀ i : Fin n,
      trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ)) =
      (trigDesignMatrix n (n - 1)).mulVec θ i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn θ i
  simp_rw [h_eq_hat, h_eq_θ] at h
  exact h

/-- Expansion of `∫ (a - b)² dx` as `∫ a² dx + ∫ b² dx - 2 ∫ a b dx`. -/
theorem integral_split_sq_sub
    (a : ℝ → ℝ) (b : ℝ → ℝ)
    (ha : Integrable (fun x => a x ^ 2) (volume.restrict (Set.Icc 0 1)))
    (hb : Integrable (fun x => b x ^ 2) (volume.restrict (Set.Icc 0 1)))
    (hab : Integrable (fun x => a x * b x) (volume.restrict (Set.Icc 0 1))) :
    ∫ x in Set.Icc (0 : ℝ) 1,
      (a x ^ 2 - 2 * a x * b x + b x ^ 2) =
    (∫ x in Set.Icc (0 : ℝ) 1, a x ^ 2) +
    (∫ x in Set.Icc (0 : ℝ) 1, b x ^ 2) -
    2 * (∫ x in Set.Icc (0 : ℝ) 1, a x * b x) := by
  have hab2 : Integrable (fun x => (-2) * (a x * b x)) (volume.restrict (Set.Icc 0 1)) :=
    hab.const_mul (-2)
  have hab' : Integrable (fun x => a x ^ 2 + b x ^ 2) (volume.restrict (Set.Icc 0 1)) :=
    ha.add hb
  have heq : ∀ x, a x ^ 2 - 2 * a x * b x + b x ^ 2 =
    (a x ^ 2 + b x ^ 2) + (-2) * (a x * b x) := by intro x; ring
  simp_rw [heq]
  rw [integral_add hab' hab2]
  rw [integral_add ha hb]
  rw [integral_const_mul]
  ring

/-- A trigonometric linear combination is a continuous function of `x`. -/
lemma trigLinComb_continuous (N : ℕ) (θ : Fin N → ℝ) : Continuous (fun x => trigLinComb N θ x) := by
  unfold trigLinComb
  apply continuous_finset_sum
  intro j _
  exact continuous_const.mul (trigBasis_continuous (j.val + 1))

/-- The squared difference between a trigonometric linear combination and a continuous
function `f` is integrable on `[0,1]`. -/
lemma integrableOn_sq_trigLinComb_sub_f
    {N : ℕ} (f : ℝ → ℝ) (θ : Fin N → ℝ)
    (_hθ : ∀ j : Fin N, θ j = fourierCoeff f (j.val + 1))
    (hf_cont : Continuous f) :
    Integrable (fun x => (trigLinComb N θ x - f x) ^ 2)
      (volume.restrict (Set.Icc 0 1)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact (((trigLinComb_continuous N θ).sub hf_cont).pow 2).continuousOn

/-- The product `(φ_θ_full - f) · φ_θ_tail` is integrable on `[0,1]` for continuous `f`. -/
lemma integrableOn_trigLinComb_sub_f_mul_trigLinComb
    {N : ℕ} (f : ℝ → ℝ) (θ_full θ_tail : Fin N → ℝ)
    (_hθ : ∀ j : Fin N, θ_full j = fourierCoeff f (j.val + 1))
    (hf_cont : Continuous f) :
    Integrable (fun x => (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x)
      (volume.restrict (Set.Icc 0 1)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact (((trigLinComb_continuous N θ_full).sub hf_cont).mul
    (trigLinComb_continuous N θ_tail)).continuousOn

/-- Orthogonality of cross terms: if `θ_full_j = ⟨f, φ_{j+1}⟩` are the Fourier coefficients,
then `∫₀¹ (φ_{θ_full} - f) · φ_{θ_tail} dx = 0` for any `θ_tail`. -/
theorem L2_cross_term_orthogonal
    {N : ℕ} (f : ℝ → ℝ)
    (θ_full : Fin N → ℝ)
    (θ_tail : Fin N → ℝ)
    (hθ : ∀ j : Fin N, θ_full j = fourierCoeff f (j.val + 1))
    (hf_cont : Continuous f) :
    ∫ x in Set.Icc (0 : ℝ) 1,
      (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x = 0 := by

  simp only [trigLinComb]


  have h_inner_zero : ∀ j' : Fin N,
      ∫ x in Set.Icc (0 : ℝ) 1,
        ((∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) - f x) *
        trigBasis (↑j' + 1) x = 0 := by
    intro j'

    have hj'_pos : 0 < (↑j' : ℕ) + 1 := Nat.succ_pos _

    have hA : ∫ x in Set.Icc (0 : ℝ) 1,
        (∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) * trigBasis (↑j' + 1) x =
        θ_full j' := by

      simp_rw [Finset.sum_mul]
      rw [integral_finset_sum Finset.univ (fun j _ => by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply ContinuousOn.mul
        · exact (continuous_const.mul (trigBasis_continuous _)).continuousOn
        · exact (trigBasis_continuous _).continuousOn)]


      simp_rw [mul_assoc, integral_const_mul]

      simp_rw [trigBasis_L2_orthonormal _ _ (Nat.succ_pos _) hj'_pos]

      simp only [mul_ite, mul_one, mul_zero]

      simp only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff, Fin.val_inj]
      rw [Finset.sum_ite_eq' Finset.univ j' (fun j => θ_full j)]
      simp [Finset.mem_univ]


    have hB : ∫ x in Set.Icc (0 : ℝ) 1, f x * trigBasis (↑j' + 1) x =
        θ_full j' := by
      rw [hθ j']
      rfl

    have h_eq : ∀ x, ((∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) - f x) *
        trigBasis (↑j' + 1) x =
        (∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) * trigBasis (↑j' + 1) x -
        f x * trigBasis (↑j' + 1) x := by
      intro x; ring
    simp_rw [h_eq]

    rw [integral_sub
      (by apply ContinuousOn.integrableOn_compact isCompact_Icc
          apply ContinuousOn.mul
          · apply continuousOn_finset_sum; intro j _
            exact (continuous_const.mul (trigBasis_continuous _)).continuousOn
          · exact (trigBasis_continuous _).continuousOn)
      (by apply ContinuousOn.integrableOn_compact isCompact_Icc
          exact (hf_cont.mul (trigBasis_continuous _)).continuousOn)]
    linarith [hA, hB]


  have h_prod_sum : ∀ x : ℝ,
      (∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x - f x) *
      (∑ j : Fin N, θ_tail j * trigBasis (↑j + 1) x) =
      ∑ j' : Fin N, θ_tail j' *
        ((∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x - f x) * trigBasis (↑j' + 1) x) := by
    intro x
    simp_rw [Finset.mul_sum, mul_comm (θ_tail _) _, ← mul_assoc]
  simp_rw [h_prod_sum]
  rw [integral_finset_sum Finset.univ (fun j' _ => by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply ContinuousOn.mul
    · exact continuousOn_const
    · apply ContinuousOn.mul
      · apply ContinuousOn.sub
        · apply continuousOn_finset_sum; intro j _
          exact (continuous_const.mul (trigBasis_continuous _)).continuousOn
        · exact hf_cont.continuousOn
      · exact (trigBasis_continuous _).continuousOn)]
  simp_rw [integral_const_mul, h_inner_zero, mul_zero, Finset.sum_const_zero]

/-- Pythagorean decomposition for truncated Fourier expansions: the squared `L²` distance
between `f` and its Fourier truncation `(θstar_j)_{j<M}` decomposes as the sum of the squared
truncated coefficients (the aliasing/tail term) plus the residual `L²` error from the
full Fourier expansion. -/
theorem L2normSq_truncation_Pythagorean
    {n : ℕ} (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (_hθstar : ∀ j, θstar j = fourierCoeff f j)
    (M : ℕ) (_hM_le : M ≤ n - 1)
    (hf_cont : Continuous f) :
    L2normSq (fun x => trigLinComb (n - 1)
      (fun j : Fin (n - 1) => if (j : ℕ) < M then θstar (j.val + 1) else 0) x - f x) =
      (((Finset.univ : Finset (Fin (n - 1))).filter (fun j : Fin (n - 1) => ¬ (j : ℕ) < M)).sum
        (fun j : Fin (n - 1) => (θstar (j.val + 1)) ^ 2)) +
      L2normSq (fun x => trigLinComb (n - 1)
        (fun j : Fin (n - 1) => θstar (j.val + 1)) x - f x) := by

  set N := n - 1
  set θ_full : Fin N → ℝ := fun j => θstar (j.val + 1)
  set θ_tail : Fin N → ℝ := fun j => if (j : ℕ) < M then 0 else θstar (j.val + 1)
  set θ_trunc : Fin N → ℝ := fun j => if (j : ℕ) < M then θstar (j.val + 1) else 0

  have h_split : ∀ j : Fin N, θ_trunc j = θ_full j - θ_tail j := by
    intro j; simp only [θ_trunc, θ_full, θ_tail]; split_ifs <;> ring
  have h_fn : ∀ x, trigLinComb N θ_trunc x - f x =
      (trigLinComb N θ_full x - f x) - trigLinComb N θ_tail x := by
    intro x; simp only [trigLinComb]
    have : ∑ j : Fin N, θ_trunc j * trigBasis (j.val + 1) x =
        (∑ j : Fin N, θ_full j * trigBasis (j.val + 1) x) -
        ∑ j : Fin N, θ_tail j * trigBasis (j.val + 1) x := by
      rw [← Finset.sum_sub_distrib]
      congr 1; ext j; rw [h_split]; ring
    linarith [this]

  conv_lhs => rw [show (fun x => trigLinComb N θ_trunc x - f x) =
    (fun x => (trigLinComb N θ_full x - f x) - trigLinComb N θ_tail x) from funext h_fn]


  unfold L2normSq

  have h_expand : ∀ x, ((trigLinComb N θ_full x - f x) - trigLinComb N θ_tail x) ^ 2 =
      (trigLinComb N θ_full x - f x) ^ 2 - 2 * (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x +
      (trigLinComb N θ_tail x) ^ 2 := by
    intro x; ring
  simp_rw [h_expand]

  have hθ_fourier : ∀ j : Fin N, θ_full j = fourierCoeff f (j.val + 1) := by
    intro j; simp [θ_full]; exact _hθstar (j.val + 1)

  have h_int_sq_sub : Integrable (fun x => (trigLinComb N θ_full x - f x) ^ 2)
      (volume.restrict (Set.Icc 0 1)) :=
    integrableOn_sq_trigLinComb_sub_f f θ_full hθ_fourier hf_cont
  have h_int_sq_tail : Integrable (fun x => (trigLinComb N θ_tail x) ^ 2)
      (volume.restrict (Set.Icc 0 1)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (Continuous.pow (trigLinComb_continuous N θ_tail) 2).continuousOn
  have h_int_cross : Integrable (fun x => (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x)
      (volume.restrict (Set.Icc 0 1)) :=
    integrableOn_trigLinComb_sub_f_mul_trigLinComb f θ_full θ_tail hθ_fourier hf_cont

  rw [show ∫ x in Set.Icc (0 : ℝ) 1,
      (trigLinComb N θ_full x - f x) ^ 2 -
      2 * (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x +
      (trigLinComb N θ_tail x) ^ 2 =
    (∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_full x - f x) ^ 2) +
    (∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_tail x) ^ 2) -
    2 * (∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x)
    from integral_split_sq_sub _ _ h_int_sq_sub h_int_sq_tail h_int_cross]
  have h_cross : ∫ x in Set.Icc (0 : ℝ) 1,
      (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x = 0 :=
    L2_cross_term_orthogonal f θ_full θ_tail hθ_fourier hf_cont
  rw [h_cross, mul_zero, sub_zero]

  have h_tail_sq : ∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_tail x) ^ 2 =
      (Finset.univ.filter (fun j : Fin N => ¬(j : ℕ) < M)).sum
        (fun j : Fin N => (θstar (j.val + 1)) ^ 2) := by


    have := L2_norm_eq_sum_sq N θ_tail
    unfold L2normSq at this
    rw [show (fun x => ∑ j : Fin N, θ_tail j * trigBasis (↑j + 1) x) =
        (fun x => trigLinComb N θ_tail x) from by ext x; simp [trigLinComb]] at this
    rw [this]


    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin N => (j : ℕ) < M)]
    simp only [not_lt]
    have h_zero : (Finset.univ.filter (fun j : Fin N => (j : ℕ) < M)).sum
        (fun j => θ_tail j ^ 2) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp [θ_tail, if_pos hj]
    rw [h_zero, zero_add]
    apply Finset.sum_congr
    · ext j; simp
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp [θ_tail, if_neg (not_lt.mpr hj)]
  rw [h_tail_sq]; ring

/-- Tail bound for Fourier coefficients of a Sobolev-class function summed beyond index
`n-1`: `∑_{j ≥ n-1} θstar_j² ≤ Q · (n-1)^{-2β}`. -/
theorem aliasing_tail_L2_bound
    (β : ℝ) (hβ_pos : 0 < β)
    (Q : ℝ) (hQ : 0 < Q)
    (θstar : ℕ → ℝ)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    {n : ℕ} (hn : 2 ≤ n) :
    ∀ (K : ℕ), ∑ j ∈ Finset.Ico (n - 1) K, (θstar j) ^ 2 ≤
      Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) := by
  intro K
  by_cases hK : n - 1 ≤ K
  ·
    have hM_pos : 0 < (n - 1 : ℕ) := by omega
    have hM_real_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hM_pos

    have hterm : ∀ j ∈ Finset.Ico (n - 1) K,
        (θstar ↑j) ^ 2 ≤ ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) *
          ((sobolevCoeff β (↑j + 1)) ^ 2 * (θstar ↑j) ^ 2) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      have hMj : (n - 1 : ℕ) ≤ j := hj.1
      have hw := sobolev_weight_ge_rpow β hβ_pos (n - 1) j hMj

      by_cases hθ : θstar j = 0
      · simp [hθ]
      · have hMpow_pos : 0 < ((n - 1 : ℕ) : ℝ) ^ (2 * β) := rpow_pos_of_pos hM_real_pos _
        rw [rpow_neg hM_real_pos.le, ← div_eq_inv_mul]
        rw [le_div_iff₀ hMpow_pos]
        nlinarith [sq_nonneg (θstar j)]

    calc ∑ j ∈ Finset.Ico (n - 1) K, (θstar j) ^ 2
        ≤ ∑ j ∈ Finset.Ico (n - 1) K, ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) *
            ((sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2) :=
          Finset.sum_le_sum hterm
      _ = ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) *
            ∑ j ∈ Finset.Ico (n - 1) K, (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2 := by
          rw [← Finset.mul_sum]
      _ ≤ ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) * Q := by
          gcongr


          have hSobK := hSobolev K
          calc ∑ j ∈ Finset.Ico (n - 1) K,
                  (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2
              ≤ ∑ j ∈ Finset.range K,
                  (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2 := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro x hx
                  simp only [Finset.mem_Ico] at hx
                  simp only [Finset.mem_range]
                  exact hx.2
                · intros i _ _; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
            _ = ∑ j : Fin K, (sobolevCoeff β (↑j.val + 1)) ^ 2 * (θstar j.val) ^ 2 := by
                simp only [← Fin.sum_univ_eq_sum_range]
            _ ≤ Q := hSobK

      _ = Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) := by ring

  ·
    push Not at hK

    have : Finset.Ico (n - 1) K = ∅ := Finset.Ico_eq_empty (by omega)
    simp [this]
    apply mul_nonneg
    · linarith
    · apply rpow_nonneg
      exact Nat.cast_nonneg _




/-- Bound on the truncated tail of squared Fourier coefficients: for a Sobolev-class
function, `∑_{M ≤ j < n-1} θstar_{j+1}² ≤ Q · M^{-2β}`. -/
theorem coeff_tail_sq_sum_le_rpow
    (β : ℝ) (hβ_pos : 0 < β)
    (Q : ℝ) (_hQ : 0 < Q)
    (θstar : ℕ → ℝ)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    {n : ℕ} (_hn : 2 ≤ n)
    (M : ℕ) (hM_pos : 0 < M) (_hM_le : M ≤ n - 1) :
    (((Finset.univ : Finset (Fin (n - 1))).filter (fun j : Fin (n - 1) => ¬ (j : ℕ) < M)).sum
      (fun j : Fin (n - 1) => (θstar (j.val + 1)) ^ 2)) ≤
      Q * (M : ℝ) ^ (-(2 * β)) := by


  have hM_real_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos

  have hterm : ∀ j : Fin (n - 1), ¬(j : ℕ) < M →
      (θstar (j.val + 1)) ^ 2 ≤
      (M : ℝ) ^ (-(2 * β)) * ((sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2) := by
    intro j hj
    push Not at hj

    have hw := sobolev_weight_ge_rpow β hβ_pos M (j.val + 1) (by omega)

    by_cases hθ : θstar (j.val + 1) = 0
    · simp [hθ]
    · have hMpow_pos : 0 < (M : ℝ) ^ (2 * β) := rpow_pos_of_pos hM_real_pos _
      rw [rpow_neg hM_real_pos.le, ← div_eq_inv_mul]
      rw [le_div_iff₀ hMpow_pos]
      nlinarith [sq_nonneg (θstar (j.val + 1))]


  have hShiftedSum : ((Finset.univ : Finset (Fin (n - 1))).sum
      (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2)) ≤ Q := by


    let g := fun k : ℕ => (sobolevCoeff β (k + 1)) ^ 2 * (θstar k) ^ 2
    have hg_nn : ∀ k, 0 ≤ g k := fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    show (Finset.univ : Finset (Fin (n - 1))).sum
        (fun j : Fin (n - 1) => g (j.val + 1)) ≤ Q
    have hSobN : (Finset.univ : Finset (Fin n)).sum (fun j : Fin n => g j.val) ≤ Q :=
      hSobolev n

    rw [Fin.sum_univ_eq_sum_range] at hSobN


    have hconv : (Finset.univ : Finset (Fin (n - 1))).sum (fun j => g (↑j + 1)) =
        ∑ i ∈ Finset.range (n - 1), g (i + 1) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => g (i + 1))]
    rw [hconv]
    have hn_eq : n = (n - 1) + 1 := by omega
    rw [hn_eq] at hSobN
    rw [Finset.sum_range_succ'] at hSobN
    linarith [hg_nn 0]
  calc (((Finset.univ : Finset (Fin (n - 1))).filter
        (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
        (fun j : Fin (n - 1) => (θstar (j.val + 1)) ^ 2))
      ≤ (((Finset.univ : Finset (Fin (n - 1))).filter
        (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
        (fun j : Fin (n - 1) => (M : ℝ) ^ (-(2 * β)) *
          ((sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2))) := by
        apply Finset.sum_le_sum
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hterm j hj
    _ = (M : ℝ) ^ (-(2 * β)) *
        (((Finset.univ : Finset (Fin (n - 1))).filter
          (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
          (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2)) := by
        rw [← Finset.mul_sum]
    _ ≤ (M : ℝ) ^ (-(2 * β)) * Q := by
        gcongr
        calc (((Finset.univ : Finset (Fin (n - 1))).filter
              (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
              (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2))
            ≤ ((Finset.univ : Finset (Fin (n - 1))).sum
              (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2)) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.filter_subset _ _
              · intros i _ _
                exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
          _ ≤ Q := hShiftedSum
    _ = Q * (M : ℝ) ^ (-(2 * β)) := by ring


open Matrix in
/-- The trigonometric linear combination at grid point `i/n` equals the `i`-th entry of
`(trigDesignMatrix n M).mulVec θ`. -/
lemma trigLinComb_eq_mulVec_apply (n M : ℕ) (hn : 0 < n) (θ : Fin M → ℝ) (i : Fin n) :
    trigLinComb M θ ((i : ℝ) / (n : ℝ)) = (trigDesignMatrix n M).mulVec θ i := by
  simp only [trigLinComb, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [trigDesignMatrix_eq_trigBasis n M hn i j]
  ring

open Matrix in
/-- The empirical squared norm of `φ_θ - f` equals the mean squared error of
`trigDesignMatrix.mulVec θ` against the grid values of `f`. -/
lemma empiricalNormSq_eq_MSE_trigDesign (n : ℕ) (hn : 0 < n) (M : ℕ)
    (θ : Fin M → ℝ) (f : ℝ → ℝ) :
    empiricalNormSq n (fun x => trigLinComb M θ x - f x) =
    Rigollet.Chapter3.MSE_35 ((trigDesignMatrix n M).mulVec θ)
      (fun i => f ((i : ℝ) / (n : ℝ))) := by
  simp only [empiricalNormSq, Rigollet.Chapter3.MSE_35]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [trigLinComb_eq_mulVec_apply n M hn θ i]

/-- Column-norm bound for the trigonometric design matrix: each column has squared
ℓ²-norm at most `n`. -/
theorem trig_design_colnorm_bound
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ j : Fin (n - 1), ∑ i : Fin n, (trigDesignMatrix n (n - 1) i j) ^ 2 ≤ ↑n := by
  intro j

  have h313 := lemma_3_13 n (n - 1) (by omega) (le_refl _)

  have h := congr_fun (congr_fun h313 j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_one,
    ↓reduceIte] at h


  have key : ∀ i : Fin n, (trigDesignMatrix n (n - 1) i j) ^ 2 =
      trigDesignMatrix n (n - 1) i j * trigDesignMatrix n (n - 1) i j := by
    intro i; ring
  simp_rw [key]
  linarith

/-- A sub-Gaussian noise vector with variance proxy `σ²` yields the Rigollet-form
sub-Gaussian noise statement at the coordinate level. -/
lemma subGaussianNoiseVec_to_subGaussianNoise
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ε : Ω → Fin n → ℝ) (σ : ℝ) (μ : MeasureTheory.Measure Ω)
    (h : IsSubGaussianNoiseVec ε (σ ^ 2) μ) :
    Rigollet.Chapter3.IsSubGaussianNoise ε σ μ :=
  h.bound

/-- Each coordinate `ε ω i` is sub-Gaussian (in the full Mathlib sense, including
integrability and zero-mean) provided the noise vector has the corresponding properties. -/
theorem subGaussianNoiseVec_to_IsSubGaussian
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (ε : Ω → Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0) :
    ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ := by
  intro i
  exact ⟨hsubG.integ i, hZeroMean i, hsubG.exp_integ i, hsubG.bound i⟩






/-- Property ORT for the trigonometric basis: the empirical squared norm of `φ_θ` on the
uniform grid equals its `L²` squared norm. -/
theorem ORT_empirical_eq_L2
    {n : ℕ} (hn : 2 ≤ n)
    (M : ℕ) (hM : M ≤ n - 1)
    (θ : Fin M → ℝ) :
    empiricalNormSq n (fun x => trigLinComb M θ x) =
    L2normSq (fun x => trigLinComb M θ x) := by
  have hn_pos : 0 < n := by omega


  have hORT := ORT_L2_eq_empirical_normSq n M hn_pos hM θ

  unfold empiricalNormSq trigLinComb
  rw [← hORT]





/-- Integrating an exponential tail bound: if `P(X ≤ A + B log(1/δ)) ≥ 1 - δ` for all
`δ ∈ (0,1]`, then `E[X] ≤ A + B`. -/
theorem tail_integration_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hMeas : Measurable X)
    (A : ℝ) (hA_pos : 0 < A)
    (B : ℝ) (hB_pos : 0 < B)
    (hTail : ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
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
      ((hMeas.sub measurable_const).max measurable_const).aestronglyMeasurable

    have hlint : ∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ ≤ ENNReal.ofReal B := by
      rw [lintegral_eq_lintegral_meas_lt μ
        (by filter_upwards with ω; exact le_max_right _ _)
        ((hMeas.sub measurable_const).max measurable_const).aemeasurable]
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
                (div_nonpos_of_nonpos_of_nonneg (by norm_num) hB_pos.le) ht.le)
            have hTail' := hTail δ hδ_pos hδ_le
            have key : A + B * Real.log (1 / δ) = A + t := by
              congr 1; rw [one_div, Real.log_inv, Real.log_exp]; field_simp
            rw [key] at hTail'
            have hms : MeasurableSet {ω | X ω ≤ A + t} := hMeas measurableSet_Iic
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
              (integrableOn_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB_pos) 0)
              (by filter_upwards with t; exact (exp_pos _).le)]
            congr 1
            rw [integral_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB_pos)]
            simp [mul_zero, exp_zero]

    calc ∫ ω, (X ω - A) ∂μ
        ≤ ∫ ω, max (X ω - A) 0 ∂μ := by
          exact integral_mono_ae hIntXA hIntMax
            (by filter_upwards with ω; exact le_max_left _ _)
      _ = (∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ).toReal := by
          exact integral_eq_lintegral_of_nonneg_ae
            (by filter_upwards with ω; exact le_max_right _ _) hMeasMax
      _ ≤ B := by
          rw [← ENNReal.toReal_ofReal hB_pos.le]
          exact ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hlint
  · rw [integral_undef hInt]; linarith


/-- Rate computation for Corollary 3.16: the upper bound
`M^{-2β} + (n-1)^{-2β} + M log(n e)/n + σ² log(1/δ)/n` is dominated by
`C' n^{-2β/(2β+1)} + C' σ² log(1/δ)/n` (up to constants depending on `n`, `β`, `M`). -/
theorem cor_3_16_rate_computation
    (n : ℕ) (hn : 2 ≤ n)
    (β : ℝ) (_hβ_pos : 0 < β)
    (_hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (M : ℕ) (hM_pos : 0 < M) (_hM_le : M ≤ n - 1)
    (σ : ℝ) (_hσ : 0 < σ) :
    ∃ (C' : ℝ), 0 < C' ∧
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    (M : ℝ) ^ (-(2 * β)) + ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) +
      (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ) +
      σ ^ 2 * Real.log (1 / δ) / (n : ℝ) ≤
    C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
    C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
  have hn1_real_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  set r := (n : ℝ) ^ (-(2 * β) / (2 * β + 1))
  have hr_pos : 0 < r := rpow_pos_of_pos hn_pos _
  set A := (M : ℝ) ^ (-(2 * β)) + ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) +
            (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ)
  have hA_pos : 0 < A := by
    apply add_pos (add_pos _ _) _
    · exact rpow_pos_of_pos hM_real_pos _
    · exact rpow_pos_of_pos hn1_real_pos _
    · apply div_pos (mul_pos hM_real_pos _) hn_pos
      apply Real.log_pos
      have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
      linarith [mul_lt_mul_of_pos_left (one_lt_exp_iff.mpr one_pos) hn_pos]
  refine ⟨A / r + 1, by linarith [div_pos hA_pos hr_pos], ?_⟩
  intro δ hδ_pos hδ_le
  set L := σ ^ 2 * Real.log (1 / δ)
  have hL_nonneg : 0 ≤ L := by
    apply mul_nonneg (sq_nonneg σ)
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ_pos]; linarith
  suffices h : A + L / ↑n ≤ (A / r + 1) * r + (A / r + 1) * L / ↑n by
    convert h using 1; ring
  have h_expand_r : (A / r + 1) * r = A + r := by
    rw [add_mul, div_mul_cancel₀ A (ne_of_gt hr_pos), one_mul]
  have hAr_nonneg : 0 ≤ A / r := div_nonneg hA_pos.le hr_pos.le
  have h_expand_L : (A / r + 1) * L / ↑n ≥ L / ↑n := by
    apply div_le_div_of_nonneg_right _ hn_pos.le
    calc L = 1 * L := (one_mul L).symm
      _ ≤ (A / r + 1) * L := by
          apply mul_le_mul_of_nonneg_right _ hL_nonneg
          linarith
  linarith





end Chapter3
