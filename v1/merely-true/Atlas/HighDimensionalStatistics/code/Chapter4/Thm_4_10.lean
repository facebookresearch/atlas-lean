/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_8
import Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_10_Bridges

open MeasureTheory Matrix Real Finset BigOperators

namespace Rigollet.Chapter4.Thm_4_10

noncomputable section

set_option linter.unusedVariables false

variable {d : ℕ}

/-- The operator norm of a square real matrix, defined via the associated Euclidean-space
linear map's continuous-linear-map norm. -/
def matOpNorm (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- A random vector `X : Omega → Fin d → ℝ` is sub-Gaussian with parameter `sigma_sq`
under `mu` if it has zero mean and every one-dimensional projection `⟨u, X⟩` (over unit
vectors `u`) has moment generating function bounded by `exp (sigma_sq * s^2 / 2)`. -/
def IsSubGaussianVector {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (X : Omega → Fin d → ℝ) (sigma_sq : ℝ) : Prop :=
  AEMeasurable X mu ∧
  (∀ j : Fin d, ∫ omega, X omega j ∂mu = 0) ∧
  ∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    ∀ (s : ℝ),
      Integrable (fun omega => Real.exp (s * (∑ j : Fin d, u j * X omega j))) mu ∧
      ∫ omega, Real.exp (s * (∑ j : Fin d, u j * X omega j)) ∂mu ≤
        Real.exp (sigma_sq * s ^ 2 / 2)

/-- The empirical covariance matrix `(1/n) ∑_i X_i X_iᵀ` of `n` sample vectors. -/
def empiricalCov {n : ℕ} {Omega : Type*}
    (X : Fin n → Omega → Fin d → ℝ) (omega : Omega) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / (n : ℝ)) • ∑ i : Fin n, Matrix.of (fun (j k : Fin d) => X i omega j * X i omega k)

/-- The empirical covariance matrix is positive semidefinite, since it is a nonnegative
combination of rank-one PSD matrices `X_i X_iᵀ`. -/
lemma empiricalCov_posSemidef {n : ℕ} {Omega : Type*}
    (X : Fin n → Omega → Fin d → ℝ) (omega : Omega) :
    (empiricalCov X omega).PosSemidef := by
  unfold empiricalCov
  apply Matrix.PosSemidef.smul _ (by positivity)
  apply Matrix.posSemidef_sum
  intro i _
  have h : Matrix.of (fun (j k : Fin d) => X i omega j * X i omega k) =
    Matrix.vecMulVec (X i omega) (star (X i omega)) := by
    ext j k; simp [Matrix.vecMulVec, star]
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- The `ℓ₀` "norm" of a vector: the number of nonzero entries. -/
def l0norm (v : Fin d → ℝ) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

/-- The outer product `v v^⊤` of a vector with itself, viewed as a matrix. -/
def outerProduct (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of (fun i j => v i * v j)

/-- `sigMat` is a spiked covariance matrix with spike strength `theta` and direction `v`
if `sigMat = θ v vᵀ + I`. -/
def IsSpikedCovariance (sigMat : Matrix (Fin d) (Fin d) ℝ)
    (theta : ℝ) (v : Fin d → ℝ) : Prop :=
  sigMat = theta • outerProduct v + (1 : Matrix (Fin d) (Fin d) ℝ)

/-- `v` is the `k`-sparse largest eigenvector of `M`: it is a unit vector with at most
`k` nonzero entries, and its Rayleigh quotient is maximal among all `k`-sparse unit
vectors. -/
def IsKSparseLargestEigenvector (M : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) (k : ℕ) : Prop :=
  dotProduct v v = 1 ∧ l0norm v ≤ k ∧
  ∀ u : Fin d → ℝ, dotProduct u u = 1 → l0norm u ≤ k →
    dotProduct v (M.mulVec v) ≥ dotProduct u (M.mulVec u)

/-- Wraps Thm 4.8's `IsLargestEigenvector` predicate for vectors indexed by `Fin d`,
transferring the `Fin d → ℝ` argument into Euclidean space. -/
def IsLargestEigenvectorFin (M : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) : Prop :=
  Thm48.IsLargestEigenvector M (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin d))

/-- The sparse PCA rate appearing in Theorem 4.10: it controls the deviation of the
empirical covariance from the population covariance and is essentially
`max(√(t/n), t/n)` for `t ≍ k log(d/k) + log(1/δ)`. -/
def sparsePCARate (d k n : ℕ) (delta : ℝ) : ℝ :=
  let t := (2 * (k : ℝ)) * Real.log 288 + (2 * (k : ℝ)) * Real.log (Real.exp 1 * (d : ℝ) / (2 * (k : ℝ))) + Real.log (1 / delta)
  max (32 * Real.sqrt (2 * t / (n : ℝ))) (64 * t / (n : ℝ))

/-- The Euclidean (`ℓ²`) norm of a vector `f : Fin d → ℝ`. -/
def euclideanNorm (f : Fin d → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin d))‖

/-- Sign-invariant distance between `vhat` and `v`: the smaller of `‖vhat - v‖` and
`‖vhat + v‖`, since eigenvectors are determined only up to sign. -/
def signInvariantDist (vhat v : Fin d → ℝ) : ℝ :=
  min (euclideanNorm (vhat - v)) (euclideanNorm (vhat + v))

/-- The absolute constant `C` appearing in the final sparse PCA bound. Here we take
`C = 3`. -/
noncomputable def sparse_pca_C : ℝ := 3

/-- The absolute constant `sparse_pca_C` is strictly positive. -/
theorem sparse_pca_C_pos : 0 < sparse_pca_C := by
  unfold sparse_pca_C; norm_num

/-- The sparse PCA rate is always nonnegative. -/
lemma sparsePCARate_nonneg (d k n : ℕ) (delta : ℝ) : 0 ≤ sparsePCARate d k n delta := by
  unfold sparsePCARate; simp only
  exact le_max_of_le_left (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- The operator norm of any matrix is nonnegative. -/
lemma matOpNorm_nonneg (A : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ matOpNorm A := by
  unfold matOpNorm; exact norm_nonneg _

set_option maxHeartbeats 800000 in
/-- In finite dimensions the operator norm of a matrix is attained: there exists a unit
vector `u` such that `‖A u‖ = matOpNorm A`. Uses compactness of the unit sphere. -/
theorem finite_dim_opnorm_achieved {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℝ) :
    ∃ u : Fin d → ℝ, dotProduct u u = 1 ∧
      ‖(Matrix.toEuclideanLin A).toContinuousLinearMap (WithLp.toLp 2 u)‖ = matOpNorm A := by
  set f := (Matrix.toEuclideanLin A).toContinuousLinearMap
  haveI : ProperSpace (EuclideanSpace ℝ (Fin d)) := inferInstance
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have h_compact : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    isCompact_sphere 0 1
  have h_ne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1).Nonempty := by
    use EuclideanSpace.single ⟨0, hd⟩ 1
    simp [EuclideanSpace.norm_single]
  have h_cont : ContinuousOn (fun x : EuclideanSpace ℝ (Fin d) => ‖f x‖)
    (Metric.sphere 0 1) := (continuous_norm.comp f.continuous).continuousOn
  obtain ⟨x, hx_mem, hx_max⟩ := h_compact.exists_isMaxOn h_ne h_cont
  have hx_norm : ‖x‖ = 1 := by
    rwa [Metric.mem_sphere, dist_zero_right] at hx_mem
  set u := x.ofLp with hu_def
  refine ⟨u, ?_, ?_⟩
  ·
    have h_norm_sq : dotProduct u u = ‖x‖ ^ 2 := by
      simp only [dotProduct, hu_def]
      rw [EuclideanSpace.norm_eq]
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
      congr 1; ext i; simp [sq]
    rw [h_norm_sq, hx_norm, one_pow]
  ·
    have h_toLp : (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d)) = x := by
      ext i; simp [hu_def]
    rw [h_toLp]
    unfold matOpNorm
    apply le_antisymm
    · calc ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
        _ = ‖f‖ := by rw [hx_norm, mul_one]
    · rw [ContinuousLinearMap.opNorm_le_iff (norm_nonneg (f x))]
      intro y
      by_cases hy : y = 0
      · simp [hy]
      · have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
        set v := (‖y‖⁻¹ : ℝ) • y
        have hv_norm : ‖v‖ = 1 := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hy_pos)),
              inv_mul_cancel₀ (ne_of_gt hy_pos)]
        have hv_mem : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
          rw [Metric.mem_sphere, dist_zero_right]; exact hv_norm
        have hfv_le : ‖f v‖ ≤ ‖f x‖ := hx_max hv_mem
        have h_fy : f y = ‖y‖ • f v := by
          show f y = ‖y‖ • f ((‖y‖⁻¹ : ℝ) • y)
          rw [map_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hy_pos), one_smul]
        calc ‖f y‖ = ‖‖y‖ • f v‖ := by rw [h_fy]
          _ = ‖y‖ * ‖f v‖ := by
              rw [norm_smul, Real.norm_of_nonneg (le_of_lt hy_pos)]
          _ ≤ ‖y‖ * ‖f x‖ := mul_le_mul_of_nonneg_left hfv_le (le_of_lt hy_pos)
          _ = ‖f x‖ * ‖y‖ := mul_comm _ _

/-- The Euclidean norm is nonnegative. -/
lemma euclideanNorm_nonneg (f : Fin d → ℝ) : 0 ≤ euclideanNorm f := by
  unfold euclideanNorm; exact norm_nonneg _

/-- The sign-invariant distance is nonnegative. -/
lemma signInvariantDist_nonneg (vhat v : Fin d → ℝ) :
    0 ≤ signInvariantDist vhat v := by
  unfold signInvariantDist; exact le_min (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)

/-- The outer product `v vᵀ` equals `Matrix.vecMulVec` applied to the Euclidean-space
embedding of `v`. -/
lemma outerProduct_eq_vecMulVec (v : Fin d → ℝ) :
    outerProduct v = vecMulVec (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))
                                (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) := by
  ext i j; simp [outerProduct, of_apply, vecMulVec]

/-- If `⟨v, v⟩ = 1` then the Euclidean-space embedding of `v` has norm one. -/
lemma dotProduct_one_norm_one (v : Fin d → ℝ) (hv : dotProduct v v = 1) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [show ∑ i : Fin d, v i ^ 2 = dotProduct v v from by
    simp [dotProduct]; congr 1; ext; ring]
  simp [hv]

/-- Bridge lemma: our `IsSpikedCovariance` predicate implies the spiked-covariance
predicate used in Theorem 4.8 (formulated in Euclidean space). -/
lemma isSpikedCovariance_bridge (M : Matrix (Fin d) (Fin d) ℝ) (theta : ℝ)
    (htheta : 0 < theta) (v : Fin d → ℝ) (hv_dot : dotProduct v v = 1)
    (hSpike : IsSpikedCovariance M theta v) :
    Thm48.IsSpikedCovariance M theta (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) := by
  refine ⟨htheta, dotProduct_one_norm_one v hv_dot, ?_⟩
  rw [hSpike, outerProduct_eq_vecMulVec]

/-- The square of the sign-invariant distance equals the minimum of the squared Euclidean
norms of `vhat - v` and `vhat + v`. -/
lemma signInvariantDist_sq_eq {d : ℕ} (vhat v : Fin d → ℝ) :
    signInvariantDist vhat v ^ 2 =
    min (‖(WithLp.toLp 2 vhat : EuclideanSpace ℝ (Fin d)) -
          (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2)
        (‖(WithLp.toLp 2 vhat : EuclideanSpace ℝ (Fin d)) +
          (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2) := by
  unfold signInvariantDist euclideanNorm
  have h1 : (WithLp.toLp 2 (vhat - v) : EuclideanSpace ℝ (Fin d)) =
    (WithLp.toLp 2 vhat : EuclideanSpace ℝ (Fin d)) -
    (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) := by ext; simp
  have h2 : (WithLp.toLp 2 (vhat + v) : EuclideanSpace ℝ (Fin d)) =
    (WithLp.toLp 2 vhat : EuclideanSpace ℝ (Fin d)) +
    (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) := by ext; simp
  rw [h1, h2]
  have ha := norm_nonneg ((WithLp.toLp 2 vhat : EuclideanSpace ℝ (Fin d)) -
    (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)))
  have hb := norm_nonneg ((WithLp.toLp 2 vhat : EuclideanSpace ℝ (Fin d)) +
    (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)))
  rcases le_total
    ‖(WithLp.toLp 2 vhat : EuclideanSpace ℝ (Fin d)) -
      (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖
    ‖(WithLp.toLp 2 vhat : EuclideanSpace ℝ (Fin d)) +
      (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ with h | h
  · rw [min_eq_left h, min_eq_left (sq_le_sq' (by linarith) h)]
  · rw [min_eq_right h, min_eq_right (sq_le_sq' (by linarith) h)]

/-- Definitional equality between our `matOpNorm` and the operator-norm definition
used in Theorem 4.8. -/
lemma matOpNorm_eq_matrixOpNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    matOpNorm A = Thm48.matrixOpNorm A := rfl

/-- Davis–Kahan in `Fin d → ℝ` form: when `M_pop` is a spiked covariance and `vhat` is
the largest eigenvector of a PSD empirical matrix `M_emp`, the squared sign-invariant
distance between `vhat` and the spike `v` is bounded by
`(8/θ²) · ‖M_emp - M_pop‖²`. -/
theorem davis_kahan_l2_bridge
    {d : ℕ} (M_pop M_emp : Matrix (Fin d) (Fin d) ℝ)
    (theta : ℝ) (htheta : 0 < theta)
    (v vhat : Fin d → ℝ)
    (hSpike : IsSpikedCovariance M_pop theta v)
    (hv_dot : dotProduct v v = 1)
    (hvhat_dot : dotProduct vhat vhat = 1)
    (hPSD : M_emp.PosSemidef)
    (hEig : IsLargestEigenvectorFin M_emp vhat) :
    signInvariantDist vhat v ^ 2 ≤ 8 / theta ^ 2 * matOpNorm (M_emp - M_pop) ^ 2 := by

  set vtilde := (WithLp.toLp 2 vhat : EuclideanSpace ℝ (Fin d))
  set v' := (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))

  have hSpike48 := isSpikedCovariance_bridge M_pop theta htheta v hv_dot hSpike

  have hvt : ‖vtilde‖ = 1 := dotProduct_one_norm_one vhat hvhat_dot

  have hEig48 : Thm48.IsLargestEigenvector M_emp vtilde := hEig

  have h48 := Thm48.theorem_4_8 M_pop theta v' hSpike48 M_emp hPSD vtilde hvt hEig48

  rw [signInvariantDist_sq_eq]

  rw [matOpNorm_eq_matrixOpNorm]
  exact h48

/-- For nonnegative reals, squaring commutes with the `min` operation. -/
lemma sq_min_eq_min_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ^ 2 = min (a ^ 2) (b ^ 2) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (sq_le_sq' (by linarith) h)]
  · rw [min_eq_right h, min_eq_right (sq_le_sq' (by linarith) h)]

/-- Restatement of `davis_kahan_l2_bridge`: under the spiked-covariance and PSD
hypotheses, `signInvariantDist² ≤ (8/θ²) · ‖M_emp - M_pop‖²`. -/
theorem davis_kahan_sin_sq_bound
    {d : ℕ} (M_pop M_emp : Matrix (Fin d) (Fin d) ℝ)
    (theta : ℝ) (htheta : 0 < theta)
    (v vhat : Fin d → ℝ)
    (hSpike : IsSpikedCovariance M_pop theta v)
    (hv_dot : dotProduct v v = 1)
    (hvhat_dot : dotProduct vhat vhat = 1)
    (hPSD : M_emp.PosSemidef)
    (hEig : IsLargestEigenvectorFin M_emp vhat) :
    signInvariantDist vhat v ^ 2 ≤ 8 / theta ^ 2 * matOpNorm (M_emp - M_pop) ^ 2 :=
  davis_kahan_l2_bridge M_pop M_emp theta htheta v vhat hSpike hv_dot hvhat_dot hPSD hEig

/-- Componentwise expansion of `(θ v vᵀ + I) w`: the `i`-th entry equals
`θ · ⟨v, w⟩ · v_i + w_i`. -/
lemma spiked_mulVec_comp' (theta : ℝ) (v w : Fin d → ℝ) (i : Fin d) :
    ((theta • outerProduct v + 1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ w) i =
    theta * (∑ j, v j * w j) * v i + w i := by
  simp only [mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    outerProduct, of_apply, Matrix.one_apply]
  have h1 : ∀ x, (theta * (v i * v x) + if i = x then 1 else 0) * w x =
    theta * (v i * v x) * w x + (if i = x then 1 else 0) * w x := by intro x; ring
  simp_rw [h1, Finset.sum_add_distrib]
  congr 1
  · have h2 : ∀ x, theta * (v i * v x) * w x = theta * v i * (v x * w x) := by intro x; ring
    simp_rw [h2, ← Finset.mul_sum]; ring
  · simp

/-- Applying the Euclidean-space linear map of `M` and extracting the underlying
`Fin d → ℝ` is the same as ordinary matrix-vector multiplication. -/
lemma clm_ofLp' (M : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ((Matrix.toEuclideanLin M).toContinuousLinearMap x).ofLp = M *ᵥ x.ofLp := by
  have : (Matrix.toEuclideanLin M).toContinuousLinearMap x = Matrix.toEuclideanLin M x := rfl
  rw [this]
  show (toLpLin 2 2 M x).ofLp = M *ᵥ x.ofLp
  rw [toLpLin_apply]

/-- Cauchy–Schwarz: if `v` is a unit vector then `⟨v, w⟩² ≤ ‖w‖²`. -/
lemma dotProduct_sq_le' (v w : Fin d → ℝ) (hv : dotProduct v v = 1) :
    (∑ j, v j * w j) ^ 2 ≤ ∑ i, w i ^ 2 := by
  set v' := (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))
  set w' := (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin d))
  have hCS := abs_real_inner_le_norm (F := EuclideanSpace ℝ (Fin d)) v' w'
  have hinner : @inner ℝ _ _ v' w' = ∑ j, v j * w j := by
    simp [inner]; congr 1; ext j; ring
  have hv_norm : ‖v'‖ = 1 := by
    rw [EuclideanSpace.norm_eq]; simp only [norm_eq_abs, sq_abs]
    rw [show ∑ i : Fin d, v i ^ 2 = dotProduct v v from by simp [dotProduct]; congr 1; ext; ring]
    simp [hv]
  have hw_sq : ‖w'‖ ^ 2 = ∑ i, w i ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
    simp only [norm_eq_abs, sq_abs]; rfl
  rw [hinner, hv_norm, one_mul] at hCS
  rw [← hw_sq, ← sq_abs]
  exact sq_le_sq' (by linarith [norm_nonneg w', abs_nonneg (∑ j, v j * w j)]) hCS

set_option maxHeartbeats 800000 in
/-- The operator norm of a spiked-covariance matrix `θ vvᵀ + I` (with `v` a unit
vector and `θ > 0`) equals `1 + θ`: the maximum eigenvalue is achieved at `v`. -/
theorem spiked_covariance_opnorm
    {d : ℕ} (M_pop : Matrix (Fin d) (Fin d) ℝ)
    (theta : ℝ) (htheta : 0 < theta)
    (v : Fin d → ℝ)
    (hv_dot : dotProduct v v = 1)
    (hSpike : IsSpikedCovariance M_pop theta v) :
    matOpNorm M_pop = 1 + theta := by
  unfold matOpNorm
  set f := (Matrix.toEuclideanLin M_pop).toContinuousLinearMap with hf_def
  have hM : M_pop = theta • outerProduct v + 1 := hSpike

  have hfx : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin d),
      (f x).ofLp i = theta * (∑ j, v j * x.ofLp j) * v i + x.ofLp i := by
    intro x i
    have h := congr_fun (clm_ofLp' M_pop x) i
    rw [h, hM]; exact spiked_mulVec_comp' theta v (x.ofLp) i
  apply le_antisymm

  · apply ContinuousLinearMap.opNorm_le_bound _ (by linarith : (0 : ℝ) ≤ 1 + theta)
    intro x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    rw [show (1 + theta) = Real.sqrt ((1 + theta) ^ 2) from
      (Real.sqrt_sq (by linarith : (1 : ℝ) + theta ≥ 0)).symm,
      ← Real.sqrt_mul (sq_nonneg (1 + theta))]
    apply Real.sqrt_le_sqrt
    have key : ∀ i, ‖(f x).ofLp i‖ ^ 2 = (theta * (∑ j, v j * x.ofLp j) * v i + x.ofLp i) ^ 2 := by
      intro i; rw [hfx x i, norm_eq_abs, sq_abs]
    simp_rw [key, norm_eq_abs, sq_abs]
    set s := ∑ j, v j * x.ofLp j
    have expand : ∀ i, (theta * s * v i + x.ofLp i) ^ 2 =
      theta ^ 2 * s ^ 2 * v i ^ 2 + 2 * theta * s * v i * x.ofLp i + x.ofLp i ^ 2 := by
      intro i; ring
    simp_rw [expand, Finset.sum_add_distrib]
    have hv_sq : ∑ i, v i ^ 2 = 1 := by
      rw [show ∑ i, v i ^ 2 = dotProduct v v from by simp [dotProduct]; congr 1; ext; ring]
      exact hv_dot
    have h1 : ∑ i, theta ^ 2 * s ^ 2 * v i ^ 2 = theta ^ 2 * s ^ 2 := by
      rw [← Finset.mul_sum]; simp [hv_sq]
    have h2 : ∑ i, 2 * theta * s * v i * x.ofLp i = 2 * theta * s ^ 2 := by
      have : ∀ i, 2 * theta * s * v i * x.ofLp i = 2 * theta * s * (v i * x.ofLp i) := by
        intro i; ring
      simp_rw [this, ← Finset.mul_sum]; ring
    rw [h1, h2]
    have hCS := dotProduct_sq_le' v (fun i => x.ofLp i) hv_dot
    nlinarith [sq_nonneg s, sq_nonneg theta]

  · set v' := (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))
    have hv_norm : ‖v'‖ = 1 := by
      rw [EuclideanSpace.norm_eq]; simp only [norm_eq_abs, sq_abs]
      rw [show ∑ i : Fin d, v i ^ 2 = dotProduct v v from by simp [dotProduct]; congr 1; ext; ring]
      simp [hv_dot]
    have hfv : f v' = (1 + theta) • v' := by
      ext i
      have h1 := congr_fun (clm_ofLp' M_pop v') i
      have h2 : v'.ofLp = v := rfl
      rw [h1, h2, hM, spiked_mulVec_comp' theta v v i]
      simp [smul_eq_mul]
      rw [show ∑ j : Fin d, v j * v j = dotProduct v v from by simp [dotProduct]]
      rw [hv_dot]; ring
    have hfv_norm : ‖f v'‖ = (1 + theta) * ‖v'‖ := by
      rw [hfv, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    calc 1 + theta = (1 + theta) * 1 := by ring
      _ = (1 + theta) * ‖v'‖ := by rw [hv_norm]
      _ = ‖f v'‖ := hfv_norm.symm
      _ ≤ ‖f‖ * ‖v'‖ := ContinuousLinearMap.le_opNorm f v'
      _ = ‖f‖ * 1 := by rw [hv_norm]
      _ = ‖f‖ := by ring

/-- Davis–Kahan-style bound specialised to the spiked covariance model: the
sign-invariant distance satisfies
`d(v̂, v) ≤ C · ((1 + θ)/θ) · ‖M_emp − M_pop‖ / ‖M_pop‖`. -/
theorem davis_kahan_spiked_bound
    {d : ℕ} (M_pop M_emp : Matrix (Fin d) (Fin d) ℝ)
    (theta : ℝ) (htheta : 0 < theta)
    (v vhat : Fin d → ℝ)
    (hv_dot : dotProduct v v = 1)
    (hvhat_dot : dotProduct vhat vhat = 1)
    (hSpike : IsSpikedCovariance M_pop theta v)
    (hPSD : M_emp.PosSemidef)
    (hEig : IsLargestEigenvectorFin M_emp vhat) :
    signInvariantDist vhat v ≤
      sparse_pca_C * ((1 + theta) / theta) * (matOpNorm (M_emp - M_pop) / matOpNorm M_pop) := by

  have h_sq := davis_kahan_sin_sq_bound M_pop M_emp theta htheta v vhat hSpike
    hv_dot hvhat_dot hPSD hEig
  have h_norm := spiked_covariance_opnorm M_pop theta htheta v hv_dot hSpike
  have h_err_nn := matOpNorm_nonneg (M_emp - M_pop)

  have h_sqrt8 : Real.sqrt 8 ≤ 3 := by
    have h3 : (3 : ℝ) = Real.sqrt 9 := by
      rw [show (9 : ℝ) = 3 ^ 2 from by norm_num]
      exact (Real.sqrt_sq (by norm_num : (3 : ℝ) ≥ 0)).symm
    rw [h3]; exact Real.sqrt_le_sqrt (by norm_num)

  have h_rhs_nn : 0 ≤ Real.sqrt 8 / theta * matOpNorm (M_emp - M_pop) :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_of_lt htheta)) h_err_nn
  have h_linear : signInvariantDist vhat v ≤
      Real.sqrt 8 / theta * matOpNorm (M_emp - M_pop) := by
    apply le_of_sq_le_sq _ h_rhs_nn
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (8 : ℝ) ≥ 0)]
    exact h_sq

  have h_three : signInvariantDist vhat v ≤
      3 / theta * matOpNorm (M_emp - M_pop) :=
    h_linear.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right h_sqrt8 (le_of_lt htheta)) h_err_nn)

  rw [h_norm]
  show signInvariantDist vhat v ≤
    sparse_pca_C * ((1 + theta) / theta) * (matOpNorm (M_emp - M_pop) / (1 + theta))

  unfold sparse_pca_C
  rw [show 3 * ((1 + theta) / theta) * (matOpNorm (M_emp - M_pop) / (1 + theta)) =
    3 / theta * matOpNorm (M_emp - M_pop) from by
      field_simp]
  exact h_three

/-- Sparse Davis–Kahan bound: if the operator-norm error `‖M_emp − M_pop‖` is at most
`‖M_pop‖ · rate`, then `d(v̂, v) ≤ C · ((1 + θ)/θ) · rate`. -/
theorem sparse_davis_kahan_bound
    {d : ℕ} (M_pop M_emp : Matrix (Fin d) (Fin d) ℝ)
    (theta : ℝ) (htheta : 0 < theta)
    (v vhat : Fin d → ℝ)
    (hv_dot : dotProduct v v = 1)
    (hvhat_dot : dotProduct vhat vhat = 1)
    (hSpike : IsSpikedCovariance M_pop theta v)
    (hPSD : M_emp.PosSemidef)
    (hEig : IsLargestEigenvectorFin M_emp vhat)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hbound : matOpNorm (M_emp - M_pop) ≤ matOpNorm M_pop * rate) :
    signInvariantDist vhat v ≤
      sparse_pca_C * ((1 + theta) / theta) * rate := by

  have h_dk := davis_kahan_spiked_bound M_pop M_emp theta htheta v vhat hv_dot hvhat_dot hSpike hPSD hEig

  have h_div : matOpNorm (M_emp - M_pop) / matOpNorm M_pop ≤ rate := by
    by_cases h : matOpNorm M_pop = 0
    · rw [h, div_zero]; exact hrate
    · exact div_le_of_le_mul₀
        (lt_of_le_of_ne (matOpNorm_nonneg M_pop) (Ne.symm h)).le hrate
        (by rwa [mul_comm])

  have h_C_pos : 0 ≤ sparse_pca_C * ((1 + theta) / theta) := by
    apply mul_nonneg (le_of_lt sparse_pca_C_pos)
    exact div_nonneg (by linarith) (le_of_lt htheta)
  calc signInvariantDist vhat v
      ≤ sparse_pca_C * ((1 + theta) / theta) *
          (matOpNorm (M_emp - M_pop) / matOpNorm M_pop) := h_dk
    _ ≤ sparse_pca_C * ((1 + theta) / theta) * rate :=
        mul_le_mul_of_nonneg_left h_div h_C_pos

/-- Under the standard nondegenerate assumptions (`0 < δ < 1`, `0 < n`, `0 < k ≤ d/2`),
the sparse PCA rate is strictly positive. -/
lemma sparsePCARate_pos (d k n : ℕ) (hn : 0 < n) (hd : 0 < d) (hk_pos : 0 < k) (hk : k ≤ d / 2)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    0 < sparsePCARate d k n delta := by
  unfold sparsePCARate
  simp only
  apply lt_max_of_lt_right
  apply div_pos
  · apply mul_pos (by norm_num : (0:ℝ) < 64)
    apply add_pos_of_nonneg_of_pos
    · apply add_nonneg
      · apply mul_nonneg
        · apply mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg k)
        · exact Real.log_nonneg (by norm_num : (1:ℝ) ≤ 288)
      · apply mul_nonneg
        · apply mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg k)
        · apply Real.log_nonneg
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ↑k)]
          calc (1 : ℝ) * (2 * ↑k) = 2 * ↑k := one_mul _
            _ ≤ ↑d := by exact_mod_cast (show 2 * k ≤ d by omega)
            _ ≤ Real.exp 1 * ↑d := le_mul_of_one_le_left (by positivity)
                (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1))
    · rw [Real.log_div one_ne_zero (ne_of_gt hdelta), Real.log_one, zero_sub]
      exact neg_pos.mpr (Real.log_neg hdelta hdelta1)
  · exact Nat.cast_pos.mpr hn

/-- The "bad event" associated to a coordinate subset `s`: the set of `omega` for which
some unit vector supported on `s` exhibits a large deviation of the empirical Rayleigh
quotient from the population value. -/
def submatrixBadEvent {n : ℕ} {Omega : Type*}
    (X : Fin n → Omega → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (s : Finset (Fin d)) (t : ℝ) : Set Omega :=
  {omega : Omega |
    ∃ (x : Fin d → ℝ), (∀ i, i ∉ s → x i = 0) ∧ dotProduct x x = 1 ∧
    |dotProduct x ((empiricalCov X omega - covMat).mulVec x)| > matOpNorm covMat * t}

/-- Containment lemma: if there exists a `2k`-sparse unit vector `w` witnessing a large
deviation in the Rayleigh quotient, then `omega` lies in `submatrixBadEvent` for some
size-`2k` subset of coordinates. -/
theorem sparse_eigenstructure_containment
    {d : ℕ} {Omega : Type*} {_ : MeasurableSpace Omega}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (n : ℕ) (hn : 0 < n) (hd : 0 < d)
    (X : Fin n → Omega → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (k : ℕ) (hk_pos : 0 < k) (hk : k ≤ d / 2)
    (t : ℝ) (ht : 0 < t)
    (omega : Omega)

    (w : Fin d → ℝ)
    (hw_sparse : l0norm w ≤ 2 * k)
    (hw_unit : dotProduct w w = 1)
    (hw_large : |dotProduct w ((empiricalCov X omega - covMat).mulVec w)| >
        matOpNorm covMat * t) :
    ∃ s ∈ Finset.powersetCard (2 * k) (Finset.univ : Finset (Fin d)),
      omega ∈ submatrixBadEvent X covMat s t := by

  set S := Finset.univ.filter (fun i => w i ≠ 0) with hS_def

  have hS_card : S.card ≤ 2 * k := hw_sparse

  have h2k_le : 2 * k ≤ (Finset.univ : Finset (Fin d)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨T, hST, hT_univ, hT_card⟩ := Finset.exists_subsuperset_card_eq
    (Finset.filter_subset _ _) hS_card h2k_le

  refine ⟨T, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]; exact ⟨hT_univ, hT_card⟩


  · exact ⟨w, fun i hi => by
      by_contra h
      exact hi (hST (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)),
    hw_unit, hw_large⟩

/-- A quadratic form `xᵀ M x` for `x` supported on `s` equals the quadratic form of the
restricted vector against the submatrix `M.submatrix f f`, where `f` enumerates `s`. -/
lemma supported_quadratic_form_eq_submatrix
    {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (m : ℕ) (s : Finset (Fin d)) (hs : s.card = m)
    (x : Fin d → ℝ) (hx_supp : ∀ i, i ∉ s → x i = 0) :
    let f : Fin m → Fin d :=
      fun j => (Thm_4_10_Bridges.finsetEquivFin s (j.cast hs.symm)).val
    let M_sub := M.submatrix f f
    let y : Fin m → ℝ := fun j => x (f j)
    dotProduct x (M.mulVec x) = dotProduct y (M_sub.mulVec y) := by
  intro f M_sub y
  simp only [dotProduct, mulVec, Matrix.submatrix]
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    exact Fin.ext (Fin.val_eq_of_eq (Fin.cast_injective hs.symm
      ((Thm_4_10_Bridges.finsetEquivFin s).injective (Subtype.val_injective hab))))
  have hf_range : ∀ i : Fin d, i ∈ s ↔ ∃ j : Fin m, f j = i := by
    intro i; constructor
    · intro hi
      obtain ⟨j, hj⟩ := (Thm_4_10_Bridges.finsetEquivFin s).surjective ⟨i, hi⟩
      exact ⟨Fin.cast hs j, by simp [f, hj]⟩
    · intro ⟨j, hj⟩; rw [← hj]; exact ((Thm_4_10_Bridges.finsetEquivFin s) _).prop


  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ s)]
  have hfilt : Finset.filter (· ∈ s) Finset.univ = s := by ext; simp
  have hfilt_not : ∀ i ∈ Finset.univ.filter (fun j => j ∉ s),
      x i * ∑ j : Fin d, M i j * x j = 0 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [hx_supp i hi, zero_mul]
  rw [Finset.sum_eq_zero hfilt_not, add_zero, hfilt]

  have inner_restrict : ∀ i ∈ s, (∑ j : Fin d, M i j * x j) = ∑ j ∈ s, M i j * x j := by
    intro i _
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ s)]
    have hfilt' : Finset.filter (· ∈ s) Finset.univ = s := by ext; simp
    have hzero : ∀ j ∈ Finset.univ.filter (fun j => j ∉ s), M i j * x j = 0 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [hx_supp j hj, mul_zero]
    rw [Finset.sum_eq_zero hzero, add_zero, hfilt']
  rw [Finset.sum_congr rfl (fun i hi => by rw [inner_restrict i hi])]


  symm
  apply Finset.sum_nbij f
  · intro a _; exact (hf_range (f a)).mpr ⟨a, rfl⟩
  · intro a₁ _ a₂ _ h; exact hf_inj h
  · intro b hb; obtain ⟨j, hj⟩ := (hf_range b).mp hb
    exact ⟨j, Finset.mem_univ _, hj⟩
  · intro a _
    congr 1
    apply Finset.sum_nbij f
    · intro a' _; exact (hf_range (f a')).mpr ⟨a', rfl⟩
    · intro a₁ _ a₂ _ h; exact hf_inj h
    · intro b hb; obtain ⟨j, hj⟩ := (hf_range b).mp hb
      exact ⟨j, Finset.mem_univ _, hj⟩
    · intro a' _; rfl

/-- The dot product `x · x` for `x` supported on `s` equals the dot product of the
restricted vector with itself. -/
lemma supported_dotProduct_eq_restricted
    {d : ℕ} (m : ℕ) (s : Finset (Fin d)) (hs : s.card = m)
    (x : Fin d → ℝ) (hx_supp : ∀ i, i ∉ s → x i = 0) :
    let f : Fin m → Fin d :=
      fun j => (Thm_4_10_Bridges.finsetEquivFin s (j.cast hs.symm)).val
    let y : Fin m → ℝ := fun j => x (f j)
    dotProduct y y = dotProduct x x := by
  intro f y
  simp only [dotProduct]
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    exact Fin.ext (Fin.val_eq_of_eq (Fin.cast_injective hs.symm
      ((Thm_4_10_Bridges.finsetEquivFin s).injective (Subtype.val_injective hab))))
  have hf_range : ∀ i : Fin d, i ∈ s ↔ ∃ j : Fin m, f j = i := by
    intro i; constructor
    · intro hi
      obtain ⟨j, hj⟩ := (Thm_4_10_Bridges.finsetEquivFin s).surjective ⟨i, hi⟩
      exact ⟨Fin.cast hs j, by simp [f, hj]⟩
    · intro ⟨j, hj⟩; rw [← hj]; exact ((Thm_4_10_Bridges.finsetEquivFin s) _).prop
  symm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ s)]
  have hfilt : Finset.filter (· ∈ s) Finset.univ = s := by ext; simp
  have hzero : ∀ i ∈ Finset.univ.filter (fun j => j ∉ s), x i * x i = 0 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [hx_supp i hi, zero_mul]
  rw [Finset.sum_eq_zero hzero, add_zero, hfilt]
  symm
  rw [show (∑ i, y i * y i) = ∑ i ∈ Finset.univ, y i * y i from by simp]
  apply Finset.sum_nbij (fun j => (Thm_4_10_Bridges.finsetEquivFin s (j.cast hs.symm)).val)
  · intro a _; exact (hf_range (f a)).mpr ⟨a, rfl⟩
  · intro a₁ _ a₂ _ h; exact hf_inj h
  · intro b hb
    obtain ⟨j, hj⟩ := (hf_range b).mp hb
    exact ⟨j, Finset.mem_univ _, hj⟩

  · intro a _; rfl

/-- For any unit vector `x`, the absolute value of the Rayleigh quotient `xᵀ M x` is
bounded by the operator norm of `M`. -/
theorem rayleigh_quotient_le_matOpNorm
    {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) (hx : dotProduct x x = 1) :
    |dotProduct x (M.mulVec x)| ≤ matOpNorm M := by
  set v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x with hv_def
  set f := (toEuclideanLin M).toContinuousLinearMap with hf_def

  have h_inner : dotProduct x (M.mulVec x) = @inner ℝ _ _ v (f v) := by
    simp [dotProduct, inner, mulVec, hv_def, hf_def]
    congr 1; ext i; ring

  have h_norm_v : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    rw [show ∑ i, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)).ofLp i‖ ^ 2 = 1 from ?_]
    · exact Real.sqrt_one
    · rw [show ∑ i : Fin d,
            ‖((WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)).ofLp) i‖ ^ 2 =
            dotProduct x x from ?_]
      · exact hx
      · simp [dotProduct, sq]

  rw [h_inner]
  calc |@inner ℝ _ _ v (f v)|
      ≤ ‖v‖ * ‖f v‖ := abs_real_inner_le_norm v (f v)
    _ ≤ ‖v‖ * (‖f‖ * ‖v‖) := by gcongr; exact f.le_opNorm v
    _ = ‖f‖ := by rw [h_norm_v]; ring

/-- The bridges-file operator norm is bounded above by our `matOpNorm`. -/
lemma bridges_matOpNorm_le_matOpNorm_same {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    Thm_4_10_Bridges.matOpNorm A ≤ matOpNorm A := by
  unfold Thm_4_10_Bridges.matOpNorm matOpNorm
  apply ciSup_le; intro v
  by_cases hv : ‖v‖ = 1
  · rw [ciSup_pos hv]
    have h : ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖ =
             ‖(toEuclideanLin A) v‖ := by congr 1
    rw [h]
    calc ‖(toEuclideanLin A) v‖
        = ‖(toEuclideanLin A).toContinuousLinearMap v‖ := rfl
      _ ≤ ‖(toEuclideanLin A).toContinuousLinearMap‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖(toEuclideanLin A).toContinuousLinearMap‖ := by rw [hv, mul_one]
  · rw [ciSup_neg hv, Real.sSup_empty]; exact norm_nonneg _

/-- Our `matOpNorm` is bounded above by the bridges-file operator norm; combined with
the reverse inequality, the two definitions agree. -/
lemma matOpNorm_le_bridges_matOpNorm_same {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    matOpNorm A ≤ Thm_4_10_Bridges.matOpNorm A := by
  unfold matOpNorm Thm_4_10_Bridges.matOpNorm
  set g := (toEuclideanLin A).toContinuousLinearMap

  have hbdd : BddAbove (Set.range (fun v : EuclideanSpace ℝ (Fin d) =>
      ⨆ (_ : ‖v‖ = 1), ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖)) := by
    use ‖g‖
    intro x hx
    simp only [Set.mem_range] at hx
    obtain ⟨v, rfl⟩ := hx
    by_cases hv : ‖v‖ = 1
    · rw [ciSup_pos hv]
      have : ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖ = ‖(toEuclideanLin A) v‖ := by
        congr 1
      rw [this]
      calc ‖(toEuclideanLin A) v‖ = ‖g v‖ := rfl
        _ ≤ ‖g‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖g‖ := by rw [hv, mul_one]
    · rw [ciSup_neg hv, Real.sSup_empty]; exact norm_nonneg _
  have hM : 0 ≤ ⨆ (v : EuclideanSpace ℝ (Fin d)) (_ : ‖v‖ = 1),
      ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖ :=
    Real.iSup_nonneg (fun v => Real.iSup_nonneg (fun _ => norm_nonneg _))
  rw [ContinuousLinearMap.opNorm_le_iff hM]
  intro x
  by_cases hx : x = 0
  · subst hx; simp
  · have hx_norm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hx_pos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx_norm)
    set u := (‖x‖⁻¹ : ℝ) • x
    have hu_norm : ‖u‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hx_pos)),
          inv_mul_cancel₀ hx_norm]
    have hfx : g x = ‖x‖ • g ((‖x‖⁻¹ : ℝ) • x) := by
      rw [map_smul, smul_smul, mul_inv_cancel₀ hx_norm, one_smul]
    rw [hfx, norm_smul, Real.norm_of_nonneg (le_of_lt hx_pos), mul_comm]
    gcongr
    have h1 : ‖g u‖ = ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec u)‖ := by
      congr 1
    rw [h1]
    calc ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec u)‖
        ≤ ⨆ (_ : ‖u‖ = 1), ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec u)‖ := by
          rw [ciSup_pos hu_norm]
      _ ≤ ⨆ (v : EuclideanSpace ℝ (Fin d)) (_ : ‖v‖ = 1),
            ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖ := le_ciSup hbdd u

/-- The bridges-file operator norm of a principal submatrix is bounded by `matOpNorm`
of the full matrix. -/
theorem bridges_matOpNorm_submatrix_le_matOpNorm
    {d : ℕ} (covMat : Matrix (Fin d) (Fin d) ℝ)
    (m : ℕ) (s : Finset (Fin d)) (hs : s.card = m) :
    let f : Fin m → Fin d :=
      fun j => (Thm_4_10_Bridges.finsetEquivFin s (j.cast hs.symm)).val
    let covMatSub := covMat.submatrix f f
    Thm_4_10_Bridges.matOpNorm (d := m) covMatSub ≤ matOpNorm covMat := by
  intro f covMatSub
  calc Thm_4_10_Bridges.matOpNorm (d := m) covMatSub
      ≤ Thm_4_10_Bridges.matOpNorm covMat :=
        Thm_4_10_Bridges.matOpNorm_submatrix_le covMat s hs
    _ ≤ matOpNorm covMat := bridges_matOpNorm_le_matOpNorm_same covMat

/-- A large supported quadratic form `|xᵀ(Σ̂ - Σ)x|` translates into a large
operator-norm deviation `‖Σ̂_sub - Σ_sub‖ > ‖Σ_sub‖ · t` for the restricted (sub)matrix
of `Σ`. -/
lemma quadratic_form_to_submatrix_opnorm
    {d : ℕ} {Omega : Type*}
    (n : ℕ) (X : Fin n → Omega → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (m : ℕ) (hm_le : m ≤ d)
    (s : Finset (Fin d)) (hs : s.card = m)
    (t : ℝ) (ht : 0 < t)
    (omega : Omega)
    (x : Fin d → ℝ)
    (hx_supp : ∀ i, i ∉ s → x i = 0)
    (hx_unit : dotProduct x x = 1)
    (hx_large : |dotProduct x ((empiricalCov X omega - covMat).mulVec x)| >
        matOpNorm covMat * t) :
    let f : Fin m → Fin d :=
      fun j => (Thm_4_10_Bridges.finsetEquivFin s (j.cast hs.symm)).val
    let Y := Thm_4_10_Bridges.restrictSamples s hs X
    let covMatSub := covMat.submatrix f f
    Thm_4_10_Bridges.matOpNorm (d := m)
      (Thm_4_6.empiricalCovariance Y omega - covMatSub) >
        Thm_4_10_Bridges.matOpNorm (d := m) covMatSub * t := by
  intro f Y covMatSub

  set y : Fin m → ℝ := fun j => x (f j) with hy_def

  have h_quad_eq := supported_quadratic_form_eq_submatrix
    (empiricalCov X omega - covMat) m s hs x hx_supp

  have h_sub_eq : (empiricalCov X omega - covMat).submatrix f f =
      (empiricalCov X omega).submatrix f f - covMat.submatrix f f := by
    ext i j; simp [Matrix.submatrix, Matrix.sub_apply]

  have h_emp_eq : (empiricalCov X omega).submatrix f f =
      Thm_4_6.empiricalCovariance Y omega := by
    ext i j
    simp only [Matrix.submatrix, empiricalCov, Thm_4_6.empiricalCovariance,
      Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply]
    congr 1

  have h_error_sub_eq : (empiricalCov X omega - covMat).submatrix f f =
      Thm_4_6.empiricalCovariance Y omega - covMatSub := by
    rw [h_sub_eq, h_emp_eq]

  have hy_unit : dotProduct y y = 1 := by
    have h_dp := supported_dotProduct_eq_restricted m s hs x hx_supp
    rw [h_dp]; exact hx_unit


  have h_rayleigh_sub := rayleigh_quotient_le_matOpNorm
    (Thm_4_6.empiricalCovariance Y omega - covMatSub) y hy_unit

  have h_quad_rewrite : dotProduct x ((empiricalCov X omega - covMat).mulVec x) =
      dotProduct y ((Thm_4_6.empiricalCovariance Y omega - covMatSub).mulVec y) := by
    rw [h_quad_eq]; congr 1
    show ((empiricalCov X omega - covMat).submatrix f f).mulVec y =
        (Thm_4_6.empiricalCovariance Y omega - covMatSub).mulVec y
    rw [h_error_sub_eq]


  have h_bridges_error_large : Thm_4_10_Bridges.matOpNorm (d := m)
      (Thm_4_6.empiricalCovariance Y omega - covMatSub) > matOpNorm covMat * t := by
    calc Thm_4_10_Bridges.matOpNorm (d := m)
          (Thm_4_6.empiricalCovariance Y omega - covMatSub)
        ≥ matOpNorm (Thm_4_6.empiricalCovariance Y omega - covMatSub) :=
          matOpNorm_le_bridges_matOpNorm_same _
      _ ≥ |dotProduct y ((Thm_4_6.empiricalCovariance Y omega - covMatSub).mulVec y)| :=
          h_rayleigh_sub
      _ = |dotProduct x ((empiricalCov X omega - covMat).mulVec x)| := by
          rw [h_quad_rewrite]
      _ > matOpNorm covMat * t := hx_large

  have h_cov_bridge : Thm_4_10_Bridges.matOpNorm (d := m) covMatSub ≤ matOpNorm covMat :=
    bridges_matOpNorm_submatrix_le_matOpNorm covMat m s hs

  calc Thm_4_10_Bridges.matOpNorm (d := m)
        (Thm_4_6.empiricalCovariance Y omega - covMatSub)
      > matOpNorm covMat * t := h_bridges_error_large
    _ ≥ Thm_4_10_Bridges.matOpNorm (d := m) covMatSub * t :=
        mul_le_mul_of_nonneg_right h_cov_bridge (le_of_lt ht)

/-- The submatrix bad event is contained in the event that the submatrix operator-norm
deviation is large. -/
lemma submatrixBadEvent_subset_opnorm_event
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]

    (n : ℕ) (X : Fin n → Omega → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (m : ℕ) (hm_le : m ≤ d)
    (s : Finset (Fin d)) (hs : s.card = m)
    (t : ℝ) (ht : 0 < t) :
    let f : Fin m → Fin d :=
      fun j => (Thm_4_10_Bridges.finsetEquivFin s (j.cast hs.symm)).val
    let Y := Thm_4_10_Bridges.restrictSamples s hs X
    let covMatSub := covMat.submatrix f f
    submatrixBadEvent X covMat s t ⊆
      {omega : Omega | Thm_4_10_Bridges.matOpNorm (d := m)
        (Thm_4_6.empiricalCovariance Y omega - covMatSub) >
          Thm_4_10_Bridges.matOpNorm (d := m) covMatSub * t} := by
  intro f Y covMatSub omega h_mem
  simp only [Set.mem_setOf_eq] at h_mem ⊢
  obtain ⟨x, hx_supp, hx_unit, hx_large⟩ := h_mem
  exact quadratic_form_to_submatrix_opnorm n X covMat m hm_le s hs t ht omega x
    hx_supp hx_unit hx_large

/-- If `X` is a sub-Gaussian random vector, then for each coordinate `c` and each `s`,
the function `ω ↦ exp(s · X(ω) c)` is integrable. -/
theorem subGaussianVector_component_exp_integrable
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → Fin d → ℝ) (sigma_sq : ℝ)
    (hSubG : IsSubGaussianVector mu X sigma_sq)
    (c : Fin d) (s : ℝ) :
    Integrable (fun ω => exp (s * X ω c)) mu := by
  obtain ⟨_, _, hMGF⟩ := hSubG
  have he_norm : ‖(EuclideanSpace.single c (1 : ℝ))‖ = 1 := by
    rw [PiLp.norm_single]; simp
  have hspec := hMGF (EuclideanSpace.single c 1) he_norm s
  have hconv : (fun omega =>
      Real.exp (s * (∑ j : Fin d, (EuclideanSpace.single c (1 : ℝ)) j * X omega j))) =
      (fun ω => exp (s * X ω c)) := by
    ext ω; congr 1; congr 1; simp
  rw [← hconv]
  exact hspec.1

/-- Each component `ω ↦ X(ω) c` of a sub-Gaussian random vector is almost-everywhere
strongly measurable. -/
lemma subGaussianVector_component_aestronglyMeasurable
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → Fin d → ℝ) (sigma_sq : ℝ)
    (hSubG : IsSubGaussianVector mu X sigma_sq)
    (c : Fin d) :
    AEStronglyMeasurable (fun ω => X ω c) mu := by
  rw [aestronglyMeasurable_iff_aemeasurable]
  have h1 := (subGaussianVector_component_exp_integrable mu X sigma_sq hSubG c 1).aestronglyMeasurable
  rw [aestronglyMeasurable_iff_aemeasurable] at h1
  have h2 : AEMeasurable (fun ω => Real.log (Real.exp (1 * X ω c))) mu :=
    Real.measurable_log.comp_aemeasurable h1
  simp [Real.log_exp] at h2
  exact h2

/-- Each component of a sub-Gaussian random vector is integrable. -/
theorem subGaussianVector_component_integrable
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → Fin d → ℝ) (sigma_sq : ℝ)
    (hSubG : IsSubGaussianVector mu X sigma_sq)
    (c : Fin d) :
    Integrable (fun ω => X ω c) mu := by
  have hexp_pos := subGaussianVector_component_exp_integrable mu X sigma_sq hSubG c 1
  have hexp_neg := subGaussianVector_component_exp_integrable mu X sigma_sq hSubG c (-1)
  have h_abs_pow := ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul
    one_ne_zero hexp_pos hexp_neg 1
  have h_abs : Integrable (fun ω => |X ω c|) mu := by
    convert h_abs_pow using 1; ext ω; simp [pow_one]
  exact h_abs.mono
    (subGaussianVector_component_aestronglyMeasurable mu X sigma_sq hSubG c)
    (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]))

/-- Each component of every restricted sample `Y k ω` (the restriction of the random
vector `X k ω` to a coordinate subset `s`) is integrable. -/
lemma restricted_samples_integrable_comp
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (n : ℕ) (X : Fin n → Omega → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (m : ℕ) (s : Finset (Fin d)) (hs : s.card = m)
    (hSubG : ∀ (i : Fin n), IsSubGaussianVector mu (X i) (matOpNorm covMat)) :
    let Y := Thm_4_10_Bridges.restrictSamples s hs X
    ∀ (k : Fin n) (c : Fin m), Integrable (fun ω => Y k ω c) mu := by
  intro Y k c


  show Integrable (fun ω => Thm_4_10_Bridges.restrictSamples s hs X k ω c) mu
  simp only [Thm_4_10_Bridges.restrictSamples, Thm_4_10_Bridges.restrictVec]
  exact subGaussianVector_component_integrable mu (X k) (matOpNorm covMat) (hSubG k) _

/-- Each component of a sub-Gaussian random vector belongs to `L²`. -/
theorem subGaussianVector_component_memLp_two
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → Fin d → ℝ) (sigma_sq : ℝ)
    (hSubG : IsSubGaussianVector mu X sigma_sq)
    (j : Fin d) : MemLp (fun ω => X ω j) 2 mu := by
  have h_asm := subGaussianVector_component_aestronglyMeasurable mu X sigma_sq hSubG j
  rw [memLp_two_iff_integrable_sq h_asm]
  have hexp_pos := subGaussianVector_component_exp_integrable mu X sigma_sq hSubG j 1
  have hexp_neg := subGaussianVector_component_exp_integrable mu X sigma_sq hSubG j (-1)
  have h_abs_pow := ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul
    one_ne_zero hexp_pos hexp_neg 2
  convert h_abs_pow using 1; ext ω; rw [sq_abs]

/-- Products of components of restricted samples are integrable (via Cauchy–Schwarz
since each component lies in `L²`). -/
lemma restricted_samples_integrable_prod
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (n : ℕ) (X : Fin n → Omega → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (m : ℕ) (s : Finset (Fin d)) (hs : s.card = m)
    (hSubG : ∀ (i : Fin n), IsSubGaussianVector mu (X i) (matOpNorm covMat)) :
    let Y := Thm_4_10_Bridges.restrictSamples s hs X
    ∀ (k l : Fin n) (c c' : Fin m), Integrable (fun ω => Y k ω c * Y l ω c') mu := by
  intro Y k l c c'

  show Integrable (fun ω => Thm_4_10_Bridges.restrictSamples s hs X k ω c *
    Thm_4_10_Bridges.restrictSamples s hs X l ω c') mu
  simp only [Thm_4_10_Bridges.restrictSamples, Thm_4_10_Bridges.restrictVec]

  have hf : MemLp (fun ω => X k ω ((Thm_4_10_Bridges.finsetEquivFin s) (c.cast hs.symm))) 2 mu :=
    subGaussianVector_component_memLp_two mu (X k) (matOpNorm covMat) (hSubG k) _
  have hg : MemLp (fun ω => X l ω ((Thm_4_10_Bridges.finsetEquivFin s) (c'.cast hs.symm))) 2 mu :=
    subGaussianVector_component_memLp_two mu (X l) (matOpNorm covMat) (hSubG l) _
  exact hf.integrable_mul hg

/-- Pairwise-product independence (mean factorisation) for distinct sample indices
transfers from the full samples `X` to the restricted samples `Y`. -/
lemma restricted_samples_indep_general
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (n : ℕ) (X : Fin n → Omega → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (m : ℕ) (s : Finset (Fin d)) (hs : s.card = m)
    (hSubG : ∀ (i : Fin n), IsSubGaussianVector mu (X i) (matOpNorm covMat))
    (hIndep : ∀ (i j : Fin n), i ≠ j → ∀ (a b : Fin d),
      ∫ ω, X i ω a * X j ω b ∂mu = (∫ ω, X i ω a ∂mu) * (∫ ω, X j ω b ∂mu)) :
    let Y := Thm_4_10_Bridges.restrictSamples s hs X
    ∀ (i j : Fin n), i ≠ j → ∀ (a b : Fin m),
      ∫ ω, Y i ω a * Y j ω b ∂mu = (∫ ω, Y i ω a ∂mu) * (∫ ω, Y j ω b ∂mu) := by
  intro Y i j hij a b

  show ∫ ω, Thm_4_10_Bridges.restrictSamples s hs X i ω a *
      Thm_4_10_Bridges.restrictSamples s hs X j ω b ∂mu =
    (∫ ω, Thm_4_10_Bridges.restrictSamples s hs X i ω a ∂mu) *
    (∫ ω, Thm_4_10_Bridges.restrictSamples s hs X j ω b ∂mu)
  simp only [Thm_4_10_Bridges.restrictSamples, Thm_4_10_Bridges.restrictVec]
  exact hIndep i j hij _ _

/-- Direct bridge to the corresponding lemma in `Thm_4_10_Bridges`: the bridges-file
operator norm of a principal submatrix is bounded by the bridges-file operator norm of
the full matrix. -/
theorem bridge_bridges_matOpNorm_submatrix_le
    {d : ℕ}
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (m : ℕ) (s : Finset (Fin d)) (hs : s.card = m) :
    let f : Fin m → Fin d :=
      fun j => (Thm_4_10_Bridges.finsetEquivFin s (j.cast hs.symm)).val
    let covMatSub := covMat.submatrix f f
    Thm_4_10_Bridges.matOpNorm (d := m) covMatSub ≤ Thm_4_10_Bridges.matOpNorm (d := d) covMat :=
  Thm_4_10_Bridges.matOpNorm_submatrix_le covMat s hs

/-- A sub-Gaussian random vector is in particular almost-everywhere measurable. -/
theorem bridge_subGaussianVector_aemeasurable
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (X : Omega → Fin d → ℝ) (σsq : ℝ)
    (hSubG : IsSubGaussianVector mu X σsq) :
    AEMeasurable X mu := hSubG.1

/-- The Thm 4.6 sub-Gaussian-vector property is monotone in the variance parameter:
upgrading `σ₁ ≤ σ₂` preserves sub-Gaussianity. -/
lemma IsSubGaussianVec_mono
    {m : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (Y : Omega → Fin m → ℝ) (σ₁ σ₂ : ℝ) (h12 : σ₁ ≤ σ₂)
    (hSG : Thm_4_6.IsSubGaussianVec (d := m) mu Y σ₁) :
    Thm_4_6.IsSubGaussianVec (d := m) mu Y σ₂ := by
  refine ⟨hSG.1, fun u hu s => ?_, fun u hu s => ?_⟩
  · calc ∫ ω, Real.exp (s * ∑ j, u j * Y ω j) ∂mu
        ≤ Real.exp (σ₁ * s ^ 2 / 2) := hSG.2.1 u hu s
      _ ≤ Real.exp (σ₂ * s ^ 2 / 2) := by
          apply Real.exp_le_exp_of_le
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right h12 (sq_nonneg s)
          · norm_num
  · calc ∫⁻ ω, ENNReal.ofReal (Real.exp (s * ∑ j, u j * Y ω j)) ∂mu
        ≤ ENNReal.ofReal (Real.exp (σ₁ * s ^ 2 / 2)) := hSG.2.2 u hu s
      _ ≤ ENNReal.ofReal (Real.exp (σ₂ * s ^ 2 / 2)) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp_of_le
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right h12 (sq_nonneg s)
          · norm_num

/-- Our `IsSubGaussianVector` predicate implies the Thm 4.6 `IsSubGaussianVec`
predicate with the same parameter. -/
lemma IsSubGaussianVec_of_IsSubGaussianVector
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (X : Omega → Fin d → ℝ) (σsq : ℝ)
    (hSubG : IsSubGaussianVector mu X σsq) :
    Thm_4_6.IsSubGaussianVec (d := d) mu X σsq := by
  refine ⟨hSubG.1, fun u hu s => ?_, fun u hu s => ?_⟩
  · exact (hSubG.2.2 u hu s).2
  ·
    have hpair := hSubG.2.2 u hu s
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpair.1
      (ae_of_all _ (fun ω => le_of_lt (Real.exp_pos _)))]
    exact ENNReal.ofReal_le_ofReal hpair.2


/-- A principal submatrix of a positive-definite matrix indexed by an injection is
itself positive definite. -/
lemma Matrix.PosDef.submatrix_of_injective {d m : ℕ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {f : Fin m → Fin d} (hf : Function.Injective f) :
    (M.submatrix f f).PosDef := by
  refine ⟨hM.isHermitian.submatrix f, fun x hx => ?_⟩
  have hy : Finsupp.mapDomain f x ≠ 0 :=
    fun h => hx (Finsupp.mapDomain_injective hf h)
  have hq := hM.2 hy
  suffices h : (x.sum fun i xi => x.sum fun j xj => star xi * (M.submatrix f f) i j * xj) =
      ((Finsupp.mapDomain f x).sum fun i yi =>
        (Finsupp.mapDomain f x).sum fun j yj => star yi * M i j * yj) by
    rw [h]; exact hq
  simp only [star_trivial, Matrix.submatrix_apply]
  symm
  rw [Finsupp.sum_mapDomain_index]
  · congr 1; ext i xi
    rw [Finsupp.sum_mapDomain_index]
    · intro b; ring
    · intro b m₁ m₂; ring
  · intro b; simp only [zero_mul, Finsupp.sum_fun_zero]
  · intro b m₁ m₂
    rw [← Finsupp.sum_add]
    congr 1; ext j xj; ring




/-- The support of a vector: the finset of coordinates on which `v` is nonzero. -/
def vectorSupport (v : Fin d → ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i => v i ≠ 0

/-- The cardinality of the union of supports of two `k`-sparse vectors is at most
`2k`. -/
theorem support_union_card (v w : Fin d → ℝ) (k : ℕ)
    (hv : l0norm v ≤ k) (hw : l0norm w ≤ k) :
    (vectorSupport v ∪ vectorSupport w).card ≤ 2 * k := by
  calc (vectorSupport v ∪ vectorSupport w).card
      ≤ (vectorSupport v).card + (vectorSupport w).card := Finset.card_union_le _ _
    _ ≤ k + k := Nat.add_le_add hv hw
    _ = 2 * k := by ring

/-- A vector supported on a finset `S` has `ℓ₀` norm at most `S.card`. -/
lemma support_subset_implies_l0norm_le (w : Fin d → ℝ) (S : Finset (Fin d))
    (hw_supp : ∀ i, i ∉ S → w i = 0) :
    l0norm w ≤ S.card := by
  unfold l0norm
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi
  by_contra h_not_in_S
  exact hi.2 (hw_supp i h_not_in_S)

/-- `HasSparseWitness` asserts that whenever the operator-norm deviation
`‖Σ̂ - Σ‖` exceeds `‖Σ‖ · t`, there is a `2k`-sparse unit vector `w` witnessing this
deviation via its quadratic form. -/
def HasSparseWitness {d : ℕ} {Omega : Type*}
    (X : Fin n → Omega → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (k : ℕ) (t : ℝ) : Prop :=
  ∀ (omega : Omega),
    matOpNorm (empiricalCov X omega - covMat) > matOpNorm covMat * t →
    ∃ w : Fin d → ℝ, l0norm w ≤ 2 * k ∧ dotProduct w w = 1 ∧
      |dotProduct w ((empiricalCov X omega - covMat).mulVec w)| > matOpNorm covMat * t






/-- Classical Stirling-type upper bound on binomial coefficients:
`C(n, k) ≤ (e · n / k)^k`. -/
lemma binom_upper_bound (n k : ℕ) (hk : 1 ≤ k) (_hkn : k ≤ n) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * ↑n / ↑k) ^ k := by
  have hk_pos : (0 : ℝ) < ↑k := by positivity
  have h1 : (n.choose k : ℝ) ≤ (↑n) ^ k / (↑(Nat.factorial k) : ℝ) := Nat.choose_le_pow_div k n
  have h2 : (↑k : ℝ) ^ k / (↑(Nat.factorial k) : ℝ) ≤ Real.exp (↑k : ℝ) :=
    Real.pow_div_factorial_le_exp (↑k : ℝ) (le_of_lt hk_pos) k
  have rhs_eq : (Real.exp 1 * ↑n / ↑k) ^ k = Real.exp ↑k * ((↑n) ^ k / (↑k) ^ k) := by
    rw [mul_div_assoc, mul_pow, Real.exp_one_pow, div_pow]
  rw [rhs_eq]
  calc (n.choose k : ℝ)
      ≤ (↑n) ^ k / (↑(Nat.factorial k) : ℝ) := h1
    _ = ((↑n) ^ k / (↑k) ^ k) * ((↑k) ^ k / (↑(Nat.factorial k) : ℝ)) := by field_simp
    _ ≤ ((↑n) ^ k / (↑k) ^ k) * Real.exp (↑k : ℝ) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp ↑k * ((↑n) ^ k / (↑k) ^ k) := by ring

/-- Combined exponential bound:
`C(d, 2k) · 288^(2k) ≤ exp(2k log 288 + 2k log(e d/(2k)))`. -/
lemma stirling_binom_exp_bound
    (d k : ℕ) (hd : 0 < d) (hk_pos : 0 < k) (hk : k ≤ d / 2) :
    ↑(Nat.choose d (2 * k)) * (288 : ℝ) ^ (2 * k) ≤
      Real.exp ((2 * ↑k) * Real.log 288 + (2 * ↑k) * Real.log (Real.exp 1 * ↑d / (2 * ↑k))) := by
  have h2k_nat_pos : 1 ≤ 2 * k := by omega
  have h2k_le_d : 2 * k ≤ d := by omega
  have h_ed2k_pos : (0 : ℝ) < Real.exp 1 * ↑d / (2 * ↑k) := by positivity

  have h_binom := binom_upper_bound d (2 * k) h2k_nat_pos h2k_le_d
  have h2k_cast : ((↑(2 * k) : ℝ)) = 2 * (↑k : ℝ) := by push_cast; ring
  rw [h2k_cast] at h_binom

  have h_prod : ↑(Nat.choose d (2 * k)) * (288 : ℝ) ^ (2 * k) ≤
      (Real.exp 1 * ↑d / (2 * ↑k)) ^ (2 * k) * (288 : ℝ) ^ (2 * k) :=
    mul_le_mul_of_nonneg_right h_binom (by positivity)

  have h_combine : (Real.exp 1 * ↑d / (2 * ↑k)) ^ (2 * k) * (288 : ℝ) ^ (2 * k) =
      (288 * (Real.exp 1 * ↑d / (2 * ↑k))) ^ (2 * k) := by
    rw [mul_pow]; ring

  have h_arg_pos : (0 : ℝ) < 288 * (Real.exp 1 * ↑d / (2 * ↑k)) := by positivity
  have h_rpow : (288 * (Real.exp 1 * ↑d / (2 * ↑k))) ^ (2 * k) =
      Real.exp ((2 * ↑k) * Real.log (288 * (Real.exp 1 * ↑d / (2 * ↑k)))) := by
    rw [← Real.rpow_natCast (288 * (Real.exp 1 * ↑d / (2 * ↑k))) (2 * k)]
    rw [Real.rpow_def_of_pos h_arg_pos]
    push_cast; ring_nf

  have h_log_split : Real.log (288 * (Real.exp 1 * ↑d / (2 * ↑k))) =
      Real.log 288 + Real.log (Real.exp 1 * ↑d / (2 * ↑k)) :=
    Real.log_mul (by positivity) (ne_of_gt h_ed2k_pos)

  calc ↑(Nat.choose d (2 * k)) * (288 : ℝ) ^ (2 * k)
      ≤ (Real.exp 1 * ↑d / (2 * ↑k)) ^ (2 * k) * (288 : ℝ) ^ (2 * k) := h_prod
    _ = (288 * (Real.exp 1 * ↑d / (2 * ↑k))) ^ (2 * k) := h_combine
    _ = Real.exp ((2 * ↑k) * Real.log (288 * (Real.exp 1 * ↑d / (2 * ↑k)))) := h_rpow
    _ = Real.exp ((2 * ↑k) * (Real.log 288 + Real.log (Real.exp 1 * ↑d / (2 * ↑k)))) := by
        rw [h_log_split]
    _ = Real.exp ((2 * ↑k) * Real.log 288 + (2 * ↑k) * Real.log (Real.exp 1 * ↑d / (2 * ↑k))) := by
        ring_nf


set_option maxHeartbeats 400000 in
/-- Threshold check: with the rate `sparsePCARate d k n δ`, the exponential bound
appearing in `thm46_union_bound_exp` is at most `δ`. -/
lemma threshold_bound_le_delta
    (d k n : ℕ) (hn : 0 < n) (hd : 0 < d) (hk_pos : 0 < k) (hk : k ≤ d / 2)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    Real.exp ((2 * ↑k) * Real.log 288 + (2 * ↑k) * Real.log (Real.exp 1 * ↑d / (2 * ↑k))
      - (↑n / 2) * min ((sparsePCARate d k n delta / 32) ^ 2) (sparsePCARate d k n delta / 32))
    ≤ delta := by


  set L := (2 * (k : ℝ)) * Real.log 288 + (2 * (k : ℝ)) * Real.log (Real.exp 1 * (d : ℝ) / (2 * (k : ℝ))) with hL_def
  set T := L + Real.log (1 / delta) with hT_def
  set r := sparsePCARate d k n delta with hr_def
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn

  have hL_nonneg : 0 ≤ L := by
    apply add_nonneg
    · apply mul_nonneg
      · apply mul_nonneg; norm_num; exact Nat.cast_nonneg _
      · exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 288)
    · apply mul_nonneg
      · apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg _)
      · apply Real.log_nonneg
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ↑k)]
        calc (1 : ℝ) * (2 * ↑k) = 2 * ↑k := one_mul _
          _ ≤ ↑d := by exact_mod_cast (show 2 * k ≤ d by omega)
          _ ≤ Real.exp 1 * ↑d := le_mul_of_one_le_left (by positivity)
              (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1))
  have hlog_pos : 0 < Real.log (1 / delta) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hdelta), Real.log_one, zero_sub]
    exact neg_pos.mpr (Real.log_neg hdelta hdelta1)
  have hT_pos : 0 < T := by linarith
  have h2Tn_nonneg : 0 ≤ 2 * T / ↑n := div_nonneg (by linarith) (le_of_lt hn_pos)


  have h_r_ge1 : r ≥ 32 * Real.sqrt (2 * T / ↑n) := by
    rw [hr_def]; unfold sparsePCARate; simp only; exact le_max_left _ _
  have h_r_ge2 : r ≥ 64 * T / ↑n := by
    rw [hr_def]; unfold sparsePCARate; simp only; exact le_max_right _ _
  have h_rdiv_ge_sqrt : r / 32 ≥ Real.sqrt (2 * T / ↑n) := by linarith
  have h_sq : (r / 32) ^ 2 ≥ 2 * T / ↑n := by
    calc (r / 32) ^ 2 ≥ (Real.sqrt (2 * T / ↑n)) ^ 2 :=
          sq_le_sq' (by linarith [Real.sqrt_nonneg (2 * T / ↑n)]) h_rdiv_ge_sqrt
      _ = 2 * T / ↑n := Real.sq_sqrt h2Tn_nonneg
  have h_rdiv : r / 32 ≥ 2 * T / ↑n := by
    have h2 : 64 * T / ↑n / 32 ≤ r / 32 := div_le_div_of_nonneg_right h_r_ge2 (by norm_num)
    have h3 : 64 * T / ↑n / 32 = 2 * T / ↑n := by ring
    linarith

  have h_min : min ((r / 32) ^ 2) (r / 32) ≥ 2 * T / ↑n := le_min h_sq h_rdiv

  have h_nminhalf : ↑n / 2 * min ((r / 32) ^ 2) (r / 32) ≥ T := by
    calc ↑n / 2 * min ((r / 32) ^ 2) (r / 32) ≥ ↑n / 2 * (2 * T / ↑n) :=
          mul_le_mul_of_nonneg_left h_min (by linarith)
      _ = T := by field_simp

  have h_exp_le : L - ↑n / 2 * min ((r / 32) ^ 2) (r / 32) ≤ Real.log delta := by
    calc L - ↑n / 2 * min ((r / 32) ^ 2) (r / 32) ≤ L - T := by linarith
      _ = -Real.log (1 / delta) := by rw [hT_def]; ring
      _ = Real.log delta := by
          rw [Real.log_div one_ne_zero (ne_of_gt hdelta), Real.log_one, zero_sub, neg_neg]

  calc Real.exp (L - ↑n / 2 * min ((r / 32) ^ 2) (r / 32))
      ≤ Real.exp (Real.log delta) := Real.exp_le_exp.mpr h_exp_le
    _ = delta := Real.exp_log hdelta


/-- Distributivity of scalar multiplication over matrix-vector multiplication:
`(θ • M) * u = θ • (M * u)`. -/
lemma sparse_smul_mulVec_distrib (θ : ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (u : Fin d → ℝ) : (θ • M).mulVec u = θ • (M.mulVec u) := by
  ext i; simp [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext j; ring

/-- The action of a rank-one matrix on a vector: `(v vᵀ) x = ⟨v, x⟩ · v`. -/
lemma sparse_vecMulVec_self_mulVec (v x : Fin d → ℝ) :
    (vecMulVec v v).mulVec x = (dotProduct v x) • v := by
  ext i; simp [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf; rw [Finset.mul_sum]; congr 1; ext j; ring

/-- The quadratic form of `v vᵀ` on `x` equals `⟨v, x⟩²`. -/
lemma sparse_dotProduct_vecMulVec_self (v x : Fin d → ℝ) :
    dotProduct x ((vecMulVec v v).mulVec x) = (dotProduct v x) ^ 2 := by
  rw [sparse_vecMulVec_self_mulVec, dotProduct_smul, sq, dotProduct_comm x v]
  simp [smul_eq_mul]

/-- The Rayleigh quotient of the spiked-covariance matrix `θ v vᵀ + I` at `u` equals
`θ ⟨v, u⟩² + ⟨u, u⟩`. -/
lemma sparse_rayleigh_spiked_model (θ : ℝ) (v u : Fin d → ℝ) :
    dotProduct u ((θ • vecMulVec v v + (1 : Matrix (Fin d) (Fin d) ℝ)).mulVec u) =
    θ * (dotProduct v u) ^ 2 + dotProduct u u := by
  rw [add_mulVec, sparse_smul_mulVec_distrib, one_mulVec, dotProduct_add,
    dotProduct_smul, sparse_dotProduct_vecMulVec_self]
  simp [smul_eq_mul]

/-- For a symmetric matrix `M`, `⟨u, M w⟩ = ⟨w, M u⟩`. -/
lemma sparse_symmetric_dotProduct_mulVec (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : Mᵀ = M) (u w : Fin d → ℝ) :
    dotProduct u (M.mulVec w) = dotProduct w (M.mulVec u) := by
  rw [dotProduct_mulVec u M, ← mulVec_transpose M u]
  rw [hM]
  exact dotProduct_comm (M.mulVec u) w

/-- Bilinear-form identity for symmetric matrices:
`⟨u, Mu⟩ - ⟨w, Mw⟩ = ⟨u - w, M(u + w)⟩`. -/
lemma sparse_bilinear_identity (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : Mᵀ = M) (u w : Fin d → ℝ) :
    dotProduct u (M.mulVec u) - dotProduct w (M.mulVec w) =
    dotProduct (u - w) (M.mulVec (u + w)) := by
  have hsym := sparse_symmetric_dotProduct_mulVec M hM u w
  simp only [mulVec_add, dotProduct_add, sub_dotProduct]
  linarith

/-- The real inner product on `EuclideanSpace ℝ (Fin d)` agrees with the ordinary
dot product on the underlying functions. -/
lemma sparse_inner_eq_dotProduct (u v : EuclideanSpace ℝ (Fin d)) :
    @inner ℝ _ _ u v =
    dotProduct (EuclideanSpace.equiv (Fin d) ℝ u) (EuclideanSpace.equiv (Fin d) ℝ v) :=
  (EuclideanSpace.inner_eq_star_dotProduct u v).trans
    (by simp [star_trivial]; exact dotProduct_comm _ _)

/-- Applying `toEuclideanLin A` to `x` and projecting back via `ofLp` gives
ordinary matrix-vector multiplication. -/
lemma sparse_toEuclideanLin_ofLp (A : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    (toEuclideanLin A x).ofLp = A.mulVec x.ofLp := by
  simp [toEuclideanLin, toLpLin, LinearEquiv.trans_apply,
    LinearEquiv.arrowCongr_apply, WithLp.linearEquiv_symm_apply, toLin'_apply]

/-- `⟨u, toEuclideanLin A w⟩` equals the dot product `u.ofLp · (A * w.ofLp)`. -/
lemma sparse_inner_toEuclideanLin' (A : Matrix (Fin d) (Fin d) ℝ)
    (u w : EuclideanSpace ℝ (Fin d)) :
    @inner ℝ _ _ u (toEuclideanLin A w) =
    dotProduct u.ofLp (A.mulVec w.ofLp) := by
  rw [sparse_inner_eq_dotProduct u (toEuclideanLin A w)]
  show u.ofLp ⬝ᵥ (toEuclideanLin A w).ofLp = u.ofLp ⬝ᵥ A *ᵥ w.ofLp
  rw [sparse_toEuclideanLin_ofLp]

set_option maxHeartbeats 800000 in
/-- Bound on a bilinear form by the operator norm:
`|⟨u, A w⟩| ≤ ‖u‖ · ‖A‖ · ‖w‖`. -/
lemma sparse_abs_bilinear_le_opNorm (A : Matrix (Fin d) (Fin d) ℝ)
    (u w : EuclideanSpace ℝ (Fin d)) :
    |dotProduct u.ofLp (A.mulVec w.ofLp)| ≤ ‖u‖ * matOpNorm A * ‖w‖ := by
  rw [← sparse_inner_toEuclideanLin']
  set f := (toEuclideanLin A).toContinuousLinearMap
  have h_eq : toEuclideanLin A w = f w := rfl
  rw [h_eq]
  calc |@inner ℝ _ _ u (f w)|
      ≤ ‖u‖ * ‖f w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖f‖ * ‖w‖) := by
        apply mul_le_mul_of_nonneg_left (f.le_opNorm w) (norm_nonneg _)
    _ = ‖u‖ * matOpNorm A * ‖w‖ := by unfold matOpNorm; ring

/-- The spiked covariance matrix `θ v vᵀ + I` is symmetric. -/
lemma sparse_spiked_transpose_eq (θ : ℝ) (v : Fin d → ℝ) :
    (θ • outerProduct v + (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ =
    θ • outerProduct v + (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [transpose_add, transpose_smul]
  congr 1
  · congr 1; ext i j; simp [outerProduct, of_apply]; ring
  · exact transpose_one

set_option maxHeartbeats 3200000 in
/-- Davis–Kahan sine-squared bound in the sparse setting: if `v̂` is the `k`-sparse
largest eigenvector of `M_emp` (with `v` itself `k`-sparse), then the squared
sign-invariant distance is bounded by `(8/θ²) · ‖M_emp - M_pop‖²`. -/
lemma sparse_davis_kahan_sin_sq
    {d : ℕ} (M_pop M_emp : Matrix (Fin d) (Fin d) ℝ)
    (theta : ℝ) (htheta : 0 < theta)
    (v vhat : Fin d → ℝ)
    (hv_dot : dotProduct v v = 1)
    (hvhat_dot : dotProduct vhat vhat = 1)
    (hSpike : IsSpikedCovariance M_pop theta v)
    (hPSD : M_emp.PosSemidef)
    (k : ℕ) (hv_sparse : l0norm v ≤ k)
    (hvhat_eig : IsKSparseLargestEigenvector M_emp vhat k) :
    signInvariantDist vhat v ^ 2 ≤ 8 / theta ^ 2 * matOpNorm (M_emp - M_pop) ^ 2 := by

  set vtilde := (WithLp.toLp 2 vhat : EuclideanSpace ℝ (Fin d))
  set v' := (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))

  have hvt : ‖vtilde‖ = 1 := dotProduct_one_norm_one vhat hvhat_dot
  have hv_norm : ‖v'‖ = 1 := dotProduct_one_norm_one v hv_dot

  rw [signInvariantDist_sq_eq]

  have hLeft := Thm48.theorem_4_8_left vtilde v' hvt hv_norm


  set vf := v'.ofLp
  set vtf := vtilde.ofLp
  have hvf_eq : v'.ofLp = vf := rfl
  have hvtf_eq : vtilde.ofLp = vtf := rfl

  set c := @inner ℝ _ _ vtilde v'
  have h_abs_le : |c| ≤ 1 := by
    have := abs_real_inner_le_norm vtilde v'; rw [hvt, hv_norm] at this; linarith

  have h_sin : Real.sin (Thm48.principalAngle vtilde v') = Real.sqrt (1 - |c| ^ 2) := by
    unfold Thm48.principalAngle; exact Real.sin_arccos |c|
  have h_sin_sq : Real.sin (Thm48.principalAngle vtilde v') ^ 2 = 1 - c ^ 2 := by
    rw [h_sin, sq_sqrt (by nlinarith [abs_nonneg c, mul_self_nonneg (1 - |c|), mul_self_nonneg (1 + |c|)])]
    congr 1; rw [sq_abs]

  have hvf_unit : vf ⬝ᵥ vf = 1 := by
    show v'.ofLp ⬝ᵥ v'.ofLp = 1
    have h1 : @inner ℝ _ _ v' v' = ‖v'‖ ^ 2 := real_inner_self_eq_norm_sq v'
    have h2 := EuclideanSpace.inner_eq_star_dotProduct v' v'; simp [star_trivial] at h2
    rw [hv_norm] at h1; linarith [h2.symm.trans h1]
  have hvtf_unit : vtf ⬝ᵥ vtf = 1 := by
    show vtilde.ofLp ⬝ᵥ vtilde.ofLp = 1
    have h1 : @inner ℝ _ _ vtilde vtilde = ‖vtilde‖ ^ 2 := real_inner_self_eq_norm_sq vtilde
    have h2 := EuclideanSpace.inner_eq_star_dotProduct vtilde vtilde; simp [star_trivial] at h2
    rw [hvt] at h1; linarith [h2.symm.trans h1]


  have hSig : M_pop = theta • outerProduct v + (1 : Matrix (Fin d) (Fin d) ℝ) := hSpike

  have h_outer_eq : outerProduct v = vecMulVec v' v' := outerProduct_eq_vecMulVec v

  have h_rv : vf ⬝ᵥ M_pop.mulVec vf = 1 + theta := by
    rw [hSig]

    rw [h_outer_eq]
    rw [sparse_rayleigh_spiked_model theta v' vf]


    rw [← hvf_eq, hvf_unit]; ring

  have hvc : v'.ofLp ⬝ᵥ vtf = c := by
    have h_inner := sparse_inner_eq_dotProduct vtilde v'
    change c = vtf ⬝ᵥ vf at h_inner
    rw [hvf_eq, dotProduct_comm, ← h_inner]
  have h_rvt : vtf ⬝ᵥ M_pop.mulVec vtf = 1 + theta * c ^ 2 := by
    rw [hSig, h_outer_eq]
    rw [sparse_rayleigh_spiked_model theta v' vtf]
    rw [hvtf_unit, hvc]; ring

  have h_diff : vf ⬝ᵥ M_pop.mulVec vf - vtf ⬝ᵥ M_pop.mulVec vtf =
      theta * (1 - c ^ 2) := by rw [h_rv, h_rvt]; ring


  have h_eig_ineq : vf ⬝ᵥ M_emp.mulVec vf ≤ vtf ⬝ᵥ M_emp.mulVec vtf := by
    exact hvhat_eig.2.2 v hv_dot hv_sparse

  set Δ := M_emp - M_pop

  have hSigSym : M_popᵀ = M_pop := by rw [hSig]; exact sparse_spiked_transpose_eq theta v
  have hSTSym : M_empᵀ = M_emp := by exact_mod_cast hPSD.1
  have hΔsym : Δᵀ = Δ := by
    show (M_emp - M_pop)ᵀ = M_emp - M_pop
    rw [transpose_sub, hSTSym, hSigSym]

  have h_decomp_v : vf ⬝ᵥ M_emp.mulVec vf =
      vf ⬝ᵥ M_pop.mulVec vf + vf ⬝ᵥ Δ.mulVec vf := by
    have : M_emp = M_pop + Δ := by simp [Δ]
    rw [this, add_mulVec, dotProduct_add]
  have h_decomp_vt : vtf ⬝ᵥ M_emp.mulVec vtf =
      vtf ⬝ᵥ M_pop.mulVec vtf + vtf ⬝ᵥ Δ.mulVec vtf := by
    have : M_emp = M_pop + Δ := by simp [Δ]
    rw [this, add_mulVec, dotProduct_add]

  have h_rayleigh_bound : theta * (1 - c ^ 2) ≤
      vtf ⬝ᵥ Δ.mulVec vtf - vf ⬝ᵥ Δ.mulVec vf := by
    rw [h_decomp_v, h_decomp_vt] at h_eig_ineq
    linarith [h_diff]

  have h_bilinear : vtf ⬝ᵥ Δ.mulVec vtf - vf ⬝ᵥ Δ.mulVec vf =
      (vtf - vf) ⬝ᵥ Δ.mulVec (vtf + vf) :=
    sparse_bilinear_identity Δ hΔsym vtf vf

  have h_cs_bound : (vtf - vf) ⬝ᵥ Δ.mulVec (vtf + vf) ≤
      ‖vtilde - v'‖ * matOpNorm Δ * ‖vtilde + v'‖ := by
    calc (vtf - vf) ⬝ᵥ Δ.mulVec (vtf + vf)
        ≤ |(vtf - vf) ⬝ᵥ Δ.mulVec (vtf + vf)| := le_abs_self _
      _ ≤ ‖vtilde - v'‖ * matOpNorm Δ * ‖vtilde + v'‖ :=
          sparse_abs_bilinear_le_opNorm Δ (vtilde - v') (vtilde + v')

  have h_norm_sub_sq : ‖vtilde - v'‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq_real, hvt, hv_norm]; ring
  have h_norm_add_sq : ‖vtilde + v'‖ ^ 2 = 2 + 2 * c := by
    rw [norm_add_sq_real, hvt, hv_norm]; ring

  have h_norm_prod_sq : ‖vtilde - v'‖ ^ 2 * ‖vtilde + v'‖ ^ 2 =
      4 * (1 - c ^ 2) := by
    rw [h_norm_sub_sq, h_norm_add_sq]; ring
  have h_norm_sub_nn : 0 ≤ ‖vtilde - v'‖ := norm_nonneg _
  have h_norm_add_nn : 0 ≤ ‖vtilde + v'‖ := norm_nonneg _
  have h_op_nn : 0 ≤ matOpNorm Δ := matOpNorm_nonneg _

  by_cases hc_eq : 1 - c ^ 2 = 0
  ·
    have hc_sq : c ^ 2 = 1 := by linarith


    have h_abs_c : |c| = 1 := by
      have := sq_abs c
      have h_nn := abs_nonneg c
      nlinarith [mul_self_nonneg (|c| - 1)]

    have h_min_zero : min (‖vtilde - v'‖ ^ 2) (‖vtilde + v'‖ ^ 2) = 0 := by
      rcases abs_cases c with ⟨hc_pos, _⟩ | ⟨hc_neg, _⟩
      ·
        rw [hc_pos] at h_abs_c
        rw [h_norm_sub_sq, h_norm_add_sq, h_abs_c]
        simp
      ·
        rw [hc_neg] at h_abs_c
        have : c = -1 := by linarith
        rw [h_norm_sub_sq, h_norm_add_sq, this]
        simp
    rw [h_min_zero]; positivity
  ·
    have h1mc2_pos : 0 < 1 - c ^ 2 := by
      by_contra h_neg
      push Not at h_neg
      have : 1 - c^2 = 0 := le_antisymm h_neg
        (by nlinarith [sq_abs c, abs_nonneg c, mul_self_nonneg (1 - |c|), mul_self_nonneg (1 + |c|)])
      exact hc_eq this

    have h_combined : theta * (1 - c ^ 2) ≤
        ‖vtilde - v'‖ * matOpNorm Δ * ‖vtilde + v'‖ := by
      linarith [h_rayleigh_bound, h_bilinear, h_cs_bound]

    have h_norm_prod : ‖vtilde - v'‖ * ‖vtilde + v'‖ =
        2 * Real.sqrt (1 - c ^ 2) := by
      have h1 : (‖vtilde - v'‖ * ‖vtilde + v'‖) ^ 2 =
          (2 * Real.sqrt (1 - c ^ 2)) ^ 2 := by
        rw [mul_pow, mul_pow]
        rw [Real.sq_sqrt (le_of_lt h1mc2_pos)]
        linarith [h_norm_prod_sq]
      have h_lhs_nn : 0 ≤ ‖vtilde - v'‖ * ‖vtilde + v'‖ :=
        mul_nonneg h_norm_sub_nn h_norm_add_nn
      have h_rhs_nn : 0 ≤ 2 * Real.sqrt (1 - c ^ 2) := by positivity
      nlinarith [sq_nonneg (‖vtilde - v'‖ * ‖vtilde + v'‖ - 2 * Real.sqrt (1 - c ^ 2))]

    have h_bound1 : theta * (1 - c ^ 2) ≤
        2 * Real.sqrt (1 - c ^ 2) * matOpNorm Δ := by
      have : ‖vtilde - v'‖ * matOpNorm Δ * ‖vtilde + v'‖ =
          (‖vtilde - v'‖ * ‖vtilde + v'‖) * matOpNorm Δ := by ring
      rw [this, h_norm_prod] at h_combined
      linarith

    have h_sqrt_pos : 0 < Real.sqrt (1 - c ^ 2) := Real.sqrt_pos.mpr h1mc2_pos
    have h_bound2 : theta * Real.sqrt (1 - c ^ 2) ≤ 2 * matOpNorm Δ := by
      have h1mc2_eq : 1 - c ^ 2 = Real.sqrt (1 - c ^ 2) * Real.sqrt (1 - c ^ 2) :=
        (Real.mul_self_sqrt (le_of_lt h1mc2_pos)).symm


      have key : theta * Real.sqrt (1 - c ^ 2) * Real.sqrt (1 - c ^ 2) ≤
          2 * matOpNorm Δ * Real.sqrt (1 - c ^ 2) := by
        nlinarith [h1mc2_eq]
      exact le_of_mul_le_mul_right key h_sqrt_pos


    have h_sin_bound : Real.sqrt (1 - c ^ 2) ≤ 2 / theta * matOpNorm Δ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ htheta]
      linarith

    have h_sq_bound : 1 - c ^ 2 ≤ (2 / theta * matOpNorm Δ) ^ 2 := by
      calc 1 - c ^ 2 = Real.sqrt (1 - c ^ 2) ^ 2 := by
            rw [Real.sq_sqrt (le_of_lt h1mc2_pos)]
        _ ≤ (2 / theta * matOpNorm Δ) ^ 2 :=
            sq_le_sq' (by nlinarith [Real.sqrt_nonneg (1 - c ^ 2)]) h_sin_bound

    have h_two_sin_sq : 2 * (1 - c ^ 2) ≤ 8 / theta ^ 2 * matOpNorm Δ ^ 2 := by
      calc 2 * (1 - c ^ 2) ≤ 2 * (2 / theta * matOpNorm Δ) ^ 2 := by linarith
        _ = 8 / theta ^ 2 * matOpNorm Δ ^ 2 := by ring


    calc min (‖vtilde - v'‖ ^ 2) (‖vtilde + v'‖ ^ 2)
        ≤ 2 * Real.sin (Thm48.principalAngle vtilde v') ^ 2 := hLeft
      _ = 2 * (1 - c ^ 2) := by rw [h_sin_sq]
      _ ≤ 8 / theta ^ 2 * matOpNorm Δ ^ 2 := h_two_sin_sq
      _ = 8 / theta ^ 2 * matOpNorm (M_emp - M_pop) ^ 2 := rfl

/-- Sparse Davis–Kahan bound packaged with an external rate hypothesis:
`d(v̂, v) ≤ C · ((1 + θ)/θ) · rate`. -/
lemma sparse_davis_kahan_submatrix_bound
    {d : ℕ} (M_pop M_emp : Matrix (Fin d) (Fin d) ℝ)
    (theta : ℝ) (htheta : 0 < theta)
    (v vhat : Fin d → ℝ)
    (hv_dot : dotProduct v v = 1)
    (hvhat_dot : dotProduct vhat vhat = 1)
    (hSpike : IsSpikedCovariance M_pop theta v)
    (hPSD : M_emp.PosSemidef)
    (k : ℕ) (hv_sparse : l0norm v ≤ k)
    (hvhat_eig : IsKSparseLargestEigenvector M_emp vhat k)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hbound : matOpNorm (M_emp - M_pop) ≤ matOpNorm M_pop * rate) :
    signInvariantDist vhat v ≤
      sparse_pca_C * ((1 + theta) / theta) * rate := by

  have hsq := sparse_davis_kahan_sin_sq M_pop M_emp theta htheta v vhat
    hv_dot hvhat_dot hSpike hPSD k hv_sparse hvhat_eig

  have hpop_norm := spiked_covariance_opnorm M_pop theta htheta v hv_dot hSpike

  have h_op_bound : matOpNorm (M_emp - M_pop) ≤ (1 + theta) * rate := by
    calc matOpNorm (M_emp - M_pop) ≤ matOpNorm M_pop * rate := hbound
      _ = (1 + theta) * rate := by rw [hpop_norm]

  have hsq2 : signInvariantDist vhat v ^ 2 ≤ 8 / theta ^ 2 * ((1 + theta) * rate) ^ 2 := by
    calc signInvariantDist vhat v ^ 2
        ≤ 8 / theta ^ 2 * matOpNorm (M_emp - M_pop) ^ 2 := hsq
      _ ≤ 8 / theta ^ 2 * ((1 + theta) * rate) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sq_le_sq' (by linarith [matOpNorm_nonneg (M_emp - M_pop)]) h_op_bound

  have hsd_nn := signInvariantDist_nonneg vhat v
  have h_rhs_nn : 0 ≤ sparse_pca_C * ((1 + theta) / theta) * rate := by
    apply mul_nonneg (mul_nonneg (le_of_lt sparse_pca_C_pos) _) hrate
    exact div_nonneg (by linarith) (le_of_lt htheta)
  rw [← Real.sqrt_sq hsd_nn, ← Real.sqrt_sq h_rhs_nn]
  apply Real.sqrt_le_sqrt
  calc signInvariantDist vhat v ^ 2
      ≤ 8 / theta ^ 2 * ((1 + theta) * rate) ^ 2 := hsq2
    _ ≤ (sparse_pca_C * ((1 + theta) / theta) * rate) ^ 2 := by
        have htheta_ne : theta ≠ 0 := ne_of_gt htheta

        have hrhs : (sparse_pca_C * ((1 + theta) / theta) * rate) ^ 2 =
            9 * ((1 + theta) * rate) ^ 2 / theta ^ 2 := by
          unfold sparse_pca_C; field_simp; ring
        rw [hrhs]

        have hlhs : 8 / theta ^ 2 * ((1 + theta) * rate) ^ 2 =
            8 * ((1 + theta) * rate) ^ 2 / theta ^ 2 := by ring
        rw [hlhs]

        apply div_le_div_of_nonneg_right _ (le_of_lt (by positivity : (0 : ℝ) < theta ^ 2))
        nlinarith [sq_nonneg ((1 + theta) * rate)]

/-- Deterministic sparse-PCA bound: if the operator-norm deviation is bounded by
`‖Σ‖ · sparsePCARate d k n δ`, then the recovered eigenvector satisfies the sparse PCA
guarantee `d(v̂, v) ≤ C ((1 + θ)/θ) · sparsePCARate d k n δ`. -/
theorem sparse_pca_deterministic_bound
    {d : ℕ} {n : ℕ} {Omega : Type*}
    (X : Fin n → Omega → Fin d → ℝ)
    (covMat : Matrix (Fin d) (Fin d) ℝ)
    (theta : ℝ) (htheta : 0 < theta)
    (v : Fin d → ℝ)
    (hv_dot : dotProduct v v = 1)
    (hSpike : IsSpikedCovariance covMat theta v)
    (k : ℕ) (hk_pos : 0 < k)
    (hv_sparse : l0norm v = k)
    (vhat : Omega → Fin d → ℝ)
    (hvhat : ∀ omega, IsKSparseLargestEigenvector (empiricalCov X omega) (vhat omega) k)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ omega : Omega,
      matOpNorm (empiricalCov X omega - covMat) ≤
        matOpNorm covMat * sparsePCARate d k n delta →
      signInvariantDist (vhat omega) v ≤
        sparse_pca_C * ((1 + theta) / theta) * sparsePCARate d k n delta := by
  intro omega h_opnorm
  have hvhat_omega := hvhat omega
  have hvhat_dot : dotProduct (vhat omega) (vhat omega) = 1 := hvhat_omega.1
  exact sparse_davis_kahan_submatrix_bound covMat (empiricalCov X omega)
    theta htheta v (vhat omega) hv_dot hvhat_dot hSpike
    (empiricalCov_posSemidef X omega) k (le_of_eq hv_sparse) hvhat_omega
    (sparsePCARate d k n delta) (sparsePCARate_nonneg d k n delta) h_opnorm




/-- Textbook form of the sparse PCA rate (without the universal constants):
`max(√(t/n), t/n)` for `t = k log(e d/k) + log(1/δ)`. -/
def sparsePCARate_textbook (d k n : ℕ) (delta : ℝ) : ℝ :=
  let t := (k : ℝ) * Real.log (Real.exp 1 * (d : ℝ) / (k : ℝ)) + Real.log (1 / delta)
  max (Real.sqrt (t / (n : ℝ))) (t / (n : ℝ))

/-- The textbook sparse PCA rate is nonnegative. -/
lemma sparsePCARate_textbook_nonneg (d k n : ℕ) (delta : ℝ) :
    0 ≤ sparsePCARate_textbook d k n delta := by
  unfold sparsePCARate_textbook; simp only
  exact le_max_of_le_left (Real.sqrt_nonneg _)

/-- Comparison: the explicit `sparsePCARate` is bounded by a universal multiple
(896) of the textbook rate. -/
lemma sparsePCARate_le_mul_textbook (d k n : ℕ) (delta : ℝ)
    (hk : 1 ≤ k) (hkd : k ≤ d) (hn : 1 ≤ n)
    (hδ_pos : 0 < delta) (hδ_lt : delta < 1) :
    sparsePCARate d k n delta ≤ 896 * sparsePCARate_textbook d k n delta := by
  unfold sparsePCARate sparsePCARate_textbook
  simp only

  set t := (2 * (k : ℝ)) * log 288 + (2 * (k : ℝ)) * log (rexp 1 * ↑d / (2 * ↑k)) +
    log (1 / delta) with ht_def
  set t' := (k : ℝ) * log (rexp 1 * ↑d / ↑k) + log (1 / delta) with ht'_def
  have hK : (0:ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
  have hD : (0:ℝ) < ↑d := Nat.cast_pos.mpr (by omega)
  have hDE : (0:ℝ) < rexp 1 * ↑d := mul_pos (exp_pos 1) hD
  have hn_pos : (0:ℝ) < ↑n := Nat.cast_pos.mpr (by omega)

  have h_t_bound : t ≤ 14 * t' := by
    simp only [ht_def, ht'_def]
    have h_log288 : log 288 ≤ 6 := by
      rw [log_le_iff_le_exp (by norm_num : (288:ℝ) > 0)]
      have h0 := Real.sum_le_exp_of_nonneg (by norm_num : (6:ℝ) ≥ 0) 8
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h0
      norm_num at h0 ⊢; linarith
    have h_log_mono : log (rexp 1 * ↑d / (2 * ↑k)) ≤ log (rexp 1 * ↑d / ↑k) := by
      apply log_le_log (div_pos hDE (by linarith))
      exact div_le_div_of_nonneg_left hDE.le hK (by linarith)
    have h_log_ge_1 : 1 ≤ log (rexp 1 * ↑d / ↑k) := by
      rw [le_log_iff_exp_le (by positivity), le_div_iff₀ hK]
      nlinarith [exp_pos 1, (Nat.cast_le (α := ℝ)).mpr hkd]
    have h_log_delta : 0 ≤ log (1 / delta) := by
      apply log_nonneg; rw [le_div_iff₀ hδ_pos]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h_log288 (show 0 ≤ 2 * (↑k : ℝ) by linarith),
               mul_le_mul_of_nonneg_left h_log_mono (show 0 ≤ 2 * (↑k : ℝ) by linarith),
               mul_le_mul_of_nonneg_right h_log_ge_1 (show 0 ≤ 12 * (↑k : ℝ) by linarith)]

  have h_t'_nonneg : 0 ≤ t' := by
    simp only [ht'_def]
    have : 0 ≤ log (rexp 1 * ↑d / ↑k) := by
      apply log_nonneg; rw [le_div_iff₀ hK]
      nlinarith [exp_pos 1, (Nat.cast_le (α := ℝ)).mpr hkd,
                 one_le_exp (show (0:ℝ) ≤ 1 by norm_num)]
    have : 0 ≤ log (1 / delta) := by
      apply log_nonneg; rw [le_div_iff₀ hδ_pos]; linarith
    positivity

  apply max_le
  ·
    calc 32 * sqrt (2 * t / ↑n)
        ≤ 896 * sqrt (t' / ↑n) := by
          suffices h : sqrt (2 * t / ↑n) ≤ 28 * sqrt (t' / ↑n) by
            calc 32 * sqrt _ ≤ 32 * (28 * sqrt _) :=
                  mul_le_mul_of_nonneg_left h (by norm_num)
              _ = 896 * sqrt _ := by ring
          rw [← sqrt_sq (show (28:ℝ) ≥ 0 by norm_num), ← sqrt_mul (by positivity)]
          apply sqrt_le_sqrt
          calc 2 * t / ↑n ≤ 784 * t' / ↑n :=
                div_le_div_of_nonneg_right (by nlinarith) hn_pos.le
            _ = 28 ^ 2 * (t' / ↑n) := by ring
      _ ≤ 896 * max (sqrt (t' / ↑n)) (t' / ↑n) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  ·
    calc 64 * t / ↑n
        ≤ 896 * t' / ↑n := div_le_div_of_nonneg_right (by nlinarith) hn_pos.le
      _ = 896 * (t' / ↑n) := mul_div_assoc _ _ _
      _ ≤ 896 * max (sqrt (t' / ↑n)) (t' / ↑n) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)


end

end Rigollet.Chapter4.Thm_4_10
