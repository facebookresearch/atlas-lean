/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Matrix.LDL
import Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_8
import Atlas.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
import Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_6

open MeasureTheory Matrix Real Finset BigOperators ProbabilityTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option linter.unusedVariables false

namespace Cor49

variable {d : ℕ}

/-- A `d × d` real matrix `S` is a *spiked covariance* with signal strength `θ > 0` along the
unit direction `v ∈ ℝ^d` if `S = θ · v v^⊤ + I_d`. This is the matrix appearing in the PCA
model of Corollary 4.9. -/
def IsSpikedCovariance (S : Matrix (Fin d) (Fin d) ℝ) (θ : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : Prop :=
  0 < θ ∧ ‖v‖ = 1 ∧ S = θ • (vecMulVec v v) + (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The operator (L²) norm of a real square matrix `A`, defined via the associated continuous
linear map on Euclidean space. -/
noncomputable def matrixOpNorm (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- The empirical (sample) covariance matrix
`Σ̂(ω) = (1/n) Σᵢ Xᵢ(ω) Xᵢ(ω)^⊤` of `n` Euclidean-vector-valued samples `X₁, …, Xₙ`. -/
def empiricalCovariance {n : ℕ} {Ω : Type*}
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / (n : ℝ)) • ∑ i : Fin n, Matrix.of (fun (j k : Fin d) => X i ω j * X i ω k)

/-- A unit vector `w` is a *largest eigenvector* of the matrix `M` if it maximises the Rayleigh
quotient `⟨u, Mu⟩` over all unit vectors `u`. -/
def IsLargestEigenvector
    (M : Matrix (Fin d) (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) : Prop :=
  ‖w‖ = 1 ∧
  ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
    dotProduct (EuclideanSpace.equiv (Fin d) ℝ u)
      (M.mulVec (EuclideanSpace.equiv (Fin d) ℝ u)) ≤
    dotProduct (EuclideanSpace.equiv (Fin d) ℝ w)
      (M.mulVec (EuclideanSpace.equiv (Fin d) ℝ w))

/-- A Euclidean-vector valued random variable `X` is sub-Gaussian with proxy variance `σ²`
(written `X ~ subG_d(σ²)`) if for every unit vector `u`, the projection `⟨u, X⟩` is a
scalar sub-Gaussian random variable with proxy variance `σ²`, both for the Bochner and the
lower-Lebesgue MGF bound. -/
def IsSubGaussianVec {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin d)) (σsq : ℝ) : Prop :=
  AEMeasurable X μ ∧
  (∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    ∀ (s : ℝ),
      ∫ ω, Real.exp (s * (∑ j : Fin d, u j * X ω j)) ∂μ ≤
        Real.exp (σsq * s ^ 2 / 2)) ∧
  (∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    ∀ (s : ℝ),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (∑ j : Fin d, u j * X ω j))) ∂μ ≤
        ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2)))

/-- The covariance estimation rate `√((d + log(1/δ))/n) ∨ (d + log(1/δ))/n` that controls the
operator-norm error of the empirical covariance matrix. -/
def covRate (d₀ n : ℕ) (delta : ℝ) : ℝ :=
  let t := (d₀ : ℝ) + Real.log (1 / delta)
  max (Real.sqrt (t / (n : ℝ))) (t / (n : ℝ))

/-- The universal constant `C₁ = 1024` appearing in the operator-norm concentration bound
for the empirical covariance matrix. -/
noncomputable def opNorm_concentration_C₁ : ℝ := 1024
/-- The universal constant `opNorm_concentration_C₁` is strictly positive. -/
theorem opNorm_concentration_C₁_pos : 0 < opNorm_concentration_C₁ := by
  unfold opNorm_concentration_C₁; norm_num

/-- ε-net reduction for the operator norm: there exists a finite set `N` of unit-ball points in
`ℝ^d` with cardinality at most `12^d` such that whenever `‖A‖_op > t`, some pair of net points
witnesses `|⟨x, A y⟩| > t/2`. This is the standard `1/4`-net argument used in Theorem 4.6. -/
theorem eps_net_opnorm_reduction_L2 (hd : 0 < d) :
    ∃ (N : Finset (EuclideanSpace ℝ (Fin d))),
      (N.card : ℝ) ≤ (12 : ℝ) ^ d ∧
      N.Nonempty ∧
      (∀ x ∈ N, ‖x‖ ≤ 1) ∧
      (∀ (A : Matrix (Fin d) (Fin d) ℝ) (t : ℝ),
        matrixOpNorm A > t →
        ∃ x ∈ N, ∃ y ∈ N,
          |dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
            (A.mulVec (EuclideanSpace.equiv (Fin d) ℝ y))| > t / 2) := by

  have hε_pos : (0 : ℝ) < 1 / 4 := by norm_num
  have hε_lt : (1 : ℝ) / 4 < 1 := by norm_num
  obtain ⟨N, hN_net, hN_card⟩ := lemma_1_18_covering_number_euclidean_ball hd (1/4) hε_pos hε_lt

  have hN_sub : ∀ x ∈ N, ‖x‖ ≤ 1 := by
    intro x hx
    have := hN_net.subset_set (Finset.mem_coe.mpr hx)
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hN_cover : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      ∃ x ∈ N, dist u x ≤ 1/4 := by
    intro u hu
    have hu_ball : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith [hu.symm.le]
    obtain ⟨x, hxN, hdist⟩ := hN_net.exists_dist_le hu_ball
    exact ⟨x, Finset.mem_coe.mp hxN, dist_comm x u ▸ hdist⟩

  have hN_ne : N.Nonempty := by
    have : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_closedBall]; simp
    obtain ⟨x, hxN, _⟩ := hN_net.exists_dist_le this
    exact ⟨x, Finset.mem_coe.mp hxN⟩

  have hN_card_bound : (N.card : ℝ) ≤ (12 : ℝ) ^ d := by
    have h12 : (3 : ℝ) / (1 / 4) = 12 := by norm_num
    have h12d : ((3 : ℝ) / (1 / 4)) ^ d = (12 : ℝ) ^ d := by rw [h12]
    calc (N.card : ℝ) ≤ ↑(Nat.ceil ((3 / (1/4)) ^ d)) := Nat.cast_le.mpr hN_card
      _ = ↑(Nat.ceil ((12 : ℝ) ^ d)) := by rw [h12d]
      _ = (12 : ℝ) ^ d := by
          have h12 : (12 : ℝ) = ↑(12 : ℕ) := by norm_num
          conv_lhs => rw [h12, ← Nat.cast_pow, Nat.ceil_natCast, Nat.cast_pow, ← h12]

  refine ⟨N, hN_card_bound, hN_ne, hN_sub, ?_⟩
  intro A t hAt

  by_contra h_neg
  push Not at h_neg


  have h_bound : ∀ x ∈ N, ∀ y ∈ N,
      dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
        (A.mulVec (EuclideanSpace.equiv (Fin d) ℝ y)) ≤ t / 2 := by
    intro x hx y hy
    exact le_of_abs_le (h_neg x hx y hy)

  have h42 : _root_.matrixOpNorm A ≤ 2 * (t / 2) :=
    lemma_4_2_eps_net_reduction A hN_cover hN_cover hN_sub hN_sub hN_ne hN_ne (t / 2) h_bound

  have h_eq : _root_.matrixOpNorm A = matrixOpNorm A := rfl
  rw [h_eq] at h42
  linarith

/-- Convert a family of Euclidean-space-valued random variables to "plain" `Fin d → ℝ`-valued
random variables by forgetting the `L²` structure. -/
def toPlainVec {n : ℕ} {Ω : Type*}
    (Y : Fin n → Ω → EuclideanSpace ℝ (Fin d)) : Fin n → Ω → Fin d → ℝ :=
  fun i ω j => Y i ω j

/-- Bridge lemma: a sub-Gaussian Euclidean-space random vector remains sub-Gaussian when
viewed through `WithLp.equiv` as a plain `Fin d → ℝ` random vector. -/
lemma isSubGaussianVec_bridge {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → EuclideanSpace ℝ (Fin d)) :
    IsSubGaussianVec μ Z 1 →
    Rigollet.Chapter4.Thm_4_6.IsSubGaussianVec μ (fun ω j => Z ω j) 1 := by
  intro ⟨hAE, hMGF, hMGF_lint⟩
  refine ⟨?_, hMGF, hMGF_lint⟩
  change AEMeasurable ((WithLp.equiv 2 (Fin d → ℝ)) ∘ Z) μ
  exact (EuclideanSpace.equiv (Fin d) ℝ).continuous.measurable.comp_aemeasurable hAE

/-- A vector with Euclidean (`L²`) norm at most `1` also has supremum (`L∞`) norm at most `1`. -/
lemma norm_plain_le_euclidean (x : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ ≤ 1) :
    ‖(fun j => x j : Fin d → ℝ)‖ ≤ 1 := by
  apply pi_norm_le_iff_of_nonneg (by linarith) |>.mpr
  intro j
  calc ‖x j‖ = |x.ofLp j| := rfl
    _ ≤ √(∑ i, ‖x.ofLp i‖ ^ 2) := by
        rw [Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
        calc |x.ofLp j| ^ 2 = ‖x.ofLp j‖ ^ 2 := by rw [Real.norm_eq_abs]
          _ ≤ ∑ i, ‖x.ofLp i‖ ^ 2 := by
              apply Finset.single_le_sum (f := fun i => ‖x.ofLp i‖ ^ 2)
              · intro i _; exact sq_nonneg _
              · exact Finset.mem_univ j
    _ = ‖x‖ := (EuclideanSpace.norm_eq x).symm
    _ ≤ 1 := hx

/-- A sub-Gaussian random vector is almost-everywhere strongly measurable. -/
theorem subGaussianVec_aestronglyMeasurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (σsq : ℝ)
    (hSubG : IsSubGaussianVec μ X σsq) : AEStronglyMeasurable X μ :=
  hSubG.1.aestronglyMeasurable



/-- Apply a matrix `M` to a Euclidean-space vector `x`, transporting through `WithLp.equiv`. -/
def applyMatrix (M : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (M *ᵥ (WithLp.equiv 2 (Fin d → ℝ) x))

/-- Componentwise formula: `(applyMatrix M x) j = Σᵢ M j i · x i`. -/
lemma applyMatrix_apply (M : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    (applyMatrix M x) j = ∑ i, M j i * x i := by
  simp [applyMatrix, WithLp.equiv, mulVec, dotProduct]

/-- The componentwise sum `Σⱼ uⱼ · xⱼ` equals the Euclidean inner product `⟨u, x⟩`. -/
lemma sum_eq_inner (u x : EuclideanSpace ℝ (Fin d)) :
    ∑ j : Fin d, u j * x j = @inner ℝ _ _ u x := by
  simp only [PiLp.inner_apply]; congr 1; ext j; simp [inner, mul_comm]

/-- Transpose adjoint identity in the Euclidean inner product:
`⟨θ, M x⟩ = ⟨M^⊤ θ, x⟩`. -/
lemma inner_applyMatrix_eq_inner_transpose
    (M : Matrix (Fin d) (Fin d) ℝ) (θ x : EuclideanSpace ℝ (Fin d)) :
    @inner ℝ _ _ θ (applyMatrix M x) = @inner ℝ _ _ (applyMatrix M.transpose θ) x := by
  simp only [applyMatrix, inner, starRingEnd_apply, star_trivial, RCLike.re_to_real,
    WithLp.equiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  change dotProduct (M.mulVec x.ofLp) θ.ofLp = dotProduct x.ofLp (M.transpose.mulVec θ.ofLp)
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm]
  congr 1
  rw [← vecMul_transpose M.transpose θ.ofLp, transpose_transpose]

/-- `applyMatrix` agrees with the standard `Matrix.toEuclideanLin` linear map. -/
lemma applyMatrix_eq_toEuclideanLin
    (M : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    applyMatrix M x = (toEuclideanLin M) x := by
  simp [applyMatrix, toEuclideanLin]; rfl

/-- The `matrixOpNorm` defined here equals the Mathlib `L²` operator norm `‖M‖`. -/
lemma matrixOpNorm_eq_norm (M : Matrix (Fin d) (Fin d) ℝ) : matrixOpNorm M = ‖M‖ := by
  simp only [matrixOpNorm, l2_opNorm_def, LinearEquiv.trans_apply]

/-- Over the reals, the matrix transpose coincides with the conjugate transpose. -/
lemma real_transpose_eq_conjTranspose (M : Matrix (Fin d) (Fin d) ℝ) :
    M.transpose = M.conjTranspose := by
  ext i j; simp [conjTranspose_apply, star_trivial]

/-- Operator norm bound: `‖M^⊤ θ‖ ≤ ‖M‖_op · ‖θ‖`. -/
lemma norm_applyMatrix_transpose_le
    (M : Matrix (Fin d) (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    ‖applyMatrix M.transpose θ‖ ≤ matrixOpNorm M * ‖θ‖ := by
  rw [applyMatrix_eq_toEuclideanLin]
  have h2 : (toEuclideanLin M.transpose) θ =
      (toEuclideanLin M.transpose).toContinuousLinearMap θ := rfl
  rw [h2]
  calc ‖(toEuclideanLin M.transpose).toContinuousLinearMap θ‖
      ≤ ‖(toEuclideanLin M.transpose).toContinuousLinearMap‖ * ‖θ‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = matrixOpNorm M.transpose * ‖θ‖ := by rw [matrixOpNorm]
    _ = ‖M.transpose‖ * ‖θ‖ := by rw [matrixOpNorm_eq_norm]
    _ = ‖M.conjTranspose‖ * ‖θ‖ := by rw [real_transpose_eq_conjTranspose]
    _ = ‖M‖ * ‖θ‖ := by rw [l2_opNorm_conjTranspose]
    _ = matrixOpNorm M * ‖θ‖ := by rw [matrixOpNorm_eq_norm]

/-- Coordinate version of the transpose adjoint identity:
`Σⱼ uⱼ (M x)ⱼ = Σⱼ (M^⊤ u)ⱼ xⱼ`. -/
lemma sum_applyMatrix_eq (M : Matrix (Fin d) (Fin d) ℝ) (u x : EuclideanSpace ℝ (Fin d)) :
    ∑ j : Fin d, u j * (applyMatrix M x) j =
    ∑ j : Fin d, (applyMatrix M.transpose u) j * x j := by
  rw [sum_eq_inner, inner_applyMatrix_eq_inner_transpose, ← sum_eq_inner]

/-- For all real `x`, `x² ≤ e^x + e^(-x) = 2 cosh x`. -/
lemma sq_le_exp_add_exp_neg (x : ℝ) : x ^ 2 ≤ exp x + exp (-x) := by
  rw [show exp x + exp (-x) = 2 * cosh x from by rw [Real.cosh_eq]; ring]
  have hs := Real.hasSum_cosh x
  have h_nn : ∀ n, 0 ≤ x ^ (2 * n) / ↑(2 * n).factorial := by
    intro n
    apply div_nonneg (Even.pow_nonneg ⟨n, by ring⟩ x) (Nat.cast_nonneg' _)
  have h_le : 1 + x ^ 2 / 2 ≤ cosh x := by
    rw [hs.tsum_eq.symm]
    calc 1 + x ^ 2 / 2
        = ∑ i ∈ range 2, x ^ (2 * i) / ↑(2 * i).factorial := by
          simp [Finset.sum_range_succ, Nat.factorial]
      _ ≤ ∑' n, x ^ (2 * n) / ↑(2 * n).factorial :=
          hs.summable.sum_le_tsum (range 2) (fun n _ => h_nn n)
  linarith

/-- A coordinate of a sub-Gaussian random vector lies in `L²(μ)` (square-integrable). -/
theorem subgaussian_component_memLp_two :
    ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (σsq : ℝ)
    (_ : IsSubGaussianVec μ X σsq)
    (a : Fin d)
    (_ : AEStronglyMeasurable (fun ω => X ω a) μ)
    (_ : Integrable (fun ω => exp (X ω a)) μ)
    (_ : Integrable (fun ω => exp (-(X ω a))) μ),
    MemLp (fun ω => X ω a) 2 μ := by
  intro d Ω inst μ hP X σsq _hSG a hm hint_pos hint_neg
  rw [memLp_two_iff_integrable_sq hm]
  have hdom : Integrable (fun ω => exp (X ω a) + exp (-(X ω a))) μ :=
    hint_pos.add hint_neg
  have hsq_asm : AEStronglyMeasurable (fun ω => (X ω a) ^ 2) μ := hm.pow 2
  exact hdom.mono hsq_asm (by
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (by positivity)]
    exact sq_le_exp_add_exp_neg (X ω a))

/-- Products `Xₐ · X_b` of two coordinates of a sub-Gaussian random vector are integrable
(by Cauchy–Schwarz from `subgaussian_component_memLp_two`). -/
theorem subgaussian_product_integrable :
    ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (σsq : ℝ)
    (_ : IsSubGaussianVec μ X σsq)
    (a b : Fin d)
    (_ : AEStronglyMeasurable (fun ω => X ω a) μ)
    (_ : Integrable (fun ω => exp (X ω a)) μ)
    (_ : Integrable (fun ω => exp (-(X ω a))) μ)
    (_ : AEStronglyMeasurable (fun ω => X ω b) μ)
    (_ : Integrable (fun ω => exp (X ω b)) μ)
    (_ : Integrable (fun ω => exp (-(X ω b))) μ),
    Integrable (fun ω => X ω a * X ω b) μ := by
  intro d Ω inst μ hP X σsq hSG a b hma hia hia' hmb hib hib'
  exact (subgaussian_component_memLp_two μ X σsq hSG a hma hia hia').integrable_mul
    (subgaussian_component_memLp_two μ X σsq hSG b hmb hib hib')

/-- Bilinear transform of the covariance under a linear map: if `E[X X^⊤] = Σ`, then for any
matrix `M` one has `E[(M X)(M X)^⊤] = M Σ M^⊤` (entrywise statement). -/
theorem bochner_bilinear_transform :
    ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ (Fin d))
    (Sig : Matrix (Fin d) (Fin d) ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hInt : ∀ (a b : Fin d), Integrable (fun ω => X ω a * X ω b) μ)
    (_ : ∀ (j k : Fin d), ∫ ω, X ω j * X ω k ∂μ = Sig j k),
    ∀ (j k : Fin d),
      ∫ ω, (applyMatrix M (X ω)) j * (applyMatrix M (X ω)) k ∂μ = (M * Sig * Mᵀ) j k := by
  intro d Ω inst μ instP X Sig M hInt hE j k
  have hInt' : ∀ a b, Integrable (fun ω => M j a * (M k b * (X ω a * X ω b))) μ :=
    fun a b => ((hInt a b).const_mul _).const_mul _
  simp_rw [applyMatrix_apply, Finset.sum_mul_sum univ univ]
  simp_rw [show ∀ (a b : Fin d) (ω : Ω), M j a * X ω a * (M k b * X ω b) =
    M j a * (M k b * (X ω a * X ω b)) from fun a b ω => by ring]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => hInt' a b))]
  simp_rw [integral_finset_sum _ (fun b _ => hInt' _ b)]
  simp_rw [integral_const_mul, hE]
  simp only [mul_apply, transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro a _; ring

/-- Outer-product identity for transformed vectors: `(M x)(M x)^⊤ = M (x x^⊤) M^⊤`. -/
lemma apply_outer_product (M : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    Matrix.of (fun (j k : Fin d) => applyMatrix M x j * applyMatrix M x k) =
    M * Matrix.of (fun (j k : Fin d) => x j * x k) * Mᵀ := by
  ext j k
  simp only [applyMatrix, of_apply, mul_apply, transpose_apply,
    WithLp.equiv, mulVec, dotProduct, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext a; congr 1; ext b; ring

/-- Linear transforms commute with the empirical covariance:
`Σ̂(M X) = M Σ̂(X) M^⊤`. -/
theorem empirical_covariance_linear_map :
    ∀ {d n : ℕ} {Ω : Type*}
    (M : Matrix (Fin d) (Fin d) ℝ)
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (ω : Ω),
    empiricalCovariance (fun i ω => applyMatrix M (X i ω)) ω =
      M * empiricalCovariance X ω * Mᵀ := by
  intro d n Ω M X ω
  unfold empiricalCovariance
  simp_rw [apply_outer_product]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [mul_smul_comm, smul_mul_assoc]

/-- The `PiLp 2` inner product of two vectors agrees with their Euclidean dot product. -/
lemma piLp_inner_eq_dotProduct (u v : Fin d → ℝ) :
    @inner ℝ (WithLp 2 (Fin d → ℝ)) _
      (WithLp.toLp 2 u) (WithLp.toLp 2 v) = dotProduct u v := by
  simp only [inner, dotProduct]; congr 1; ext i; simp [RCLike.re_to_real]; ring

/-- Every row of an invertible matrix is nonzero. -/
lemma row_ne_zero_of_invertible (M : Matrix (Fin d) (Fin d) ℝ) [Invertible M]
    (i : Fin d) : M i ≠ 0 := by
  intro h; have : (M * ⅟M) i i = 0 := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_left (congr_fun h k) _
  rw [mul_invOf_self] at this; simp at this



/-- For a sub-Gaussian random vector `X`, both `e^{Xᵢ}` and `e^{-Xᵢ}` are integrable. -/
theorem subgaussianVec_exp_integrable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (σsq : ℝ)
    (hSubG : IsSubGaussianVec μ X σsq) (i : Fin d) :
    Integrable (fun ω => Real.exp (X ω i)) μ ∧
    Integrable (fun ω => Real.exp (-(X ω i))) μ := by

  obtain ⟨hAEM, hMGF_boch, hMGF_lint⟩ := hSubG

  set f : Fin d → Ω → ℝ := fun j ω => X ω j with hf_def

  have hf_aesm : ∀ j, AEStronglyMeasurable (f j) μ := by
    intro j
    exact (EuclideanSpace.proj j |>.continuous).comp_aestronglyMeasurable
      hAEM.aestronglyMeasurable

  have h_unit : ∀ j : Fin d, ‖(EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ = 1 :=
    fun j => by rw [PiLp.norm_single]; simp
  have h_sum : ∀ j : Fin d, ∀ ω, ∑ k : Fin d, (EuclideanSpace.single j (1 : ℝ) :
      EuclideanSpace ℝ (Fin d)) k * X ω k = X ω j :=
    fun j ω => by simp [Finset.sum_ite_eq']

  have h_individual_mgf_lint : ∀ j s,
      ∫⁻ ω, ENNReal.ofReal (exp (s * f j ω)) ∂μ ≤
        ENNReal.ofReal (exp (Real.sqrt (max σsq 0) ^ 2 * s ^ 2 / 2)) := by
    intro j s
    have h_bound := hMGF_lint (EuclideanSpace.single j 1) (h_unit j) s
    simp_rw [h_sum j] at h_bound
    calc ∫⁻ ω, ENNReal.ofReal (exp (s * f j ω)) ∂μ
        ≤ ENNReal.ofReal (exp (σsq * s ^ 2 / 2)) := h_bound
      _ ≤ ENNReal.ofReal (exp (Real.sqrt (max σsq 0) ^ 2 * s ^ 2 / 2)) := by
          apply ENNReal.ofReal_le_ofReal
          apply exp_le_exp_of_le
          apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ 2)
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg s)
          rw [Real.sq_sqrt (le_max_right σsq 0)]
          exact le_max_left σsq 0

  have h_int : ∀ j s, Integrable (fun ω => exp (s * f j ω)) μ :=
    fun j s => Rigollet.Chapter4.Thm_4_6.exp_individual_integrable μ d f
      (Real.sqrt (max σsq 0)) h_individual_mgf_lint hf_aesm j s

  constructor
  ·
    have : (fun ω => exp (X ω i)) = (fun ω => exp (1 * f i ω)) := by
      ext ω; simp [hf_def]
    rw [this]
    exact h_int i 1
  ·
    have : (fun ω => exp (-(X ω i))) = (fun ω => exp ((-1) * f i ω)) := by
      ext ω; simp [hf_def]
    rw [this]
    exact h_int i (-1)

/-- Regularity package for sub-Gaussian random vectors: each coordinate is strongly measurable
and has integrable two-sided exponential. -/
theorem subgaussian_vec_regularity :
    ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (σsq : ℝ)
    (_ : IsSubGaussianVec μ X σsq),
    (∀ i, AEStronglyMeasurable (fun ω => X ω i) μ) ∧
    (∀ i, Integrable (fun ω => Real.exp (X ω i)) μ) ∧
    (∀ i, Integrable (fun ω => Real.exp (-(X ω i))) μ) := by
  intro d Ω _ μ _ X σsq hSubG
  have hX := subGaussianVec_aestronglyMeasurable μ X σsq hSubG
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hX
  · exact (subgaussianVec_exp_integrable μ X σsq hSubG i).1
  · exact (subgaussianVec_exp_integrable μ X σsq hSubG i).2

/-- Convenience corollary: all coordinatewise products `Xₐ X_b` of a sub-Gaussian random vector
are integrable. -/
theorem subgaussian_vec_product_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) (σsq : ℝ)
    (hSubG : IsSubGaussianVec μ X σsq) :
    ∀ (a b : Fin d), Integrable (fun ω => X ω a * X ω b) μ := by
  intro a b
  obtain ⟨hm, hep, hen⟩ := subgaussian_vec_regularity μ X σsq hSubG
  exact subgaussian_product_integrable μ X σsq hSubG a b
    (hm a) (hep a) (hen a) (hm b) (hep b) (hen b)




/-- Algebraic identity matching the `t/2` split of the operator-norm threshold with the
`t/32` rate appearing in the Bernstein bound. -/
lemma half_div16_eq_div32 (t : ℝ) :
    min ((t / 2 / 16) ^ 2) (t / 2 / 16) = min ((t / 32) ^ 2) (t / 32) := by
  congr 1 <;> ring

/-- If `|N| ≤ 12^d`, then `|N|² ≤ 144^d`. -/
lemma card_sq_le_144d {α : Type*} {N : Finset α}
    (hN : (N.card : ℝ) ≤ (12 : ℝ) ^ d) :
    (N.card : ℝ) ^ 2 ≤ (144 : ℝ) ^ d := by
  calc (N.card : ℝ) ^ 2 ≤ ((12 : ℝ) ^ d) ^ 2 := by
        apply sq_le_sq'
        · linarith [Nat.cast_nonneg (α := ℝ) N.card]
        · exact hN
    _ = (144 : ℝ) ^ d := by
        rw [← pow_mul, show d * 2 = 2 * d from by ring, pow_mul,
            show (12 : ℝ) ^ 2 = 144 from by norm_num]




/-- Numerical bound `e^{16} ≥ 289` obtained from the first few Taylor terms of `exp`. -/
lemma exp_16_ge_289 : (289 : ℝ) ≤ Real.exp 16 := by
  have h : (0 : ℝ) ≤ 16 := by norm_num
  have := Real.sum_le_exp_of_nonneg h 4
  simp [Finset.sum_range_succ] at this; linarith

/-- `288^d ≤ exp(16 d)`, used to absorb the `(288)^d` covering-number factor. -/
lemma h288d_le_exp16d (d : ℕ) : (288 : ℝ) ^ d ≤ Real.exp (16 * ↑d) := by
  calc (288 : ℝ) ^ d ≤ (Real.exp 16) ^ d := by
        gcongr; linarith [exp_16_ge_289]
    _ = Real.exp (↑d * 16) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (16 * ↑d) := by ring_nf

/-- For `0 < δ < 1`, `exp(-16 · log(1/δ)) = δ^{16} ≤ δ`. -/
lemma exp_neg_log_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.exp (-(16 * Real.log (1 / δ))) ≤ δ := by
  rw [one_div, Real.log_inv, show -(16 * -Real.log δ) = ↑(16 : ℕ) * Real.log δ from by
    push_cast; ring]
  rw [Real.exp_nat_mul, Real.exp_log hδ]
  calc δ ^ 16 = δ ^ 1 * δ ^ 15 := by ring
    _ ≤ δ ^ 1 * 1 := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_one₀ (le_of_lt hδ) (le_of_lt hδ1)
        · exact pow_nonneg (le_of_lt hδ) 1
    _ = δ := by ring

/-- Algebraic verification that the tail bound from the general concentration inequality,
evaluated at the threshold `1024 · covRate d n δ`, is at most `δ`. -/
lemma rate_algebraic_bound
    (hd : 0 < d) (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (288 : ℝ) ^ d *
      Real.exp (-(↑n / 2 * min ((1024 * covRate d n δ / 32) ^ 2)
        (1024 * covRate d n δ / 32))) ≤ δ := by
  set r := (d : ℝ) + Real.log (1 / δ) with hr_def
  set c := covRate d n δ with hc_def
  have h_simp : 1024 * c / 32 = 32 * c := by ring
  rw [h_simp]
  have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr hd
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hlog_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos; rw [one_div]; exact (one_lt_inv₀ hδ).mpr hδ1
  have hr_pos : 0 < r := by linarith
  have hc_ge_rn : c ≥ r / ↑n := by
    simp only [hc_def, covRate]; exact le_max_right _ _
  have hc_ge_sqrt : c ≥ Real.sqrt (r / ↑n) := by
    simp only [hc_def, covRate]; exact le_max_left _ _
  have hc_pos : 0 < c := by linarith [div_pos hr_pos hn_pos]

  have h_exp_bound : ↑n / 2 * min ((32 * c) ^ 2) (32 * c) ≥ 16 * r := by
    by_cases h : 1 ≤ 32 * c
    ·
      have hsq : (32 * c) ^ 2 ≥ 32 * c := by nlinarith
      rw [min_eq_right hsq.le]
      have : ↑n / 2 * (32 * c) ≥ ↑n / 2 * (32 * (r / ↑n)) := by nlinarith
      linarith [show ↑n / 2 * (32 * (r / ↑n)) = 16 * r from by field_simp; ring]
    ·
      push Not at h
      have hsq : (32 * c) ^ 2 ≤ 32 * c := by nlinarith
      rw [min_eq_left hsq]

      have hrn_nn : 0 ≤ r / ↑n := le_of_lt (div_pos hr_pos hn_pos)
      have hcsq : c ^ 2 ≥ r / ↑n := by
        have h1 : Real.sqrt (r / ↑n) ≤ c := hc_ge_sqrt
        have h2 : 0 ≤ Real.sqrt (r / ↑n) := Real.sqrt_nonneg _
        have h3 : (Real.sqrt (r / ↑n)) ^ 2 = r / ↑n := Real.sq_sqrt hrn_nn
        nlinarith [sq_nonneg (c - Real.sqrt (r / ↑n)), sq_abs (Real.sqrt (r / ↑n))]

      have : (32 * c) ^ 2 = 1024 * c ^ 2 := by ring
      rw [this]
      have h1 : ↑n / 2 * (1024 * (r / ↑n)) = 512 * r := by field_simp; ring
      nlinarith

  calc (288 : ℝ) ^ d * Real.exp (-(↑n / 2 * min ((32 * c) ^ 2) (32 * c)))
      ≤ Real.exp (16 * ↑d) * Real.exp (-(16 * r)) := by
        apply mul_le_mul (h288d_le_exp16d d) _ (le_of_lt (Real.exp_pos _))
          (le_of_lt (Real.exp_pos _))
        apply Real.exp_le_exp.mpr; linarith
    _ = Real.exp (-(16 * Real.log (1 / δ))) := by
        rw [← Real.exp_add]; congr 1; rw [hr_def]; ring
    _ ≤ δ := exp_neg_log_bound δ hδ hδ1


/-- Davis–Kahan eigenvector perturbation bound (Theorem 4.8 reformulated): in a spiked
covariance model with signal direction `v`, the largest eigenvector `v̂` of any PSD perturbation
`Σ̃` satisfies `min_{ε=±1} ‖ε v̂ - v‖ ≤ (2√2 / θ) · ‖Σ̃ - Σ‖_op`. -/
theorem davisKahan_eigvec_bound
    {d : ℕ}
    (Sig : Matrix (Fin d) (Fin d) ℝ) (θ : ℝ) (v : EuclideanSpace ℝ (Fin d))
    (hSpike : IsSpikedCovariance Sig θ v)
    (SigTilde : Matrix (Fin d) (Fin d) ℝ) (hPSD : SigTilde.PosSemidef)
    (vhat : EuclideanSpace ℝ (Fin d))
    (hvhat : IsLargestEigenvector SigTilde vhat) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ‖ε • vhat - v‖ ≤ 2 * Real.sqrt 2 / θ * matrixOpNorm (SigTilde - Sig) := by

  have hSpike' : Thm48.IsSpikedCovariance Sig θ v := hSpike
  have hvhat' : Thm48.IsLargestEigenvector SigTilde vhat := hvhat

  have h48 := Thm48.theorem_4_8 Sig θ v hSpike' SigTilde hPSD vhat hvhat'.1 hvhat'


  change min (‖vhat - v‖ ^ 2) (‖vhat + v‖ ^ 2) ≤
    8 / θ ^ 2 * matrixOpNorm (SigTilde - Sig) ^ 2 at h48

  have hθ_pos : 0 < θ := hSpike.1
  have hv_unit : ‖v‖ = 1 := hSpike.2.1
  have hvhat_unit : ‖vhat‖ = 1 := hvhat.1
  have hΔ_nn : 0 ≤ matrixOpNorm (SigTilde - Sig) := norm_nonneg _

  have h_sq_eq : 8 / θ ^ 2 * matrixOpNorm (SigTilde - Sig) ^ 2 =
      (2 * Real.sqrt 2 / θ * matrixOpNorm (SigTilde - Sig)) ^ 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp; nlinarith [h2]
  rw [h_sq_eq] at h48

  set C := 2 * Real.sqrt 2 / θ * matrixOpNorm (SigTilde - Sig) with hC_def
  have hC_nn : 0 ≤ C := by positivity
  have h_sub_nn : 0 ≤ ‖vhat - v‖ := norm_nonneg _
  have h_add_nn : 0 ≤ ‖vhat + v‖ := norm_nonneg _

  by_cases h_sub : ‖vhat - v‖ ^ 2 ≤ ‖vhat + v‖ ^ 2
  ·
    rw [min_eq_left h_sub] at h48
    have h_le : ‖vhat - v‖ ≤ C := by nlinarith [sq_nonneg (‖vhat - v‖ - C)]
    exact ⟨1, Or.inl rfl, by simp [one_smul]; exact h_le⟩
  ·
    push Not at h_sub
    rw [min_eq_right h_sub.le] at h48
    have h_le : ‖vhat + v‖ ≤ C := by nlinarith [sq_nonneg (‖vhat + v‖ - C)]
    refine ⟨-1, Or.inr rfl, ?_⟩

    have : (-1 : ℝ) • vhat - v = -(vhat + v) := by ext i; simp; ring
    rw [this, norm_neg]; exact h_le

/-- The empirical covariance matrix is positive-semidefinite at every sample point, as a
nonnegative scalar multiple of a sum of outer products. -/
theorem empiricalCovariance_posSemidef
    {d n : ℕ} {Ω : Type*}
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    (empiricalCovariance X ω).PosSemidef := by
  unfold empiricalCovariance
  apply Matrix.PosSemidef.smul
  · exact posSemidef_sum Finset.univ (fun i _ => by
      have : Matrix.of (fun (j k : Fin d) => X i ω j * X i ω k) =
        vecMulVec (fun j => X i ω j) (star (fun j => X i ω j)) := by
        ext j k; simp [vecMulVec, Matrix.of_apply]
      rw [this]
      exact posSemidef_vecMulVec_self_star _)
  · positivity

/-- The Euclidean inner product equals the dot product of the underlying `Fin d → ℝ`
representations. -/
lemma inner_eq_dotProduct_ofLp {d : ℕ}
    (v x : EuclideanSpace ℝ (Fin d)) :
    @inner ℝ _ _ v x = dotProduct v.ofLp x.ofLp := by
  simp only [PiLp.inner_apply, dotProduct]; congr 1; ext i; simp [inner]; ring

/-- `‖v‖² = v · v` for Euclidean vectors. -/
lemma euclidean_norm_sq_eq_dotProduct {d : ℕ}
    (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ^ 2 = dotProduct v.ofLp v.ofLp := by
  rw [EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
  simp only [dotProduct]; congr 1; ext i; simp [Real.norm_eq_abs, sq]

/-- If `v` is a unit vector then `v · v = 1`. -/
lemma unit_dotProduct_one {d : ℕ}
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    dotProduct v.ofLp v.ofLp = 1 := by
  have := euclidean_norm_sq_eq_dotProduct v; rw [hv, one_pow] at this; linarith

/-- Action of a spiked matrix on a vector: `(θ v v^⊤ + I) x = θ ⟨v, x⟩ v + x`. -/
lemma spiked_mulVec_raw {d : ℕ} (θ : ℝ) (v x : Fin d → ℝ) :
    (θ • vecMulVec v v + (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x =
    (θ * dotProduct v x) • v + x := by
  ext i
  simp [add_mulVec, smul_mulVec, vecMulVec_mulVec, one_mulVec,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

set_option maxHeartbeats 800000 in
/-- The operator norm of a spiked covariance `Σ = θ v v^⊤ + I` (with `‖v‖ = 1` and `θ > 0`)
equals `1 + θ`, since the top eigenvalue is `1 + θ` with eigenvector `v`. -/
theorem spiked_opNorm_eq
    {d : ℕ}
    (Sig : Matrix (Fin d) (Fin d) ℝ) (θ : ℝ) (v : EuclideanSpace ℝ (Fin d))
    (hSpike : IsSpikedCovariance Sig θ v) :
    matrixOpNorm Sig = 1 + θ := by
  obtain ⟨hθ_pos, hv_unit, hSig⟩ := hSpike
  set f := (Matrix.toEuclideanLin Sig).toContinuousLinearMap
  unfold matrixOpNorm
  apply le_antisymm
  ·

    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
    intro x
    show ‖(Matrix.toEuclideanLin Sig) x‖ ≤ (1 + θ) * ‖x‖
    conv_lhs => rw [show (Matrix.toEuclideanLin Sig) x =
      (WithLp.equiv 2 (Fin d → ℝ)).symm (Sig *ᵥ x.ofLp) from rfl]
    rw [hSig, spiked_mulVec_raw]
    set a := dotProduct v.ofLp x.ofLp
    have heq : (WithLp.equiv 2 (Fin d → ℝ)).symm ((θ * a) • v.ofLp + x.ofLp) =
      (θ * a) • v + x := by
      ext i; simp [WithLp.equiv, smul_eq_mul]
    rw [heq]
    have ha : |a| ≤ ‖x‖ := by
      have h1 : |a| ≤ ‖v‖ * ‖x‖ := by
        rw [show a = @inner ℝ _ _ v x from (inner_eq_dotProduct_ofLp v x).symm]
        exact abs_real_inner_le_norm v x
      rw [hv_unit, one_mul] at h1; exact h1
    calc ‖(θ * a) • v + x‖
        ≤ ‖(θ * a) • v‖ + ‖x‖ := norm_add_le _ _
      _ = |θ * a| * ‖v‖ + ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = |θ * a| + ‖x‖ := by rw [hv_unit, mul_one]
      _ = θ * |a| + ‖x‖ := by rw [abs_mul, abs_of_pos hθ_pos]
      _ ≤ θ * ‖x‖ + ‖x‖ := by linarith [mul_le_mul_of_nonneg_left ha (le_of_lt hθ_pos)]
      _ = (1 + θ) * ‖x‖ := by ring
  ·

    have hfv : f v = (1 + θ) • v := by
      show (Matrix.toEuclideanLin Sig) v = (1 + θ) • v
      conv_lhs => rw [show (Matrix.toEuclideanLin Sig) v =
        (WithLp.equiv 2 (Fin d → ℝ)).symm (Sig *ᵥ v.ofLp) from rfl]
      rw [hSig, spiked_mulVec_raw, unit_dotProduct_one v hv_unit, mul_one]
      ext i; simp [WithLp.equiv, smul_eq_mul]; ring
    have h1 : ‖f v‖ = 1 + θ := by
      rw [hfv, norm_smul, Real.norm_of_nonneg (by linarith), hv_unit, mul_one]
    have h2 := ContinuousLinearMap.le_opNorm f v
    rw [h1, hv_unit, mul_one] at h2
    exact h2

/-- Complementary-event probability bound: if `μ(Sᶜ) ≤ δ` then `μ(S) ≥ 1 - δ`. -/
lemma prob_compl_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Set Ω) (δ : ℝ) (hδ : 0 < δ)
    (hbad : μ Sᶜ ≤ ENNReal.ofReal δ) :
    μ S ≥ ENNReal.ofReal (1 - δ) := by
  rw [ge_iff_le, ENNReal.ofReal_sub _ (le_of_lt hδ), ENNReal.ofReal_one]
  rw [tsub_le_iff_right]
  calc (1 : ENNReal) = μ Set.univ := (measure_univ).symm
    _ ≤ μ S + μ Sᶜ := by
        rw [← Set.union_compl_self S]; exact measure_union_le S Sᶜ
    _ ≤ μ S + ENNReal.ofReal δ := by gcongr


end Cor49
