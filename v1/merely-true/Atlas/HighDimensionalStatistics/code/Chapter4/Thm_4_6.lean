/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_12
import Atlas.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_18

open MeasureTheory ProbabilityTheory Matrix Real Finset BigOperators

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

variable {d : ℕ}

namespace Rigollet.Chapter4.Thm_4_6

/-- Operator (L²) norm of a real square matrix `A`, defined as the supremum of `‖A v‖` over
unit vectors `v` in Euclidean space. -/
def matrixOpNorm (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ (v : EuclideanSpace ℝ (Fin d)) (_ : ‖v‖ = 1),
    ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖

/-- A `Fin d → ℝ`-valued random variable `X` is sub-Gaussian with proxy variance `σ²`
(`X ~ subG_d(σ²)`) if every projection `⟨u, X⟩` along a unit vector `u` is scalar
sub-Gaussian with proxy variance `σ²`, both in Bochner and lower-Lebesgue MGF form. -/
def IsSubGaussianVec {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin d → ℝ) (σsq : ℝ) : Prop :=
  AEMeasurable X μ ∧
  (∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    ∀ (s : ℝ),
      ∫ ω, Real.exp (s * (∑ j : Fin d, u j * X ω j)) ∂μ ≤
        Real.exp (σsq * s ^ 2 / 2)) ∧
  (∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
    ∀ (s : ℝ),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (∑ j : Fin d, u j * X ω j))) ∂μ ≤
        ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2)))

/-- Empirical (sample) covariance matrix
`Σ̂(ω) = (1/n) Σᵢ Xᵢ(ω) Xᵢ(ω)^⊤` for `Fin d → ℝ`-valued samples. -/
def empiricalCovariance {n : ℕ} {Ω : Type*}
    (X : Fin n → Ω → Fin d → ℝ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / (n : ℝ)) • ∑ i : Fin n, Matrix.of (fun (j k : Fin d) => X i ω j * X i ω k)

/-- Covariance estimation rate `√((d + log(1/δ))/n) ∨ (d + log(1/δ))/n` controlling the
operator-norm deviation of the empirical covariance matrix. -/
def covRate (d n : ℕ) (δ : ℝ) : ℝ :=
  let t := (d : ℝ) + Real.log (1 / δ)
  max (Real.sqrt (t / (n : ℝ))) (t / (n : ℝ))

/-- A uniform bound `‖A v‖ ≤ M` for all unit vectors `v` implies `‖A‖_op ≤ M`. -/
lemma opnorm_le_of_bound (A : Matrix (Fin d) (Fin d) ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 →
      ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖ ≤ M) :
    matrixOpNorm A ≤ M := by
  apply ciSup_le; intro v
  by_cases hv : ‖v‖ = 1
  · rw [ciSup_pos hv]; exact h v hv
  · rw [ciSup_neg hv, Real.sSup_empty]; exact hM

/-- The local `matrixOpNorm` (supremum form) is bounded above by the global root-level
`_root_.matrixOpNorm` (continuous-linear-map form). -/
lemma matrixOpNorm_le_root (A : Matrix (Fin d) (Fin d) ℝ) :
    matrixOpNorm A ≤ _root_.matrixOpNorm A := by
  unfold matrixOpNorm _root_.matrixOpNorm
  apply ciSup_le; intro v
  by_cases hv : ‖v‖ = 1
  · rw [ciSup_pos hv]
    have heq : (EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v) =
        Matrix.toEuclideanLin A v := rfl
    rw [heq]
    calc ‖Matrix.toEuclideanLin A v‖
        = ‖(Matrix.toEuclideanLin A).toContinuousLinearMap v‖ := rfl
      _ ≤ ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ := by rw [hv, mul_one]
  · rw [ciSup_neg hv]
    exact Real.sSup_empty ▸ norm_nonneg _

/-- Euclidean (`L²`) unit-ball membership implies supremum (`L∞`) unit-ball membership. -/
lemma norm_plain_le_euclidean_loc (x : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ ≤ 1) :
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

/-- ε-net reduction (plain `Fin d → ℝ` version): there is a finite set `N` of unit-ball
vectors with `|N| ≤ 12^d` such that whenever `‖A‖_op > t`, two net points `x, y ∈ N` witness
`|⟨x, A y⟩| > t/2`. -/
theorem eps_net_opnorm_reduction (hd : 0 < d) :
    ∃ (N : Finset (Fin d → ℝ)),
      (N.card : ℝ) ≤ (12 : ℝ) ^ d ∧
      N.Nonempty ∧
      (∀ x ∈ N, ‖x‖ ≤ 1) ∧
      (∀ (A : Matrix (Fin d) (Fin d) ℝ) (t : ℝ),
        matrixOpNorm A > t →
        ∃ x ∈ N, ∃ y ∈ N,
          |dotProduct x (A.mulVec y)| > t / 2) := by

  have hε_pos : (0 : ℝ) < 1 / 4 := by norm_num
  have hε_lt : (1 : ℝ) / 4 < 1 := by norm_num
  obtain ⟨N_L2, hN_net, hN_card⟩ := lemma_1_18_covering_number_euclidean_ball hd (1/4) hε_pos hε_lt

  let N : Finset (Fin d → ℝ) := N_L2.image (EuclideanSpace.equiv (Fin d) ℝ)

  have hN_sub_L2 : ∀ x ∈ N_L2, ‖x‖ ≤ 1 := by
    intro x hx
    have := hN_net.subset_set (Finset.mem_coe.mpr hx)
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hN_cover : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      ∃ x ∈ N_L2, dist u x ≤ 1/4 := by
    intro u hu
    have hu_ball : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith [hu.symm.le]
    obtain ⟨x, hxN, hdist⟩ := hN_net.exists_dist_le hu_ball
    exact ⟨x, Finset.mem_coe.mp hxN, dist_comm x u ▸ hdist⟩

  have hN_ne_L2 : N_L2.Nonempty := by
    have : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_closedBall]; simp
    obtain ⟨x, hxN, _⟩ := hN_net.exists_dist_le this
    exact ⟨x, Finset.mem_coe.mp hxN⟩
  have hN_ne : N.Nonempty := hN_ne_L2.image _

  have hN_card_bound : (N.card : ℝ) ≤ (12 : ℝ) ^ d := by
    have h1 : N.card ≤ N_L2.card := Finset.card_image_le
    have h12 : (3 : ℝ) / (1 / 4) = 12 := by norm_num
    have h12d : ((3 : ℝ) / (1 / 4)) ^ d = (12 : ℝ) ^ d := by rw [h12]
    calc (N.card : ℝ) ≤ (N_L2.card : ℝ) := Nat.cast_le.mpr h1
      _ ≤ ↑(Nat.ceil ((3 / (1/4)) ^ d)) := Nat.cast_le.mpr hN_card
      _ = ↑(Nat.ceil ((12 : ℝ) ^ d)) := by rw [h12d]
      _ = (12 : ℝ) ^ d := by
          have h12' : (12 : ℝ) = ↑(12 : ℕ) := by norm_num
          conv_lhs => rw [h12', ← Nat.cast_pow, Nat.ceil_natCast, Nat.cast_pow, ← h12']

  have hN_norm : ∀ x ∈ N, ‖x‖ ≤ 1 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact norm_plain_le_euclidean_loc y (hN_sub_L2 y hy)

  refine ⟨N, hN_card_bound, hN_ne, hN_norm, ?_⟩
  intro A t hAt

  by_contra h_neg
  push Not at h_neg

  have h_bound : ∀ x ∈ N_L2, ∀ y ∈ N_L2,
      dotProduct (EuclideanSpace.equiv (Fin d) ℝ x)
        (A.mulVec (EuclideanSpace.equiv (Fin d) ℝ y)) ≤ t / 2 := by
    intro x hx y hy
    have hxN : EuclideanSpace.equiv (Fin d) ℝ x ∈ N := Finset.mem_image_of_mem _ hx
    have hyN : EuclideanSpace.equiv (Fin d) ℝ y ∈ N := Finset.mem_image_of_mem _ hy
    exact le_of_abs_le (h_neg _ hxN _ hyN)

  have h42 : _root_.matrixOpNorm A ≤ 2 * (t / 2) :=
    lemma_4_2_eps_net_reduction A hN_cover hN_cover hN_sub_L2 hN_sub_L2 hN_ne_L2 hN_ne_L2
      (t / 2) h_bound

  have h_bridge := matrixOpNorm_le_root A
  linarith

/-- Bilinear form of a rank-one outer product: `x · (v v^⊤) y = (x · v) (v · y)`. -/
lemma dotProduct_outer_mulVec (x y v : Fin d → ℝ) :
    dotProduct x ((Matrix.of (fun j k => v j * v k)).mulVec y) =
    dotProduct x v * dotProduct v y := by
  simp only [dotProduct, mulVec, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext k; congr 1; ext j; ring

/-- Polarisation identity expressing the product of two linear forms as a difference of
squares: `(x · v)(v · y) = ((x+y)·v)² − ((x−y)·v)² ) / 4`. -/
lemma polarization_dotProduct (x y v : Fin d → ℝ) :
    dotProduct x v * dotProduct v y =
    ((dotProduct (x + y) v) ^ 2 - (dotProduct (x - y) v) ^ 2) / 4 := by
  have hxp : dotProduct (x + y) v = dotProduct x v + dotProduct y v := by
    simp [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hxm : dotProduct (x - y) v = dotProduct x v - dotProduct y v := by
    simp [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hcomm : dotProduct v y = dotProduct y v := by
    simp [dotProduct]; congr 1; ext i; ring
  rw [hxp, hxm, hcomm]; ring

/-- Decomposition of the centred bilinear form along the empirical covariance as an average of
i.i.d. summands: `⟨x, (Σ̂ - I) y⟩ = (1/n) Σᵢ ((x · Yᵢ)(Yᵢ · y) - x · y)`. -/
lemma bilinear_form_decomposition
    {d : ℕ} (n : ℕ) (hn : 0 < n) {Ω : Type*}
    (Y : Fin n → Ω → Fin d → ℝ) (ω : Ω) (x y : Fin d → ℝ) :
    dotProduct x ((empiricalCovariance Y ω - 1).mulVec y) =
    (↑n)⁻¹ * ∑ i : Fin n,
      ((∑ j : Fin d, x j * Y i ω j) * (∑ k : Fin d, Y i ω k * y k)
       - dotProduct x y) := by
  simp only [empiricalCovariance, Matrix.sub_mulVec, dotProduct_sub,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  simp only [Matrix.sum_mulVec, dotProduct_sum]
  rw [one_div, Matrix.one_mulVec]
  have h2 : ∀ i : Fin n,
      x ⬝ᵥ (of fun j k => Y i ω j * Y i ω k).mulVec y =
      (∑ j, x j * Y i ω j) * (∑ k, Y i ω k * y k) := by
    intro i
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]; congr 1; ext k; congr 1; ext j; ring
  simp_rw [h2]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  field_simp

/-- A linear projection `⟨u, Y⟩` of a sub-Gaussian vector along a unit direction `u` is a
(scalar) sub-Gaussian random variable, provided basic integrability and zero-mean conditions
hold. -/
theorem subgaussianvec_projection_is_subgaussian
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → Fin d → ℝ} {σsq : ℝ}
    (hSubG : IsSubGaussianVec μ Y σsq)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    (hInt : Integrable (fun ω => ∑ j, u j * Y ω j) μ)
    (hMean : ∫ ω, (∑ j, u j * Y ω j) ∂μ = 0)
    (hExpInt : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * ∑ j, u j * Y ω j)) μ) :
    IsSubGaussian (fun ω => ∑ j, u j * Y ω j) σsq μ :=
  ⟨hInt, hMean, hExpInt, fun s => hSubG.2.1 u hu s⟩

/-- Coordinate-sum restatement of the polarisation identity, written for sums of products. -/
lemma polarization_product_eq (x y z : Fin d → ℝ) :
    (∑ j, x j * z j) * (∑ k, z k * y k) =
      ((∑ j, (x + y) j * z j) ^ 2 - (∑ j, (x - y) j * z j) ^ 2) / 4 :=
  polarization_dotProduct x y z







/-- For independent random variables `fᵢ`, the integral of the product `∏ᵢ exp(sᵢ fᵢ)`
factorises into the product of the individual MGFs. -/
theorem nfold_exp_integral_factoring
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (f : Fin n → Ω → ℝ) (s : Fin n → ℝ)
    (hIndepFun : iIndepFun (m := fun _ => inferInstance) f μ)
    (hMeas : ∀ i, AEMeasurable (f i) μ) :
    ∫ ω, ∏ i : Fin n, Real.exp (s i * f i ω) ∂μ =
      ∏ i : Fin n, ∫ ω, Real.exp (s i * f i ω) ∂μ :=
  hIndepFun.integral_fun_prod_comp (f := fun i => fun x => Real.exp (s i * x)) hMeas
    (fun _ => (Measurable.exp (measurable_const.mul measurable_id)).aestronglyMeasurable)

/-- Under a (finite) MGF bound in lower-Lebesgue form, the integrand `e^{s fᵢ}` is integrable
for every `s`. -/
theorem exp_individual_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (f : Fin n → Ω → ℝ) (b : ℝ)
    (h_mgf : ∀ i s, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * f i ω)) ∂μ ≤
      ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)))
    (hMeas : ∀ i, AEStronglyMeasurable (f i) μ)
    (i : Fin n) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * f i ω)) μ := by
  constructor
  ·
    have : (fun ω => Real.exp (s * f i ω)) = Real.exp ∘ (fun ω => s * f i ω) := rfl
    rw [this]
    exact continuous_exp.comp_aestronglyMeasurable
      ((aestronglyMeasurable_const.mul (hMeas i)))
  ·
    change ∫⁻ a, ↑‖Real.exp (s * f i a)‖₊ ∂μ < ⊤
    calc ∫⁻ a, ↑‖Real.exp (s * f i a)‖₊ ∂μ
        = ∫⁻ a, ENNReal.ofReal (Real.exp (s * f i a)) ∂μ := by
          congr 1; ext ω
          simp [ENNReal.ofReal, Real.toNNReal_eq_nnnorm_of_nonneg (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)) := h_mgf i s
      _ < ⊤ := ENNReal.ofReal_lt_top

/-- The exponential of the empirical average `l · (1/n) Σᵢ fᵢ` is integrable, by domination
through Jensen's inequality applied to the convex function `exp`. -/
theorem average_exp_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (f : Fin n → Ω → ℝ) (b : ℝ)
    (h_mgf : ∀ i s, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * f i ω)) ∂μ ≤
      ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)))
    (hIndepFun : iIndepFun (m := fun _ => inferInstance) f μ)
    (hMeas : ∀ i, AEMeasurable (f i) μ)
    (l : ℝ) :
    Integrable (fun ω => Real.exp (l * ((↑n)⁻¹ * ∑ i : Fin n, f i ω))) μ := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hn_inv_pos : (0 : ℝ) < (↑n : ℝ)⁻¹ := inv_pos_of_pos hn_pos

  have hf_aesm : ∀ i, AEStronglyMeasurable (f i) μ :=
    fun i => (hMeas i).aestronglyMeasurable

  have h_int : ∀ i s, Integrable (fun ω => Real.exp (s * f i ω)) μ :=
    fun i s => exp_individual_integrable μ n f b h_mgf hf_aesm i s


  have h_target_aesm : AEStronglyMeasurable
      (fun ω => Real.exp (l * ((↑n : ℝ)⁻¹ * ∑ i, f i ω))) μ := by
    apply Continuous.comp_aestronglyMeasurable
      (by fun_prop : Continuous (fun x : ℝ => Real.exp (l * ((↑n : ℝ)⁻¹ * x))))
    have : (fun ω => ∑ i : Fin n, f i ω) = (∑ i : Fin n, f i) := by
      ext ω; simp [Finset.sum_apply]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ (fun i _ => hf_aesm i)

  have h_dom_int : Integrable (fun ω => (↑n : ℝ)⁻¹ * ∑ i, Real.exp (l * f i ω)) μ := by
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro i _
    exact h_int i l

  have h_bound : ∀ᵐ ω ∂μ, ‖Real.exp (l * ((↑n : ℝ)⁻¹ * ∑ i, f i ω))‖ ≤
      ‖(↑n : ℝ)⁻¹ * ∑ i, Real.exp (l * f i ω)‖ := by
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg' n))
      (Finset.sum_nonneg (fun i _ => le_of_lt (exp_pos _))))]
    have hsum_eq : l * ((↑n : ℝ)⁻¹ * ∑ i, f i ω) =
        ∑ i : Fin n, (↑n : ℝ)⁻¹ • (l * f i ω) := by
      simp only [smul_eq_mul, Finset.mul_sum]
      congr 1; ext i; ring
    rw [hsum_eq]
    have hsum_dom : (↑n : ℝ)⁻¹ * ∑ i, Real.exp (l * f i ω) =
        ∑ i : Fin n, (↑n : ℝ)⁻¹ • Real.exp (l * f i ω) := by
      simp [smul_eq_mul, Finset.mul_sum]
    rw [hsum_dom]
    exact ConvexOn.map_sum_le convexOn_exp
      (fun i _ => le_of_lt hn_inv_pos)
      (by simp [Finset.sum_const]; field_simp)
      (fun i _ => Set.mem_univ _)
  exact h_dom_int.mono h_target_aesm h_bound

/-- MGF of the empirical average of `n` independent random variables with proxy `b²`: the
proxy variance shrinks by a factor of `n`, giving `exp(b² l² / (2n))`. -/
lemma average_mgf_from_independence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (f : Fin n → Ω → ℝ) (b : ℝ)
    (h_mgf : ∀ i s, ∫ ω, Real.exp (s * f i ω) ∂μ ≤ Real.exp (b ^ 2 * s ^ 2 / 2))
    (h_mgf_lint : ∀ i s, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * f i ω)) ∂μ ≤
      ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)))
    (hIndepFun : iIndepFun (m := fun _ => inferInstance) f μ)
    (hMeas : ∀ i, AEMeasurable (f i) μ)
    (l : ℝ) :
    (∫ ω, Real.exp (l * ((↑n)⁻¹ * ∑ i : Fin n, f i ω)) ∂μ ≤
      Real.exp (b ^ 2 * l ^ 2 / (2 * ↑n))) ∧
    Integrable (fun ω => Real.exp (l * ((↑n)⁻¹ * ∑ i : Fin n, f i ω))) μ := by
  constructor
  ·

    simp_rw [show ∀ ω, l * ((↑n : ℝ)⁻¹ * ∑ i, f i ω) =
      ∑ i, (l * (↑n : ℝ)⁻¹) * f i ω from fun ω => by simp [Finset.mul_sum, mul_assoc], exp_sum]

    rw [nfold_exp_integral_factoring μ n f (fun _ => l * (↑n : ℝ)⁻¹) hIndepFun hMeas]

    calc ∏ i : Fin n, ∫ ω, Real.exp (l * (↑n : ℝ)⁻¹ * f i ω) ∂μ
        ≤ ∏ _i : Fin n, Real.exp (b ^ 2 * (l * (↑n : ℝ)⁻¹) ^ 2 / 2) :=
          Finset.prod_le_prod (fun i _ => integral_nonneg fun ω => (Real.exp_pos _).le)
            (fun i _ => h_mgf i _)
      _ = Real.exp (b ^ 2 * l ^ 2 / (2 * ↑n)) := by
          simp only [Finset.prod_const, Finset.card_fin, ← Real.exp_nat_mul]
          congr 1
          have hn' : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
          field_simp
  ·
    exact average_exp_integrable μ n hn f b h_mgf_lint hIndepFun hMeas l

/-- A sub-Gaussian random vector is `AEMeasurable`. -/
theorem subgaussian_vec_aemeasurable
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → Fin d → ℝ) (σ : ℝ) (hSubG : IsSubGaussianVec μ Y σ) :
    AEMeasurable Y μ :=
  hSubG.1




/-- Two-sided Chernoff tail bound from a sub-exponential MGF assumption with proxy
`b²/(2n)`: the resulting tail decay is `2 exp(-(n/2) · min((s/b)², s/b))`. -/
theorem chernoff_from_mgf
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n)
    (f : Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hmgf : ∀ l, ∫ ω, Real.exp (l * f ω) ∂μ ≤ Real.exp (b ^ 2 * l ^ 2 / (2 * ↑n)))
    (h_int : ∀ l, Integrable (fun ω => Real.exp (l * f ω)) μ)
    (s : ℝ) (hs : 0 < s) :
    μ {ω : Ω | |f ω| > s} ≤
      ENNReal.ofReal (2 * Real.exp (-(↑n / 2 * min ((s / b) ^ 2) (s / b)))) := by
  have hn_pos : (0 : ℝ) < (↑n : ℝ) := Nat.cast_pos.mpr hn
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  set C := Real.exp (-(↑n * s ^ 2 / (2 * b ^ 2)))
  have hC_pos : 0 < C := Real.exp_pos _

  have h_upper : μ.real {ω | s ≤ f ω} ≤ C := by
    calc μ.real {ω | s ≤ f ω}
        ≤ Real.exp (-(↑n * s / b ^ 2) * s) * mgf f μ (↑n * s / b ^ 2) :=
          measure_ge_le_exp_mul_mgf s (by positivity) (h_int _)
      _ ≤ Real.exp (-(↑n * s / b ^ 2) * s) *
          Real.exp (b ^ 2 * (↑n * s / b ^ 2) ^ 2 / (2 * ↑n)) := by
          gcongr; exact hmgf _
      _ = Real.exp (-(↑n * s / b ^ 2) * s +
          b ^ 2 * (↑n * s / b ^ 2) ^ 2 / (2 * ↑n)) := by rw [← Real.exp_add]
      _ = C := by congr 1; field_simp; ring

  have h_lower : μ.real {ω | s ≤ -f ω} ≤ C := by
    have hmgf_neg : ∀ l, mgf (fun ω => -f ω) μ l ≤
        Real.exp (b ^ 2 * l ^ 2 / (2 * ↑n)) := by
      intro l; show ∫ ω, Real.exp (l * -f ω) ∂μ ≤ _
      simp_rw [mul_neg, ← neg_mul]
      have := hmgf (-l); simp only [neg_sq] at this; exact this
    calc μ.real {ω | s ≤ -f ω}
        ≤ Real.exp (-(↑n * s / b ^ 2) * s) *
          mgf (fun ω => -f ω) μ (↑n * s / b ^ 2) := by
          exact measure_ge_le_exp_mul_mgf s (by positivity)
            (by simp only [mul_neg, ← neg_mul]; exact h_int _)
      _ ≤ Real.exp (-(↑n * s / b ^ 2) * s) *
          Real.exp (b ^ 2 * (↑n * s / b ^ 2) ^ 2 / (2 * ↑n)) := by
          gcongr; exact hmgf_neg _
      _ = Real.exp (-(↑n * s / b ^ 2) * s +
          b ^ 2 * (↑n * s / b ^ 2) ^ 2 / (2 * ↑n)) := by rw [← Real.exp_add]
      _ = C := by congr 1; field_simp; ring

  have h_subset : {ω : Ω | |f ω| > s} ⊆ {ω | s ≤ f ω} ∪ {ω | s ≤ -f ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, gt_iff_lt] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    cases abs_cases (f ω) with
    | inl h => left; linarith [h.1]
    | inr h => right; linarith [h.1]

  have h_C_le : C ≤ Real.exp (-(↑n / 2 * min ((s / b) ^ 2) (s / b))) := by
    apply Real.exp_le_exp.mpr
    have : ↑n * s ^ 2 / (2 * b ^ 2) = ↑n / 2 * (s / b) ^ 2 := by field_simp
    rw [this]
    nlinarith [min_le_left ((s / b) ^ 2) (s / b), show (0 : ℝ) < ↑n / 2 from by linarith]

  calc μ {ω | |f ω| > s}
      ≤ μ ({ω | s ≤ f ω} ∪ {ω | s ≤ -f ω}) := measure_mono h_subset
    _ ≤ μ {ω | s ≤ f ω} + μ {ω | s ≤ -f ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := by
        gcongr
        · exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hC_pos.le).mpr
            (Measure.real_def μ _ ▸ h_upper)
        · exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hC_pos.le).mpr
            (Measure.real_def μ _ ▸ h_lower)
    _ = ENNReal.ofReal (2 * C) := by
        rw [← ENNReal.ofReal_add hC_pos.le hC_pos.le]; congr 1; ring
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(↑n / 2 * min ((s / b) ^ 2) (s / b)))) := by
        apply ENNReal.ofReal_le_ofReal; linarith [h_C_le]



/-- Algebraic identity matching the `t/2` threshold split with the `t/32` rate. -/
lemma half_div16_eq_div32 (t : ℝ) :
    min ((t / 2 / 16) ^ 2) (t / 2 / 16) = min ((t / 32) ^ 2) (t / 32) := by
  congr 1 <;> ring

/-- If `|N| ≤ 12^d`, then `2 |N|² ≤ 288^d`. Used to absorb the union-bound constant into the
covering-number factor. -/
lemma two_card_sq_le_288d {α : Type*} {N : Finset α} (hd : 0 < d)
    (hN : (N.card : ℝ) ≤ (12 : ℝ) ^ d) :
    2 * (N.card : ℝ) ^ 2 ≤ (288 : ℝ) ^ d := by
  have h1 : (N.card : ℝ) ^ 2 ≤ (144 : ℝ) ^ d := by
    calc (N.card : ℝ) ^ 2 ≤ ((12 : ℝ) ^ d) ^ 2 := by
          apply sq_le_sq'
          · linarith [Nat.cast_nonneg (α := ℝ) N.card]
          · exact hN
      _ = (144 : ℝ) ^ d := by
          rw [← pow_mul, show d * 2 = 2 * d from by ring, pow_mul,
              show (12 : ℝ) ^ 2 = 144 from by norm_num]
  calc 2 * (N.card : ℝ) ^ 2 ≤ 2 * (144 : ℝ) ^ d := by linarith
    _ ≤ 2 ^ d * (144 : ℝ) ^ d := by
        gcongr
        exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    _ = (288 : ℝ) ^ d := by rw [← mul_pow]; norm_num



/-- Existence of a whitening matrix: for any positive-definite covariance `Σ`, there is a
matrix `S` (the inverse of the principal matrix square root) with `S Σ S^⊤ = I`. -/
theorem posdef_whitening_matrix_exists
    (covMat : Matrix (Fin d) (Fin d) ℝ) (hPD : covMat.PosDef) :
    ∃ (S : Matrix (Fin d) (Fin d) ℝ), S * covMat * S.transpose = 1 := by
  classical
  open scoped MatrixOrder in
  let R := CFC.sqrt covMat
  have hR_unit : IsUnit R := by
    open scoped MatrixOrder in
    exact (CFC.isUnit_sqrt_iff covMat hPD.posSemidef.nonneg).mpr hPD.isUnit
  use R⁻¹
  have hRsq : R ^ 2 = covMat := by
    open scoped MatrixOrder in exact CFC.sq_sqrt covMat hPD.posSemidef.nonneg
  have hR_sa : IsSelfAdjoint R := by
    open scoped MatrixOrder in
    exact (CFC.sqrt_nonneg covMat).posSemidef.isHermitian.isSelfAdjoint
  have hR_symm : R.transpose = R := by
    have := hR_sa.star_eq
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hRinv_symm : R⁻¹.transpose = R⁻¹ := by
    rw [← conjTranspose_eq_transpose_of_trivial, conjTranspose_nonsing_inv,
        conjTranspose_eq_transpose_of_trivial, hR_symm]
  rw [hRinv_symm, ← hRsq, sq]
  obtain ⟨u, hu⟩ := hR_unit
  rw [← hu]; simp

/-- Quadratic form `v ↦ v^⊤ Σ v` associated with the covariance matrix `Σ`. -/
def covQuadForm (covMat : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : ℝ :=
  ∑ j : Fin d, ∑ k : Fin d, v j * covMat j k * v k

/-- The covariance quadratic form equals `v · (Σ v)`. -/
lemma covQuadForm_eq_dotProduct (covMat : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    covQuadForm covMat v = dotProduct v (covMat.mulVec v) := by
  simp only [covQuadForm, dotProduct, mulVec]
  congr 1; ext j
  simp only [Finset.mul_sum]
  congr 1; ext k; ring

/-- Sub-Gaussianity is preserved under whitening: if `X` is `subG_d(‖Σ‖_op)` with covariance
`Σ` and `S Σ S^⊤ = I`, then `S X` is `subG_d(1)`. -/
theorem subgaussian_whitening_preservation
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin d → ℝ)
    (S covMat : Matrix (Fin d) (Fin d) ℝ)
    (hSG : IsSubGaussianVec μ X (matrixOpNorm covMat))
    (hcov : ∀ (j k : Fin d), ∫ ω, X ω j * X ω k ∂μ = covMat j k)
    (hWhiten : S * covMat * S.transpose = 1)
    (hDir : ∀ (w : Fin d → ℝ) (s : ℝ),
      ∫ ω, Real.exp (s * (∑ j : Fin d, w j * X ω j)) ∂μ ≤
        Real.exp (dotProduct w (covMat.mulVec w) * s ^ 2 / 2))
    (hDirL : ∀ (w : Fin d → ℝ) (s : ℝ),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (∑ j : Fin d, w j * X ω j))) ∂μ ≤
        ENNReal.ofReal (Real.exp (dotProduct w (covMat.mulVec w) * s ^ 2 / 2))) :
    IsSubGaussianVec μ (fun ω => S.mulVec (X ω)) 1 := by
  obtain ⟨hMeas, _, _⟩ := hSG
  have hMeasSX : AEMeasurable (fun ω => S.mulVec (X ω)) μ := by
    have heq : (fun ω => S.mulVec (X ω)) = S.mulVecLin ∘ X := by ext ω; simp
    rw [heq]
    exact (LinearMap.continuous_of_finiteDimensional S.mulVecLin).measurable.comp_aemeasurable hMeas
  have hsum_rw : ∀ (u : EuclideanSpace ℝ (Fin d)) (ω : Ω),
      ∑ j : Fin d, u.ofLp j * (S.mulVec (X ω)) j =
      ∑ k : Fin d, (S.transpose.mulVec u.ofLp) k * X ω k := by
    intro u ω
    simp only [mulVec, dotProduct, transpose_apply]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1; ext j; congr 1; ext k; ring
  have hqf_eq : ∀ (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 →
      dotProduct (S.transpose.mulVec u.ofLp) (covMat.mulVec (S.transpose.mulVec u.ofLp)) = 1 := by
    intro u hu
    rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul]
    rw [show vecMul u.ofLp S = S.transpose.mulVec u.ofLp
      from (mulVec_transpose S u.ofLp).symm]
    rw [dotProduct_mulVec (vecMul u.ofLp (S * covMat)) S.transpose u.ofLp]
    rw [vecMul_vecMul]
    rw [← dotProduct_mulVec u.ofLp (S * covMat * S.transpose) u.ofLp]
    rw [hWhiten, one_mulVec]
    have h : Real.sqrt (∑ i : Fin d, ‖u i‖ ^ 2) = 1 := by
      rw [← EuclideanSpace.norm_eq]; exact hu
    have hnn : (0 : ℝ) ≤ ∑ i : Fin d, ‖u i‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) _)
    have h2 : (∑ i : Fin d, ‖u i‖ ^ 2 : ℝ) = 1 := by nlinarith [Real.sq_sqrt hnn]
    simp only [dotProduct]
    convert h2 using 1
    congr 1; ext i; rw [Real.norm_eq_abs, sq_abs, sq]
  refine ⟨hMeasSX, ?_, ?_⟩
  · intro u hu s
    simp_rw [hsum_rw u]
    calc ∫ ω, Real.exp (s * ∑ j, (S.transpose.mulVec u.ofLp) j * X ω j) ∂μ
        ≤ Real.exp (dotProduct (S.transpose.mulVec u.ofLp)
            (covMat.mulVec (S.transpose.mulVec u.ofLp)) * s ^ 2 / 2) :=
          hDir _ s
      _ = Real.exp (1 * s ^ 2 / 2) := by rw [hqf_eq u hu]
  · intro u hu s
    simp_rw [hsum_rw u]
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (s * ∑ j, (S.transpose.mulVec u.ofLp) j * X ω j)) ∂μ
        ≤ ENNReal.ofReal (Real.exp (dotProduct (S.transpose.mulVec u.ofLp)
            (covMat.mulVec (S.transpose.mulVec u.ofLp)) * s ^ 2 / 2)) :=
          hDirL _ s
      _ = ENNReal.ofReal (Real.exp (1 * s ^ 2 / 2)) := by rw [hqf_eq u hu]

/-- The family `v ↦ ‖A v‖` (restricted to the unit sphere via the indicator supremum) is
bounded above by `‖A‖`, so its range is a `BddAbove` set. -/
lemma matrixOpNorm_bddAbove (A : Matrix (Fin d) (Fin d) ℝ) :
    BddAbove (Set.range (fun v : EuclideanSpace ℝ (Fin d) =>
      ⨆ (_ : ‖v‖ = 1), ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖)) := by
  use ‖(toEuclideanLin A).toContinuousLinearMap‖
  intro x hx
  obtain ⟨v, rfl⟩ := hx
  dsimp
  by_cases hv : ‖v‖ = 1
  · rw [ciSup_pos hv]
    change ‖(toEuclideanLin A) v‖ ≤ _
    calc ‖(toEuclideanLin A) v‖
        = ‖(toEuclideanLin A).toContinuousLinearMap v‖ := rfl
      _ ≤ ‖(toEuclideanLin A).toContinuousLinearMap‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖(toEuclideanLin A).toContinuousLinearMap‖ := by rw [hv, mul_one]
  · rw [ciSup_neg hv, Real.sSup_empty]; exact norm_nonneg _

/-- The operator norm of a positive-definite matrix is strictly positive. -/
theorem opnorm_pos_def_norm [Nonempty (Fin d)]
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) : matrixOpNorm A > 0 := by
  obtain ⟨i⟩ := ‹Nonempty (Fin d)›
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
  have he_norm : ‖e‖ = 1 := by simp [e]
  have hdiag : 0 < A i i := hA.diag_pos
  have hAe_ne : A.mulVec (e : Fin d → ℝ) ≠ 0 := by
    intro h
    have := congr_fun h i
    simp [mulVec, dotProduct, e, EuclideanSpace.single] at this
    linarith
  have hAe_pos : 0 < ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec e)‖ := by
    rw [norm_pos_iff]
    intro h
    apply hAe_ne
    have := congr_arg (EuclideanSpace.equiv (Fin d) ℝ) h
    simp at this
    exact this
  calc matrixOpNorm A
      = ⨆ (v : EuclideanSpace ℝ (Fin d)) (_ : ‖v‖ = 1),
          ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖ := rfl
    _ ≥ ⨆ (_ : ‖e‖ = 1), ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec e)‖ :=
        le_ciSup_of_le (matrixOpNorm_bddAbove A) e le_rfl
    _ = ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec e)‖ := by
        rw [ciSup_pos he_norm]
    _ > 0 := hAe_pos

/-- The local `matrixOpNorm` equals Mathlib's `L²` operator norm on matrices. -/
lemma matrixOpNorm_eq_l2 (A : Matrix (Fin d) (Fin d) ℝ) :
    matrixOpNorm A = @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A := by
  apply le_antisymm
  ·
    apply ciSup_le; intro v
    by_cases hv : ‖v‖ = 1
    · rw [ciSup_pos hv]; change ‖(toEuclideanLin A) v‖ ≤ _
      calc ‖(toEuclideanLin A) v‖ = ‖(toEuclideanLin A).toContinuousLinearMap v‖ := rfl
        _ ≤ ‖(toEuclideanLin A).toContinuousLinearMap‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖(toEuclideanLin A).toContinuousLinearMap‖ := by rw [hv, mul_one]
    · rw [ciSup_neg hv, Real.sSup_empty]; exact ContinuousLinearMap.opNorm_nonneg _

  ·
    show ‖(toEuclideanLin A).toContinuousLinearMap‖ ≤ _
    apply ContinuousLinearMap.opNorm_le_bound
    · apply Real.iSup_nonneg; intro v; apply Real.iSup_nonneg; intro _; exact norm_nonneg _
    · intro v
      change ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖ ≤ matrixOpNorm A * ‖v‖
      by_cases hv : v = 0
      · simp [hv, mulVec_zero]
      · have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
        let w : EuclideanSpace ℝ (Fin d) := (‖v‖⁻¹ : ℝ) • v
        have hw_norm : ‖w‖ = 1 := by simp [w, norm_smul, inv_mul_cancel₀ (ne_of_gt hv_pos)]
        have hAw : ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec w)‖ ≤ matrixOpNorm A := by
          calc ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec w)‖
              = ⨆ (_ : ‖w‖ = 1), ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec w)‖ := by
                rw [ciSup_pos hw_norm]
            _ ≤ _ := le_ciSup (matrixOpNorm_bddAbove A) w
        have hmv : A.mulVec w = ‖v‖⁻¹ • A.mulVec v := by simp [w, mulVec_smul]
        rw [hmv] at hAw
        simp only [map_smul, norm_smul, norm_inv, Real.norm_of_nonneg (le_of_lt hv_pos)] at hAw
        calc ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖
            = ‖v‖ * (‖v‖⁻¹ * ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖) := by
              rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hv_pos), one_mul]
          _ ≤ ‖v‖ * matrixOpNorm A := mul_le_mul_of_nonneg_left hAw (le_of_lt hv_pos)
          _ = matrixOpNorm A * ‖v‖ := mul_comm _ _

/-- Operator-norm bound under whitening: if `S Σ S^⊤ = I`, then
`‖A‖_op ≤ ‖Σ‖_op · ‖S A S^⊤‖_op`. -/
theorem opnorm_whitening_bound_axiom
    (S covMat A : Matrix (Fin d) (Fin d) ℝ)
    (hWhiten : S * covMat * S.transpose = 1)
    (hPD : covMat.PosDef) :
    matrixOpNorm A ≤ matrixOpNorm covMat * matrixOpNorm (S * A * S.transpose) := by
  open scoped Matrix.Norms.L2Operator in
  rw [matrixOpNorm_eq_l2, matrixOpNorm_eq_l2, matrixOpNorm_eq_l2]


  have hSdet_ne : S.det ≠ 0 := by
    intro h
    have : (S * covMat * S.transpose).det = (1 : Matrix (Fin d) (Fin d) ℝ).det := by rw [hWhiten]
    simp [det_mul, det_transpose, h] at this
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet_ne
  have hSTdet : IsUnit S.transpose.det := by rwa [det_transpose]

  have hcov_eq : covMat = S⁻¹ * S.transpose⁻¹ := by
    have h2 : covMat * S.transpose = S⁻¹ := by
      have := congr_arg (S⁻¹ * ·) hWhiten
      simp only [mul_assoc] at this
      rw [← mul_assoc S⁻¹ S, nonsing_inv_mul _ hSdet, one_mul, mul_one] at this; exact this
    calc covMat = covMat * (S.transpose * S.transpose⁻¹) := by
            rw [mul_nonsing_inv _ hSTdet, mul_one]
      _ = covMat * S.transpose * S.transpose⁻¹ := by rw [← mul_assoc]
      _ = S⁻¹ * S.transpose⁻¹ := by rw [h2]

  have hA_eq : A = S⁻¹ * (S * A * S.transpose) * S.transpose⁻¹ := by
    simp only [mul_assoc]
    rw [mul_nonsing_inv _ hSTdet, mul_one, ← mul_assoc, nonsing_inv_mul _ hSdet, one_mul]

  have hST_inv : S.transpose⁻¹ = S⁻¹ᵀ := (transpose_nonsing_inv S).symm
  have h_transpose_norm : @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ᵀ =
      @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact l2_opNorm_conjTranspose _

  have hcov_norm : @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm covMat =
      @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ *
      @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ := by
    rw [hcov_eq, hST_inv]
    rw [← conjTranspose_eq_transpose_of_trivial S⁻¹]
    have h := l2_opNorm_conjTranspose_mul_self S⁻¹ᴴ
    rw [conjTranspose_conjTranspose] at h
    rw [l2_opNorm_conjTranspose] at h; exact h

  calc @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A
      = @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
          (S⁻¹ * (S * A * S.transpose) * S.transpose⁻¹) := by rw [← hA_eq]
    _ ≤ @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (S⁻¹ * (S * A * S.transpose)) *
        @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S.transpose⁻¹ := l2_opNorm_mul _ _
    _ ≤ (@norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ *
         @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (S * A * S.transpose)) *
        @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S.transpose⁻¹ := by
        apply mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _)
        exact @norm_nonneg _ Matrix.instL2OpNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup _
    _ = @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ *
        @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm S⁻¹ *
        @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (S * A * S.transpose) := by
        rw [hST_inv, h_transpose_norm]; ring
    _ = @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm covMat *
        @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (S * A * S.transpose) := by
        rw [← hcov_norm]

/-- Operator-norm transfer property used in the whitening reduction:
`‖A‖_op > ‖Σ‖_op · t  ⇒  ‖S A S^⊤‖_op > t`. -/
theorem opnorm_whitening_transfer_axiom [Nonempty (Fin d)]

    (S covMat A : Matrix (Fin d) (Fin d) ℝ)
    (hWhiten : S * covMat * S.transpose = 1)
    (hPD : covMat.PosDef)
    (t : ℝ)
    (h : matrixOpNorm A > matrixOpNorm covMat * t) :
    matrixOpNorm (S * A * S.transpose) > t := by
  by_contra hle
  push Not at hle
  have hcov_pos : matrixOpNorm covMat > 0 := opnorm_pos_def_norm covMat hPD
  have hcov_nn : (0 : ℝ) ≤ matrixOpNorm covMat := le_of_lt hcov_pos
  have h2 : matrixOpNorm covMat * matrixOpNorm (S * A * S.transpose) ≤
      matrixOpNorm covMat * t :=
    mul_le_mul_of_nonneg_left hle hcov_nn
  have h3 : matrixOpNorm A ≤ matrixOpNorm covMat * matrixOpNorm (S * A * S.transpose) :=
    opnorm_whitening_bound_axiom S covMat A hWhiten hPD
  linarith

/-- For a sub-Gaussian random vector, all coordinatewise products `Xⱼ X_k` are integrable. -/
theorem subgaussian_integrable_products
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin d → ℝ) (σsq : ℝ)
    (hSG : IsSubGaussianVec μ X σsq)
    (j k : Fin d) :
    Integrable (fun ω => X ω j * X ω k) μ := by

  have hASM : ∀ i : Fin d, AEStronglyMeasurable (fun ω => X ω i) μ :=
    fun i => ((measurable_pi_apply i).comp_aemeasurable hSG.1).aestronglyMeasurable

  have hComp_lint : ∀ i : Fin d, ∀ s : ℝ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω i)) ∂μ ≤
        ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2)) := by
    intro i s
    have hei : ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      rw [PiLp.norm_single]; simp
    have := hSG.2.2 (EuclideanSpace.single i 1) hei s
    simp at this; exact this

  set b := |σsq| + 1
  have hb_sq : σsq ≤ b ^ 2 := by
    calc σsq ≤ |σsq| := le_abs_self σsq
    _ ≤ |σsq| + 1 := le_add_of_nonneg_right (by positivity)
    _ ≤ (|σsq| + 1) ^ 2 := by nlinarith [abs_nonneg σsq]
  have hComp_b : ∀ i : Fin d, ∀ s : ℝ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω i)) ∂μ ≤
        ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)) := by
    intro i s
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω i)) ∂μ
        ≤ ENNReal.ofReal (Real.exp (σsq * s ^ 2 / 2)) := hComp_lint i s
      _ ≤ ENNReal.ofReal (Real.exp (b ^ 2 * s ^ 2 / 2)) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp_of_le; gcongr

  have hExpInt : ∀ i : Fin d, ∀ s : ℝ,
      Integrable (fun ω => Real.exp (s * X ω i)) μ := by
    intro i s
    exact exp_individual_integrable μ d (fun i ω => X ω i) b hComp_b hASM i s

  have hMemLp : ∀ i : Fin d, MemLp (fun ω => X ω i) 2 μ := by
    intro i
    rw [memLp_two_iff_integrable_sq (hASM i)]
    have hexp_pos := hExpInt i 1
    have hexp_neg := hExpInt i (-1)
    have h_abs_pow := ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul
      one_ne_zero hexp_pos hexp_neg 2
    convert h_abs_pow using 1; ext ω; rw [sq_abs]

  exact (hMemLp j).integrable_mul (hMemLp k)

/-- The matrix whose `(j, k)` entry is `vⱼ v_k` coincides with `vecMulVec v v`. -/
lemma of_eq_vecMulVec (v : Fin d → ℝ) :
    Matrix.of (fun j k => v j * v k) = vecMulVec v v := by
  ext j k; simp [vecMulVec_apply, of_apply]

/-- Outer-product transform: `S (v v^⊤) S^⊤ = (S v)(S v)^⊤`. -/
lemma outer_product_transform (S : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    S * vecMulVec v v * S.transpose = vecMulVec (S.mulVec v) (S.mulVec v) := by
  rw [mul_vecMulVec, vecMulVec_mul]; congr 1
  rw [← mulVec_transpose]; simp [Matrix.transpose_transpose]

/-- Linear transforms commute with the empirical covariance:
`Σ̂(S X) = S Σ̂(X) S^⊤`. -/
lemma emp_cov_linear_transform {n : ℕ} {Ω : Type*}
    (X : Fin n → Ω → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (ω : Ω) :
    empiricalCovariance (fun i ω => S.mulVec (X i ω)) ω =
      S * empiricalCovariance X ω * S.transpose := by
  simp only [empiricalCovariance]
  rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [of_eq_vecMulVec, of_eq_vecMulVec, outer_product_transform]

/-- Conjugated-covariance integral identity:
`E[(S X)ⱼ (S X)_k] = (S Σ S^⊤)ⱼ_k`. -/
lemma integral_mulVec_eq_conjugated_cov
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin d → ℝ)
    (S covMat : Matrix (Fin d) (Fin d) ℝ)
    (hcov : ∀ (j k : Fin d), ∫ ω, X ω j * X ω k ∂μ = covMat j k)
    (hSG : IsSubGaussianVec μ X (matrixOpNorm covMat))
    (j k : Fin d) :
    ∫ ω, (S.mulVec (X ω)) j * (S.mulVec (X ω)) k ∂μ =
      (S * covMat * S.transpose) j k := by
  simp only [mulVec, dotProduct]
  have hInt : ∀ (a b : Fin d), Integrable (fun ω => X ω a * X ω b) μ :=
    subgaussian_integrable_products μ X _ hSG
  conv_lhs => arg 2; ext ω; rw [Finset.sum_mul_sum]
  have hint_term : ∀ (c c' : Fin d),
      Integrable (fun ω => S j c * X ω c * (S k c' * X ω c')) μ := by
    intro c c'
    have : (fun ω => S j c * X ω c * (S k c' * X ω c')) =
           fun ω => (S j c * S k c') * (X ω c * X ω c') := by ext ω; ring
    rw [this]; exact (hInt c c').const_mul _
  rw [integral_finset_sum _ (fun c _ => integrable_finset_sum _ (fun c' _ => hint_term c c'))]
  simp_rw [integral_finset_sum _ (fun c' _ => hint_term _ c')]
  simp_rw [show ∀ (c c' : Fin d), (fun ω => S j c * X ω c * (S k c' * X ω c')) =
    (fun ω => (S j c * S k c') * (X ω c * X ω c')) from fun c c' => by ext ω; ring]
  simp_rw [integral_const_mul, hcov]
  simp only [mul_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro c' _
  ring








/-- Numerical bound `e^{16} ≥ 289`, obtained from the first few terms of the Taylor series. -/
lemma exp_16_ge_289 : (289 : ℝ) ≤ Real.exp 16 := by
  have h : (0 : ℝ) ≤ 16 := by norm_num
  have := Real.sum_le_exp_of_nonneg h 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  norm_num at this
  linarith

/-- Numerical bound `288 ≤ e^{16}`. -/
lemma h288_le_exp16 : (288 : ℝ) ≤ Real.exp 16 :=
  le_trans (by norm_num : (288 : ℝ) ≤ 289) exp_16_ge_289

/-- `288^d ≤ exp(16 d)`, used to absorb the covering-number factor into the exponential. -/
lemma h288d_le_exp16d (d : ℕ) : (288 : ℝ) ^ d ≤ Real.exp (16 * ↑d) := by
  calc (288 : ℝ) ^ d ≤ (Real.exp 16) ^ d := by
        gcongr; exact h288_le_exp16
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

/-- Algebraic verification that the right-hand side of the general concentration bound,
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
    · have hsq : (32 * c) ^ 2 ≥ 32 * c := by nlinarith
      rw [min_eq_right hsq.le]
      have : ↑n / 2 * (32 * c) ≥ ↑n / 2 * (32 * (r / ↑n)) := by nlinarith
      linarith [show ↑n / 2 * (32 * (r / ↑n)) = 16 * r from by field_simp; ring]
    · push Not at h
      have hsq : (32 * c) ^ 2 ≤ 32 * c := by nlinarith
      rw [min_eq_left hsq]
      have hrn_nn : 0 ≤ r / ↑n := le_of_lt (div_pos hr_pos hn_pos)
      have hcsq : c ^ 2 ≥ r / ↑n := by
        have h1 : Real.sqrt (r / ↑n) ≤ c := hc_ge_sqrt
        have h2 : 0 ≤ Real.sqrt (r / ↑n) := Real.sqrt_nonneg _
        have h3 : (Real.sqrt (r / ↑n)) ^ 2 = r / ↑n := Real.sq_sqrt hrn_nn
        nlinarith [sq_nonneg (c - Real.sqrt (r / ↑n))]
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


end Rigollet.Chapter4.Thm_4_6

end
