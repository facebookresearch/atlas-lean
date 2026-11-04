/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2

open MeasureTheory Matrix Real Finset

noncomputable section

/-- The operator (spectral) norm of a real matrix, defined via the associated continuous
linear map on Euclidean spaces. -/
def matrixOpNorm {d T : ℕ} (A : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- A random matrix `F : Ω → Matrix (Fin d) (Fin T) ℝ` is *sub-Gaussian with proxy
variance* `σsq` if for every pair of unit vectors `u ∈ ℝ^d`, `v ∈ ℝ^T`, the random scalar
$u^\top F v$ is sub-Gaussian with proxy variance `σsq`. -/
def IsSubGaussianMatrix {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}
    (F : Ω → Matrix (Fin d) (Fin T) ℝ) (σsq : ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (u : EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin T)),
    ‖u‖ = 1 → ‖v‖ = 1 →
    IsSubGaussian (fun ω => dotProduct (EuclideanSpace.equiv (Fin d) ℝ u)
      ((F ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ v))) σsq μ

/-- A sub-Gaussian matrix observation model: an unknown signal `Θstar` is observed with
additive sub-Gaussian noise `F` having proxy variance `σsq`. -/
structure SubGaussianMatrixModel (Ω : Type*) [MeasurableSpace Ω]
    (d T : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] where
  Θstar : Matrix (Fin d) (Fin T) ℝ
  F : Ω → Matrix (Fin d) (Fin T) ℝ
  σsq : ℝ
  hF : IsSubGaussianMatrix F σsq μ

/-- The observed matrix in the sub-Gaussian model: `y = Θstar + F(ω)`. -/
def SubGaussianMatrixModel.observed {Ω : Type*} [MeasurableSpace Ω]
    {d T : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (model : SubGaussianMatrixModel Ω d T μ) (ω : Ω) : Matrix (Fin d) (Fin T) ℝ :=
  model.Θstar + model.F ω

/-- A singular value decomposition record for a `d × T` matrix: rank `r`, singular values
`σval`, and the corresponding left/right singular vectors `u`, `v`. -/
structure SVD (d T : ℕ) where
  r : ℕ
  hr : r ≤ min d T
  σval : Fin r → ℝ
  u : Fin r → (Fin d → ℝ)
  v : Fin r → (Fin T → ℝ)
  σval_nonneg : ∀ j, 0 ≤ σval j

/-- Reconstruct a matrix from its SVD data:
$\sum_j \sigma_j\, u_j v_j^\top$. -/
def SVD.toMatrix {d T : ℕ} (S : SVD d T) : Matrix (Fin d) (Fin T) ℝ :=
  ∑ j : Fin S.r, S.σval j • vecMulVec (S.u j) (S.v j)

/-- `S` is a singular value decomposition of `A` when `A` equals the matrix reconstructed
from `S`. -/
def SVD.IsDecompOf {d T : ℕ} (S : SVD d T) (A : Matrix (Fin d) (Fin T) ℝ) : Prop :=
  A = S.toMatrix

/-- Apply singular value thresholding at level `2τ` to an SVD:
$\sum_j \sigma_j \mathbf{1}(|\sigma_j| > 2\tau)\, u_j v_j^\top$. -/
def SVD.svtMatrix {d T : ℕ} (S : SVD d T) (τ : ℝ) : Matrix (Fin d) (Fin T) ℝ :=
  ∑ j : Fin S.r, (if |S.σval j| > 2 * τ then S.σval j else 0) •
    vecMulVec (S.u j) (S.v j)

/-- `Θhat` is the singular value thresholding (SVT) estimator at threshold `τ` for the
observation `y` if it arises from thresholding the singular values of some SVD of `y`. -/
def IsSVTEstimator {d T : ℕ} (y Θhat : Matrix (Fin d) (Fin T) ℝ) (τ : ℝ) : Prop :=
  ∃ S : SVD d T, S.IsDecompOf y ∧ Θhat = S.svtMatrix τ

/-- Constructive form of the singular value thresholding estimator, given an explicit SVD `S`
and threshold `τ`. -/
def singularValueThresholding {d T : ℕ} (S : SVD d T) (τ : ℝ) :
    Matrix (Fin d) (Fin T) ℝ :=
  S.svtMatrix τ

/-- **Definition 4.1** (Singular Value Thresholding estimator): `Θhat` is an SVT estimator of
threshold `τ` for the observation `y`. -/
def definition_4_1 {d T : ℕ} (y Θhat : Matrix (Fin d) (Fin T) ℝ) (τ : ℝ) : Prop :=
  IsSVTEstimator y Θhat τ

end
