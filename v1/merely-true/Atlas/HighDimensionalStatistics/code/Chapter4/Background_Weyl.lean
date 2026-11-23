/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1

open Matrix Real Finset

noncomputable section

/-- An SVD is *ordered* when its singular values are listed in nonincreasing order. -/
def SVD.IsOrdered {d T : ℕ} (S : SVD d T) : Prop :=
  ∀ i j : Fin S.r, i ≤ j → S.σval j ≤ S.σval i

/-- The SVD's recorded singular values coincide with the true (mathlib-defined)
singular values of the linear map associated to `A`. -/
def SVD.HasTrueSingularValues {d T : ℕ} (S : SVD d T)
    (A : Matrix (Fin d) (Fin T) ℝ) : Prop :=
  ∀ k : Fin S.r, S.σval k = (toEuclideanLin A).singularValues k.val

/-- The operator norm is symmetric under swapping the arguments of a subtraction:
$\|B - A\|_{op} = \|A - B\|_{op}$. -/
lemma matrixOpNorm_neg_sub {d T : ℕ} (A B : Matrix (Fin d) (Fin T) ℝ) :
    matrixOpNorm (B - A) = matrixOpNorm (A - B) := by
  unfold matrixOpNorm
  rw [show B - A = -(A - B) from (neg_sub A B).symm, map_neg,
      show (-toEuclideanLin (A - B)).toContinuousLinearMap =
           -(toEuclideanLin (A - B)).toContinuousLinearMap from map_neg _ _,
      ContinuousLinearMap.opNorm_neg]





end
