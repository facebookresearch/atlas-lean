/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_6
import Atlas.HighDimensionalStatistics.code.Chapter4.Cor_4_9

open MeasureTheory ProbabilityTheory Matrix Real Finset BigOperators

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {d : ℕ}

namespace EuclideanBridge

/-- Forget the Euclidean (`L²`) structure, viewing a vector as a plain function `Fin d → ℝ`. -/
def euclideanToFun : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ) := WithLp.equiv 2 (Fin d → ℝ)

/-- Equip a plain function `Fin d → ℝ` with the Euclidean (`L²`) structure. -/
def funToEuclidean : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 (Fin d → ℝ)).symm

/-- `euclideanToFun` left-inverts `funToEuclidean`. -/
@[simp] lemma euclideanToFun_funToEuclidean (v : Fin d → ℝ) :
    euclideanToFun (funToEuclidean v) = v :=
  (WithLp.equiv 2 (Fin d → ℝ)).apply_symm_apply v

/-- `funToEuclidean` left-inverts `euclideanToFun`. -/
@[simp] lemma funToEuclidean_euclideanToFun (v : EuclideanSpace ℝ (Fin d)) :
    funToEuclidean (euclideanToFun v) = v :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm_apply_apply v

/-- Componentwise, `euclideanToFun` is the identity. -/
@[simp] lemma euclideanToFun_apply (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    euclideanToFun v i = v i := rfl

/-- Componentwise, `funToEuclidean` is the identity. -/
@[simp] lemma funToEuclidean_apply (v : Fin d → ℝ) (i : Fin d) :
    funToEuclidean v i = v i := rfl

end EuclideanBridge
