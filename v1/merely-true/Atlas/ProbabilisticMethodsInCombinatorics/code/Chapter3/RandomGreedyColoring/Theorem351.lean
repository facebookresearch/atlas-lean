/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter3.RandomGreedyColoring.StructuralLemma
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
open Finset Fintype TwoColorableHypergraph

namespace TwoColorableHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Quantitative bound used in the analysis of Theorem 3.5.1: for $k \geq 2$,
$\tfrac{1}{8}(1 + 1/\log k) < 1$. -/
lemma one_eighth_bound (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℝ) / 8 * (1 + 1 / Real.log ↑k) < 1 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogk : Real.log 2 ≤ Real.log (↑k : ℝ) := by
    apply Real.log_le_log (by norm_num : (0:ℝ) < 2)
    exact_mod_cast hk
  have hlogk_pos : (0 : ℝ) < Real.log ↑k := by linarith
  have hlogk_bound : (0.6931471803 : ℝ) < Real.log ↑k := by linarith
  have h1 : 1 / Real.log ↑k < 1 / 0.6931471803 := by
    apply div_lt_div_of_pos_left one_pos (by positivity) hlogk_bound
  have h2 : (1:ℝ) / 0.6931471803 < 1.4428 := by norm_num
  linarith



end TwoColorableHypergraph
