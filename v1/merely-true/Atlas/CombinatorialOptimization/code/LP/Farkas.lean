/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix


lemma clm_repr {m : ℕ} (f : (Fin m → ℝ) →L[ℝ] ℝ) (v : Fin m → ℝ) :
    f v = dotProduct (fun i => f (Pi.single i 1 : Fin m → ℝ)) v := by
  simp only [dotProduct]
  have hv : v = ∑ i : Fin m, (v i) • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Finset.mem_univ]
  conv_lhs => rw [hv]
  rw [map_sum]; congr 1; ext i; rw [map_smul, smul_eq_mul, mul_comm]

