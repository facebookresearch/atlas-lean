/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.MainLemma2F

open Finset

namespace LineSumDecomposition

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- **`L²` bound for a sum of line indicators.** Let `ℒ` be a finite collection of lines
in `𝔽_p × 𝔽_p`, each of size `p` and pairwise intersecting in at most one point. For
`f = ∑_{L ∈ ℒ} 1_L`, the `L²` norm decomposes as `f = f₀ + f_h` with `f₀` constant and
$\|f\|_2^2 = \|f_0\|_2^2 + \|f_h\|_2^2 \le |\mathcal L|^2 + |\mathcal L| \cdot p$. -/
theorem norm_sq_lineSumFn_le (ℒ : Finset (Finset (ZMod p × ZMod p)))
    (hlines : ∀ L ∈ ℒ, L.card = p)
    (hinter : ∀ L₁ ∈ ℒ, ∀ L₂ ∈ ℒ, L₁ ≠ L₂ → (L₁ ∩ L₂).card ≤ 1) :
    ∑ x : ZMod p × ZMod p, (lineSumFn ℒ x) ^ 2 ≤
    (ℒ.card : ℝ) ^ 2 + (ℒ.card : ℝ) * (p : ℝ) := by

  have hdecomp : ∀ x : ZMod p × ZMod p,
      (lineSumFn ℒ x) ^ 2 =
      (lineSumConst ℒ) ^ 2 + 2 * lineSumConst ℒ * lineSumHighFreq ℒ x +
      (lineSumHighFreq ℒ x) ^ 2 := by
    intro x
    have h := decomposition ℒ x
    rw [h]; ring
  simp_rw [hdecomp, Finset.sum_add_distrib]

  have hcross : ∑ x : ZMod p × ZMod p,
      2 * lineSumConst ℒ * lineSumHighFreq ℒ x = 0 := by
    rw [show (fun x => 2 * lineSumConst ℒ * lineSumHighFreq ℒ x) =
        (fun x => 2 * (lineSumConst ℒ * lineSumHighFreq ℒ x)) from by ext x; ring]
    rw [← Finset.mul_sum]
    rw [orthogonal_const_highFreq ℒ hlines]
    ring
  rw [hcross, add_zero]

  have h_const := norm_sq_const_eq ℒ
  have h_high := norm_sq_highFreq_le ℒ hlines hinter
  linarith

end LineSumDecomposition
