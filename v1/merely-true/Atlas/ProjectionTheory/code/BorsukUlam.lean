/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace BorsukUlam

/-- The unit `n`-sphere `S^n = { x ∈ ℝ^{n+1} : ‖x‖ = 1 }`, regarded as a subset of
the Euclidean space `EuclideanSpace ℝ (Fin (n + 1))`. -/
def Sphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The unit sphere is closed under negation: if `x ∈ S^n`, then `−x ∈ S^n`. This is
used to make sense of the antipodal hypothesis in Borsuk–Ulam. -/
lemma neg_mem_sphere {n : ℕ} {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ Sphere n) : -x ∈ Sphere n := by
  simp only [Sphere, Metric.mem_sphere, dist_zero_right] at hx ⊢
  rw [norm_neg]
  exact hx



end BorsukUlam
