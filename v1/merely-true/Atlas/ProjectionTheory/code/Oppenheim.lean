/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped Matrix

namespace Oppenheim

/-- A real quadratic form $Q$ is *indefinite* if it has mixed signature, i.e. it attains both
strictly positive and strictly negative values. -/
def IsIndefinite {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) : Prop :=
  (∃ v : Fin n → ℝ, Q v > 0) ∧ (∃ v : Fin n → ℝ, Q v < 0)

/-- A real quadratic form $Q$ is *proportional to an integer form* if there exist a scalar
$c \in \mathbb{R}$ and an integer matrix $M$ such that the Gram matrix of $Q$ equals
$c \cdot M$ (i.e. the coefficients of $Q$ all lie in $\mathbb{Z}\alpha$ for some $\alpha$). -/
def IsProportionalToIntegerForm {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ)) : Prop :=
  ∃ (c : ℝ) (M : Matrix (Fin n) (Fin n) ℤ),
    QuadraticMap.toMatrix' Q = c • (M.map (Int.cast : ℤ → ℝ))



end Oppenheim
