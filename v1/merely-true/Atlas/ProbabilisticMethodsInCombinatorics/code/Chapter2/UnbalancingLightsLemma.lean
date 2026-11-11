/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Powerset
set_option maxHeartbeats 800000

open MvPolynomial Finset

namespace UnbalancingLights

/-- The linear monomial $x_0 x_1 \cdots x_{k-1}$, encoded as the exponent vector that is
$1$ on every coordinate. -/
noncomputable def linearMonomial (k : ℕ) : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

/-- The class $\mathcal{P}_k$ of multivariate real polynomials in $k$ variables of total
degree at most $k$, with all coefficients bounded by $1$ in absolute value, and whose
coefficient at the linear monomial $x_1 \cdots x_k$ equals $1$. -/
def P_k (k : ℕ) : Set (MvPolynomial (Fin k) ℝ) :=
  { g | g.totalDegree ≤ k ∧
        (∀ m : Fin k →₀ ℕ, |g.coeff m| ≤ 1) ∧
        g.coeff (linearMonomial k) = 1 }



end UnbalancingLights
