/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Polynomial.GaussLucas

open Finset BigOperators

theorem convexHull_finset_eq_convex_combinations (S : Finset ℂ) :
    (convexHull ℝ (↑S : Set ℂ)) =
      { x : ℂ | ∃ w : ℂ → ℝ, (∀ a ∈ S, 0 ≤ w a) ∧
        ∑ a ∈ S, w a = 1 ∧ ∑ a ∈ S, w a • a = x } := by
  ext x
  exact Finset.mem_convexHull'

open Polynomial Complex
open scoped Polynomial ComplexConjugate

namespace Polynomial

theorem gauss_lucas {P : ℂ[X]} (hP : 0 < P.degree) :
    P.derivative.rootSet ℂ ⊆ convexHull ℝ (P.rootSet ℂ) :=
  rootSet_derivative_subset_convexHull_rootSet hP

end Polynomial
