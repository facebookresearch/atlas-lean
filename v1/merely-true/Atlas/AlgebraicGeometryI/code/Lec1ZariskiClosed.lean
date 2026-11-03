/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

open MvPolynomial

/-- A Zariski closed subset of `k^n` is the zero set of a finite collection of polynomials in
`k[x_1, …, x_n]`. (Definition 1, Lecture 1.) -/
def IsZariskiClosed {n : ℕ} {k : Type*} [Field k] (S : Set (Fin n → k)) : Prop :=
  ∃ T : Finset (MvPolynomial (Fin n) k),
    S = {x : Fin n → k | ∀ f ∈ T, MvPolynomial.eval x f = 0}
