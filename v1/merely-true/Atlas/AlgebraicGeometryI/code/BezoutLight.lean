/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Atlas.AlgebraicGeometryI.code.BezoutTheorem

set_option maxHeartbeats 400000

open MvPolynomial

/-- The degree-`n` piece of the homogeneous quotient ring `k[x₀, x₁, x₂] / I`, presented as the
quotient of the space of degree-`n` homogeneous polynomials by the corresponding piece of `I`. -/
noncomputable abbrev homogQuotPiece (k : Type*) [Field k]
    (I : Ideal (MvPolynomial (Fin 3) k)) (n : ℕ) :=
  (homogeneousSubmodule (Fin 3) k n) ⧸
    Submodule.comap (homogeneousSubmodule (Fin 3) k n).subtype (I.restrictScalars k)

/-- Predicate stating that the bivariate polynomial `f ∈ k[X][Y]` has total degree at most `n`,
i.e. for each coefficient `f.coeff i ∈ k[X]` the sum of its `X`-degree and `Y`-index `i` is `≤ n`. -/
def hasTotalDegreeAtMost {k : Type*} [CommSemiring k]
    (f : Polynomial (Polynomial k)) (n : ℕ) : Prop :=
  ∀ i, (f.coeff i).natDegree + i ≤ n



