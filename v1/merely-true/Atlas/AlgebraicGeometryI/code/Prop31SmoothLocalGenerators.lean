/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maps

noncomputable section

/-- The maximal ideal of polynomials in `k[X_1, ..., X_n]` vanishing at the point `x`. -/
def maxIdealOfPoint_P31 {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : Ideal (MvPolynomial (Fin n) k) :=
  RingHom.ker (MvPolynomial.eval x)

/-- The maximal ideal at a point is genuinely maximal. -/
instance maxIdealOfPoint_P31_isMaximal {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : (maxIdealOfPoint_P31 x).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (fun c => ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩)

/-- The image of the maximal ideal at `x` in the quotient `k[X]/I`, for `I` contained
in that maximal ideal. -/
def maxIdealInQuotient_P31 {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (_ : I ≤ maxIdealOfPoint_P31 x) :
    Ideal (MvPolynomial (Fin n) k ⧸ I) :=
  Ideal.map (Ideal.Quotient.mk I) (maxIdealOfPoint_P31 x)

/-- The image maximal ideal in the quotient is maximal. -/
instance maxIdealInQuotient_P31_isMaximal {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_P31 x) :
    (maxIdealInQuotient_P31 I x hI).IsMaximal := by
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le
  · exact Ideal.Quotient.mk_surjective
  · rwa [Ideal.mk_ker]

/-- The image maximal ideal in the quotient is prime. -/
instance maxIdealInQuotient_P31_isPrime {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_P31 x) :
    (maxIdealInQuotient_P31 I x hI).IsPrime :=
  (maxIdealInQuotient_P31_isMaximal I x hI).isPrime

/-- The local ring of the variety `V(I)` at the point `x`. -/
abbrev localRingAtPoint_P31 {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_P31 x) :=
  Localization.AtPrime (maxIdealInQuotient_P31 I x hI)

/-- The Jacobian matrix of `f_1, ..., f_m ∈ k[X_1, ..., X_n]` at the point `x ∈ k^n`. -/
def jacobianMatrix_P31 {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (x : Fin n → k) :
    Matrix (Fin m) (Fin n) k :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (f i))






end
