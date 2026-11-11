/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 400000

noncomputable section

open MvPolynomial Module

namespace LocalIntersection

variable (k : Type*) [Field k]

/-- The quotient ring `k[x,y]/(f,g)` used to define intersection multiplicities. -/
abbrev IntersectionQuotient (f g : MvPolynomial (Fin 2) k) :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span ({f, g} : Set (MvPolynomial (Fin 2) k))

/-- Multiplication by `x` as a `k`-linear endomorphism of the intersection quotient. -/
def mulByXOp (f g : MvPolynomial (Fin 2) k) :
    End k (IntersectionQuotient k f g) :=
  Algebra.lmul k _ (Ideal.Quotient.mk _ (X 0))

/-- Multiplication by `y` as a `k`-linear endomorphism of the intersection quotient. -/
def mulByYOp (f g : MvPolynomial (Fin 2) k) :
    End k (IntersectionQuotient k f g) :=
  Algebra.lmul k _ (Ideal.Quotient.mk _ (X 1))

/-- The multiplication-by-`x` and multiplication-by-`y` endomorphisms commute. -/
theorem mulByXOp_mul_mulByYOp (f g : MvPolynomial (Fin 2) k) :
    mulByXOp k f g * mulByYOp k f g = mulByYOp k f g * mulByXOp k f g := by
  unfold mulByXOp mulByYOp
  simp only [← map_mul (Algebra.lmul k _)]
  exact congr_arg _ (mul_comm _ _)

/-- The common generalized eigenspace where `x` acts with generalized eigenvalue `a`
and `y` with generalized eigenvalue `b`. -/
def commonGenEigenspace (f g : MvPolynomial (Fin 2) k) (a b : k) :
    Submodule k (IntersectionQuotient k f g) :=
  (mulByXOp k f g).maxGenEigenspace a ⊓ (mulByYOp k f g).maxGenEigenspace b

/-- The local intersection multiplicity of `f` and `g` at the point `(a,b)` is the
`k`-dimension of the common generalized eigenspace (Def 13, Lec 5). -/
def localIntersectionMultiplicity (f g : MvPolynomial (Fin 2) k) (a b : k) : ℕ :=
  finrank k (commonGenEigenspace k f g a b)

/-- The total intersection number of `f` and `g` is the `k`-dimension of the
intersection quotient `k[x,y]/(f,g)`. -/
def totalIntersectionNumberMv (f g : MvPolynomial (Fin 2) k) : ℕ :=
  finrank k (IntersectionQuotient k f g)

/-- The local intersection multiplicity equals the `k`-dimension of the common
generalized eigenspace, by definition. -/
theorem localIntersectionMultiplicity_eq_finrank
    (f g : MvPolynomial (Fin 2) k) (a b : k) :
    localIntersectionMultiplicity k f g a b =
    finrank k ↥((mulByXOp k f g).maxGenEigenspace a ⊓
                (mulByYOp k f g).maxGenEigenspace b) := by
  rfl

end LocalIntersection

end
