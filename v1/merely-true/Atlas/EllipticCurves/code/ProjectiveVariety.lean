/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Irreducible

open MvPolynomial Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {σ : Type*}

/-- A set of multivariate polynomials over `k` is a set of homogeneous
polynomials if every member is homogeneous of some degree. -/
def IsSetOfHomogeneousPolynomials (S : Set (MvPolynomial σ k)) : Prop :=
  ∀ p ∈ S, ∃ n : ℕ, p.IsHomogeneous n

/-- The projective zero locus over `K` of a set `S` of `k`-polynomials: the set
of points in `ℙ(σ → K)` whose representative satisfies `p = 0` for every
`p ∈ S`. -/
def projectiveZeroLocus (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K]
    (S : Set (MvPolynomial σ k)) : Set (Projectivization K (σ → K)) :=
  {P | ∀ p ∈ S, aeval P.rep p = 0}

/-- Membership in the projective zero locus unfolds to: every polynomial in `S`
vanishes on a representative of `P`. -/
@[simp]
theorem mem_projectiveZeroLocus_iff (S : Set (MvPolynomial σ k))
    (P : Projectivization K (σ → K)) :
    P ∈ projectiveZeroLocus k K S ↔ ∀ p ∈ S, aeval P.rep p = 0 :=
  Iff.rfl

/-- A subset `V` of projective space is a projective algebraic set (defined
over `k`) if it is the projective zero locus of some set of homogeneous
`k`-polynomials. -/
def IsProjectiveAlgebraicSet (k : Type*) [Field k] [Algebra k K]
    (V : Set (Projectivization K (σ → K))) : Prop :=
  ∃ S : Set (MvPolynomial σ k),
    IsSetOfHomogeneousPolynomials S ∧ V = projectiveZeroLocus k K S

/-- A nonempty projective algebraic set is irreducible (as an algebraic set over
`k`) if it cannot be expressed as a proper union of two projective algebraic
sets. -/
def IsIrreducibleProjectiveAlgebraicSet (k : Type*) [Field k] [Algebra k K]
    (V : Set (Projectivization K (σ → K))) : Prop :=
  IsProjectiveAlgebraicSet k V ∧
  V.Nonempty ∧
  ∀ V₁ V₂ : Set (Projectivization K (σ → K)),
    IsProjectiveAlgebraicSet k V₁ →
    IsProjectiveAlgebraicSet k V₂ →
    V = V₁ ∪ V₂ → V = V₁ ∨ V = V₂

/-- A projective variety over `k` is an irreducible projective algebraic set
defined over `k`. -/
def IsProjectiveVariety (k : Type*) [Field k] [Algebra k K]
    (V : Set (Projectivization K (σ → K))) : Prop :=
  IsIrreducibleProjectiveAlgebraicSet k V

end
