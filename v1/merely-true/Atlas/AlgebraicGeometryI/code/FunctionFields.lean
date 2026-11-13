/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.NakayamaApplications
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.NumberTheory.RamificationInertia.Basic

noncomputable section

open Module Ideal

section FunctionField

end FunctionField

section MorphismDegree

variable (B A : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
  [Algebra B A] [FaithfulSMul B A]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The degree of a finite morphism of integral domains, defined via the
fraction-field extension `[K(A) : K(B)]`. -/
def morphismDegree : ℕ := finrank (FractionRing B) (FractionRing A)

omit [IsDomain B] in
/-- For an algebraic extension of domains, the fraction-field degree agrees with
the module rank: `[K(A) : K(B)] = rank_B A`. -/
theorem morphismDegree_eq_finrank [Algebra.IsAlgebraic B A] :
    morphismDegree B A = finrank B A :=
  Algebra.IsAlgebraic.finrank_of_isFractionRing B (FractionRing B) A (FractionRing A)

end MorphismDegree

section FiberBound

end FiberBound

section Ramification

end Ramification
