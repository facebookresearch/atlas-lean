/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CartierDivisorScheme
import Atlas.AlgebraicGeometryI.code.CartierDivisorGroup
import Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors
import Atlas.AlgebraicGeometryI.code.DivisorsPicard
import Atlas.AlgebraicGeometryI.code.WeilDivisor
import Atlas.AlgebraicGeometryI.code.PicardGroup
import Atlas.AlgebraicGeometryI.code.AffinePushforwardCohomology
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Flat.Localization
open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace Lec14DivisorsPicard

/-- Cartier divisor group `DC(X)` of an integral scheme `X` (Def 30, Lec 14):
abbreviation for `CartierDivisorScheme.CartierDivisorGroupScheme X`. -/
abbrev cartierDivisorGroupScheme (X : Scheme.{u}) [IsIntegral X] :=
  CartierDivisorScheme.CartierDivisorGroupScheme X

section DedekindCartier
open scoped nonZeroDivisors
variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- Algebraic form of the Cartier divisor group attached to a Dedekind domain `A`
with fraction field `K`. -/
abbrev cartierDivisorGroupAlg := CartierDivisorGroup A K

end DedekindCartier

section WeilCartierGeneral
open LocallyFactorialDivisors

variable (R : Type*) [CommRing R] [IsDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

end WeilCartierGeneral

section WeilCartierDedekind
open scoped nonZeroDivisors
open IsDedekindDomain
variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

end WeilCartierDedekind

section PicardGroup
open scoped nonZeroDivisors
variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

end PicardGroup

section LineBundlesCartier
open InvertibleSheaves
variable (R : Type u) [CommRing R]

/-- Corollary 19 (Lec 14): the Picard group `Pic(R)` of invertible sheaves on `Spec R`
is naturally a commutative group under tensor product. -/
@[reducible]
def corollary_19_invertible_sheaves_group (R : Type*) [CommRing R] :
    CommGroup (CommRing.Pic R) := inferInstance

end LineBundlesCartier

section DivisorDegree

/-- Degree of a Weil divisor `D = Σ nᵢ [Pᵢ]`: the integer sum of the coefficients `Σ nᵢ`. -/
def weilDivisorDegree {Y : Type*} [DecidableEq Y] (D : WeilDivisor.Group Y) : ℤ :=
  D.sum (fun _ n => n)

/-- The degree of the zero divisor is `0`. -/
theorem weilDivisorDegree_zero {Y : Type*} [DecidableEq Y] :
    weilDivisorDegree (0 : WeilDivisor.Group Y) = 0 := by
  simp [weilDivisorDegree, Finsupp.sum]

/-- The degree map is additive: `deg(D₁ + D₂) = deg(D₁) + deg(D₂)`. -/
theorem weilDivisorDegree_add {Y : Type*} [DecidableEq Y] (D₁ D₂ : WeilDivisor.Group Y) :
    weilDivisorDegree (D₁ + D₂) = weilDivisorDegree D₁ + weilDivisorDegree D₂ := by
  simp only [weilDivisorDegree]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]

/-- Packaged `AddMonoidHom` version of `weilDivisorDegree`. -/
def degreeHom {Y : Type*} [DecidableEq Y] : WeilDivisor.Group Y →+ ℤ where
  toFun := weilDivisorDegree
  map_zero' := weilDivisorDegree_zero
  map_add' := weilDivisorDegree_add

/-- Degree is invariant under linear equivalence: assuming that principal divisors
have degree zero, linearly equivalent divisors `D₁ ∼ D₂` satisfy `deg D₁ = deg D₂`. -/
theorem degree_eq_of_linearlyEquiv {Y : Type*} [DecidableEq Y]
    (D₁ D₂ : WeilDivisor.Group Y)
    (IsPrincipal : WeilDivisor.Group Y → Prop)
    (h_princ_deg : ∀ P, IsPrincipal P → weilDivisorDegree P = 0)
    (h_equiv : IsPrincipal (D₁ - D₂)) :
    weilDivisorDegree D₁ = weilDivisorDegree D₂ := by
  have h := h_princ_deg _ h_equiv
  have hsub : D₁ - D₂ = D₁ + (-D₂) := sub_eq_add_neg D₁ D₂
  rw [hsub, weilDivisorDegree_add] at h
  have hneg : weilDivisorDegree (-D₂) = -weilDivisorDegree D₂ := by
    simp only [weilDivisorDegree]
    rw [Finsupp.sum_neg_index (by simp)]
    simp [Finsupp.sum, Finset.sum_neg_distrib]
  linarith

end DivisorDegree

end Lec14DivisorsPicard
