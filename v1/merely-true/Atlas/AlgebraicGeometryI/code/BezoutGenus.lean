/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.BezoutIntersection
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Module.SpanRank

noncomputable section

open Polynomial BezoutIntersection

namespace BezoutGenus

variable (k : Type*) [Field k]

/-- Bundle of data for a smooth projective curve over `k`: a Dedekind coordinate ring (as an
algebra over `k`) together with its arithmetic genus. -/
structure SmoothProjectiveCurveWithCoords (k : Type*) [Field k] where
  CoordinateRing : Type*
  [instCommRing : CommRing CoordinateRing]
  [instAlgebra : Algebra k CoordinateRing]
  [instIsDomain : IsDomain CoordinateRing]
  [instIsDedekind : IsDedekindDomain CoordinateRing]
  genus : ℕ

attribute [instance] SmoothProjectiveCurveWithCoords.instCommRing
  SmoothProjectiveCurveWithCoords.instAlgebra
  SmoothProjectiveCurveWithCoords.instIsDomain
  SmoothProjectiveCurveWithCoords.instIsDedekind


/-- The resultant of two bivariate polynomials `f, g ∈ k[X][X]`, viewed as a polynomial in `k[X]`. -/
def bivariateResultant (f g : k[X][X]) : k[X] :=
  Polynomial.resultant f g

/-- The arithmetic genus of a smooth plane curve of degree `d`, equal to `(d-1)(d-2)/2`. -/
def genusOfSmoothPlaneCurve (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

end BezoutGenus
