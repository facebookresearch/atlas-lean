/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.DedekindCurve
import Atlas.AlgebraicGeometryI.code.SheafCohomology

open scoped TensorProduct
open nonZeroDivisors
open RiemannRochCurves DedekindCurve
open UniqueFactorizationMonoid

noncomputable section

namespace RiemannRochDedekind


/-- `H^1` of the structure sheaf for a Dedekind curve, repackaged at the
top-level of this namespace. -/
def h1_O (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  DedekindCurve.h1_O k A

/-- `h^1(𝒪) = dim_k Ω_{A/k}`, i.e. the arithmetic genus, for a Dedekind curve. -/
theorem h1_O_eq_genus :
    ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
      [IsDedekindDomain A] [Algebra k A] [Module.Finite k A],
      h1_O k A = Module.finrank k (Ω[A⁄k]) :=
  DedekindCurve.h1_O_eq_genus

/-- `H^1` of a skyscraper sheaf on a Dedekind curve, repackaged. -/
def h1_sky (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  DedekindCurve.h1_sky k A

/-- The `H^1` of a skyscraper sheaf vanishes. -/
theorem h1_sky_eq_zero :
    ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
      [IsDedekindDomain A] [Algebra k A] [Module.Finite k A],
      h1_sky k A = 0 :=
  DedekindCurve.h1_sky_eq_zero



end RiemannRochDedekind
