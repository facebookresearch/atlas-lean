/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Prod

noncomputable section

namespace CechCohomologyCurves

/-- Čech data for a sheaf relative to a cover by two open sets `U₁, U₂`: the `k`-vector spaces of
sections on `U₁`, `U₂`, `U₁ ∩ U₂`, together with the two restriction maps. -/
structure CechDataTwoOpen (k : Type*) [Field k] where
  sectionsU1 : Type*
  sectionsU2 : Type*
  sectionsU12 : Type*
  [addCommGroupU1 : AddCommGroup sectionsU1]
  [moduleU1 : Module k sectionsU1]
  [addCommGroupU2 : AddCommGroup sectionsU2]
  [moduleU2 : Module k sectionsU2]
  [addCommGroupU12 : AddCommGroup sectionsU12]
  [moduleU12 : Module k sectionsU12]
  restriction1 : sectionsU1 →ₗ[k] sectionsU12
  restriction2 : sectionsU2 →ₗ[k] sectionsU12

attribute [instance] CechDataTwoOpen.addCommGroupU1 CechDataTwoOpen.moduleU1
  CechDataTwoOpen.addCommGroupU2 CechDataTwoOpen.moduleU2
  CechDataTwoOpen.addCommGroupU12 CechDataTwoOpen.moduleU12

variable {k : Type*} [Field k]

/-- The Čech differential `(s₁, s₂) ↦ s₁|_{U₁₂} - s₂|_{U₁₂}` on a two-open cover. -/
def cechDifferential (D : CechDataTwoOpen k) :
    (D.sectionsU1 × D.sectionsU2) →ₗ[k] D.sectionsU12 :=
  LinearMap.coprod D.restriction1 (-D.restriction2)

/-- The 0-th Čech cohomology of a two-open cover, computed as the kernel of the Čech
differential. -/
def cechH0 (D : CechDataTwoOpen k) : Submodule k (D.sectionsU1 × D.sectionsU2) :=
  LinearMap.ker (cechDifferential D)

/-- The 1-st Čech cohomology of a two-open cover, computed as the cokernel of the Čech
differential. -/
def cechH1 (D : CechDataTwoOpen k) :=
  D.sectionsU12 ⧸ LinearMap.range (cechDifferential D)

/-- The first Čech cohomology inherits an additive commutative group structure from the quotient. -/
instance cechH1.addCommGroup (D : CechDataTwoOpen k) : AddCommGroup (cechH1 D) :=
  Submodule.Quotient.addCommGroup _

/-- The first Čech cohomology is a `k`-module via the quotient structure. -/
instance cechH1.module (D : CechDataTwoOpen k) : Module k (cechH1 D) :=
  Submodule.Quotient.module _

/-- The dimension `h⁰` of the 0-th Čech cohomology. -/
def h0 (D : CechDataTwoOpen k) : ℕ :=
  Module.finrank k (cechH0 D)

/-- The dimension `h¹` of the first Čech cohomology. -/
def h1 (D : CechDataTwoOpen k) : ℕ :=
  Module.finrank k (cechH1 D)

/-- The Euler characteristic `χ = h⁰ - h¹` of a two-open Čech datum. -/
def eulerCharacteristic (D : CechDataTwoOpen k) : ℤ :=
  (h0 D : ℤ) - (h1 D : ℤ)

/-- Čech data for a line bundle on a curve, packaged with the degree of the line bundle and the
genus of the curve. -/
structure LineBundleCurveData (k : Type*) [Field k] extends CechDataTwoOpen k where
  deg : ℤ
  genus : ℕ



end CechCohomologyCurves

end
