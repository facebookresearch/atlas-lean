/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Away.Basic

open AlgebraicGeometry CategoryTheory

namespace PushforwardDirectLimit

variable {R : CommRingCat.{0}}

/-- The localisation `M[f⁻¹]` of an `R`-module `M` at the powers of `f`, packaged as a
`ModuleCat R`. -/
noncomputable def localizedModuleCat (M : ModuleCat.{0} R) (f : R) :
    ModuleCat.{0} R :=
  ModuleCat.of R (LocalizedModule (Submonoid.powers f) M)

/-- The image of `f ∈ R` as a global section of `Spec R` via the canonical isomorphism
`Γ(Spec R, ⊤) ≅ R`. -/
noncomputable def toSpecGlobal (f : R) : Γ(Spec R, ⊤) :=
  (ConcreteCategory.hom (Scheme.ΓSpecIso R).inv) f

/-- The open immersion of the basic open `D(f) ⊆ Spec R` into `Spec R`. -/
noncomputable def basicOpenInclusion (f : R) : ↑((Spec R).basicOpen (toSpecGlobal f)) ⟶ Spec R :=
  Scheme.Opens.ι ((Spec R).basicOpen (toSpecGlobal f))






end PushforwardDirectLimit
