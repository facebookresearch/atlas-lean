/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

set_option maxHeartbeats 1600000

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Hypercohomology

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
variable (D : Type*) [Category D] [Abelian D] [HasDerivedCategory D]

section Degreewise

variable (F : C ⥤ D) [F.Additive]

/-- Apply an additive functor `F : C ⥤ D` degreewise to a cochain complex,
producing the induced functor on cochain complexes. -/
def applyDegreewise : CochainComplex C ℤ ⥤ CochainComplex D ℤ :=
  F.mapHomologicalComplex (ComplexShape.up ℤ)

/-- Naive hypercohomology functor: apply `F` degreewise and then take homology in
degree `n`. Agrees with true hypercohomology only when `F` is exact or the input is
`F`-acyclic. -/
def naiveHypercohomologyFunctor (n : ℤ) : CochainComplex C ℤ ⥤ D :=
  applyDegreewise C D F ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n

end Degreewise

section TotalDerived

variable (F : C ⥤ D) [F.Additive]

/-- The composite functor sending a cochain complex `K` in `C` to the image of `F(K)`
in the derived category of `D`. Its right derived functor is the source of hypercohomology. -/
def toDerivedOfD : CochainComplex C ℤ ⥤ DerivedCategory D :=
  F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q





end TotalDerived

section Compatibility

variable (F : C ⥤ D) [F.Additive]


end Compatibility

section SpectralSequence

variable (F : C ⥤ D) [F.Additive]




end SpectralSequence

end Hypercohomology

end
