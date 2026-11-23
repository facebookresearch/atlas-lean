/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.LocalExtensions
import Atlas.NumberTheoryI.code.RamificationTypes
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers

noncomputable section

open scoped Padic

namespace CyclotomicDVR

variable (p : ℕ) [hp : Fact (Nat.Prime p)]
variable (L : Type*) [Field L] [Algebra ℚ_[p] L]

instance instAlgebra : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

instance instIsScalarTower : IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

section CyclotomicExtension

variable [IsCyclotomicExtension {p} ℚ_[p] L]

instance instFiniteDimensional : FiniteDimensional ℚ_[p] L :=
  IsCyclotomicExtension.finiteDimensional {p} ℚ_[p] L






end CyclotomicExtension

end CyclotomicDVR

end
