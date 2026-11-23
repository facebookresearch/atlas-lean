/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.NumberField.Basic

open Ideal

section IdealNorm

variable {O : Type*} [CommRing O] [Nontrivial O] [IsDedekindDomain O] [Module.Free ℤ O]

noncomputable abbrev idealNorm : Ideal O →*₀ ℕ := Ideal.absNorm


end IdealNorm

section Theorem75

variable {O : Type*} [CommRing O] [Nontrivial O] [IsDedekindDomain O]
    [Module.Free ℤ O] [Module.Finite ℤ O]


end Theorem75

section Theorem75NumberField

open NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem idealNorm_span_singleton_numberField (α : RingOfIntegers K) :
    idealNorm (Ideal.span {α}) = Int.natAbs (Algebra.norm ℤ α) :=
  Ideal.absNorm_span_singleton α

end Theorem75NumberField
