/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Divisors

namespace Theorem19_14

variable (C : Type*) (k : Type*) (F : Type*) [Field k] [Field F]
  [Algebra k F] [inst : CurveWithConstants C k F]

open CurveWithOrd CurveWithConstants

noncomputable def divMap : Fˣ → CurveDivisor C :=
  fun f => principalDivisor (C := C) f

noncomputable def toPicMap :
    CurveDivisor C →+ CurveDivisor C ⧸ principalDivisors (C := C) (F := F) :=
  QuotientAddGroup.mk' principalDivisors

theorem exact_at_functionField_mathlib :
    Function.Exact (constantsEmb (k := k) (F := F)) (divMap C k F) := by
  intro f
  exact CurveWithConstants.exact_at_functionField (C := C) (k := k) f

theorem exact_at_DivGroup_mathlib :
    Function.Exact (divMap C k F) (toPicMap C k F) := by
  intro D
  constructor
  · intro hD
    have hD' : D ∈ (toPicMap C k F).ker := AddMonoidHom.mem_ker.mpr hD
    rw [toPicMap, QuotientAddGroup.ker_mk'] at hD'
    obtain ⟨f, hf⟩ := hD'
    exact ⟨f, hf⟩
  · rintro ⟨f, rfl⟩
    show toPicMap C k F (principalDivisor f) = 0
    have : principalDivisor f ∈ principalDivisors (C := C) (F := F) := ⟨f, rfl⟩
    have hker : principalDivisor f ∈ (toPicMap C k F).ker := by
      rw [toPicMap, QuotientAddGroup.ker_mk']
      exact this
    exact AddMonoidHom.mem_ker.mp hker

theorem toPicMap_surjective :
    Function.Surjective (toPicMap C k F) :=
  QuotientAddGroup.mk'_surjective principalDivisors

theorem picard_exact_sequence :
    Function.Injective (constantsEmb (k := k) (F := F)) ∧
    Function.Exact (constantsEmb (k := k) (F := F)) (divMap C k F) ∧
    Function.Exact (divMap C k F) (toPicMap C k F) ∧
    Function.Surjective (toPicMap C k F) :=
  ⟨CurveWithConstants.constantsEmb_injective,
   exact_at_functionField_mathlib C k F,
   exact_at_DivGroup_mathlib C k F,
   toPicMap_surjective C k F⟩

end Theorem19_14
