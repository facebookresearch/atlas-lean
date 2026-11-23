/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import Atlas.NumberTheoryI.code.GeometryOfNumbers

open NumberField

namespace ClassGroupFinite

noncomputable def minkowskiConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
  ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K) ^ Module.finrank ℚ K *
   √|↑(discr K)|)

theorem idealClass_exists_integral_absNorm_le_minkowskiConstant
    (K : Type*) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) :
    ∃ I : ↥(nonZeroDivisors (Ideal (𝓞 K))),
      ClassGroup.mk0 I = C ∧
      ↑(Ideal.absNorm (I : Ideal (𝓞 K))) ≤ minkowskiConstant K :=
  NumberField.exists_ideal_in_class_of_norm_le C

theorem ideals_bounded_absNorm_card_le (K : Type*) [Field K] [NumberField K] (M : ℕ) :
    Nat.card {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} ≤
      (Module.finrank ℚ K * M) ^ Nat.log 2 M :=
  GeometryOfNumbers.ideals_bounded_norm_card_le K M

theorem classGroup_finite (K : Type*) [Field K] [NumberField K] :
    Finite (ClassGroup (𝓞 K)) :=
  inferInstance

end ClassGroupFinite
