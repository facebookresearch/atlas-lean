/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Basic

open NumberField

theorem number_field_and_ring_of_integers (K : Type*) [Field K] [NumberField K] :
    FiniteDimensional ℚ K ∧ (𝓞 K = ↥(integralClosure ℤ K)) :=
  ⟨inferInstance, rfl⟩
