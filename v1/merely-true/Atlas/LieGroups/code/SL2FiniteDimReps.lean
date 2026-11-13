/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SL2Basics
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

open Polynomial

section ScalarSemisimple

theorem semisimple_sub_smul_id {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] V) (c : K) (hf : Module.End.IsSemisimple f) :
    Module.End.IsSemisimple (f - c • LinearMap.id) := by
  rw [show c • (LinearMap.id : V →ₗ[K] V) = algebraMap K _ c from by
    simp [Algebra.algebraMap_eq_smul_one]; rfl]
  exact Module.End.isSemisimple_sub_algebraMap_iff.mpr hf

end ScalarSemisimple

section CasimirSemisimple

end CasimirSemisimple
