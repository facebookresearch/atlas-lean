/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Ch22WeberLFunction
import Atlas.NumberTheoryI.code.Cor227
noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

def RayClassChar.kernelSubgroup {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) :
    Subgroup (FracIdealsCoprime K 𝔪) :=
  (MonoidHom.ker χ).comap (toRayClass K 𝔪)

theorem RayClassChar.rayGroup_le_kernelSubgroup {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) :
    RayGroup K 𝔪 ≤ χ.kernelSubgroup := by
  intro x hx
  show toRayClass K 𝔪 x ∈ MonoidHom.ker χ
  rw [MonoidHom.mem_ker]
  have : toRayClass K 𝔪 x = 1 := by
    show (QuotientGroup.mk' (RayGroup K 𝔪)) x = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  rw [this, map_one]

def RayClassChar.kernelCongruenceSubgroup {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) :
    CongruenceSubgroupPair K where
  modulus := 𝔪
  subgroup := χ.kernelSubgroup
  ray_le := χ.rayGroup_le_kernelSubgroup

end RayClassField
