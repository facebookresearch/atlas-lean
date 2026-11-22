/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.GlobalCFT

noncomputable section

open NumberField RayClassField

namespace GlobalCFT

universe u

variable (K : Type u) [Field K] [NumberField K]

structure CongruenceSubgroup (𝔪 : Modulus K) where
  toSubgroup : Subgroup (FracIdealsCoprime K 𝔪)
  ray_le : RayGroup K 𝔪 ≤ toSubgroup

variable {K}

def CongruenceSubgroup.mk' {𝔪 : Modulus K}
    (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h : IsCongruenceSubgroup K 𝔪 𝒞) :
    CongruenceSubgroup K 𝔪 :=
  ⟨𝒞, h.contains_ray⟩

instance {𝔪 : Modulus K} : CoeOut (CongruenceSubgroup K 𝔪)
    (Subgroup (FracIdealsCoprime K 𝔪)) :=
  ⟨CongruenceSubgroup.toSubgroup⟩

@[ext]
theorem CongruenceSubgroup.ext {𝔪 : Modulus K}
    {𝒞₁ 𝒞₂ : CongruenceSubgroup K 𝔪}
    (h : 𝒞₁.toSubgroup = 𝒞₂.toSubgroup) : 𝒞₁ = 𝒞₂ := by
  cases 𝒞₁; cases 𝒞₂; simp only [mk.injEq]; exact h

def CongruenceSubgroup.ray (𝔪 : Modulus K) : CongruenceSubgroup K 𝔪 :=
  ⟨RayGroup K 𝔪, le_refl _⟩

def CongruenceSubgroup.top (𝔪 : Modulus K) : CongruenceSubgroup K 𝔪 :=
  ⟨⊤, le_top⟩

def CongruenceSubgroup.index {𝔪 : Modulus K} (𝒞 : CongruenceSubgroup K 𝔪) : ℕ :=
  𝒞.toSubgroup.index

end GlobalCFT

end
