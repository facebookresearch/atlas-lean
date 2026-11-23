/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Cor227
import Atlas.NumberTheoryI.code.Lem225

noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

theorem Modulus.ext_iff (𝔪 𝔫 : Modulus K) : 𝔪 = 𝔫 ↔ ∀ v, 𝔪 v = 𝔫 v := by
  constructor
  · rintro rfl; intro; rfl
  · intro h
    cases 𝔪; cases 𝔫
    congr 1
    funext v
    exact h v

theorem Modulus.dvd_antisymm (𝔪 𝔫 : Modulus K) (h₁ : 𝔪.dvd 𝔫) (h₂ : 𝔫.dvd 𝔪) :
    𝔪 = 𝔫 := by
  rw [Modulus.ext_iff]
  intro v
  exact le_antisymm (h₁ v) (h₂ v)

end RayClassField
