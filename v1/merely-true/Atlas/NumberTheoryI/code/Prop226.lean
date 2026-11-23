/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Lem225

noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

lemma Modulus.gcd_dvd_left (𝔪₁ 𝔪₂ : Modulus K) : (𝔪₁.gcd 𝔪₂).dvd 𝔪₁ :=
  fun _ => min_le_left _ _

lemma Modulus.gcd_dvd_right (𝔪₁ 𝔪₂ : Modulus K) : (𝔪₁.gcd 𝔪₂).dvd 𝔪₂ :=
  fun _ => min_le_right _ _

lemma Modulus.dvd_lcm_left (𝔪₁ 𝔪₂ : Modulus K) : 𝔪₁.dvd (𝔪₁.lcm 𝔪₂) :=
  fun _ => le_max_left _ _

lemma Modulus.dvd_lcm_right (𝔪₁ 𝔪₂ : Modulus K) : 𝔪₂.dvd (𝔪₁.lcm 𝔪₂) :=
  fun _ => le_max_right _ _















end RayClassField
