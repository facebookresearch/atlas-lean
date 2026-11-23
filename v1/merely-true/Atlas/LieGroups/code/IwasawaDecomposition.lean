/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

structure CartanDecomposition
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] where
  𝔨 : LieSubalgebra ℝ 𝔤
  𝔭 : Submodule ℝ 𝔤
  isCompl : IsCompl (𝔨 : Submodule ℝ 𝔤) 𝔭
  bracket_𝔨_𝔭 : ∀ (x y : 𝔤), x ∈ 𝔨 → y ∈ 𝔭 → ⁅x, y⁆ ∈ 𝔭
  bracket_𝔭_𝔭 : ∀ (x y : 𝔤), x ∈ 𝔭 → y ∈ 𝔭 → ⁅x, y⁆ ∈ (𝔨 : Submodule ℝ 𝔤)

structure IwasawaData
    (G : Type*) [Group G] [TopologicalSpace G] where
  K : Subgroup G
  A : Subgroup G
  N : Subgroup G
  K_compact : CompactSpace K
  A_comm : ∀ (a b : A), a * b = b * a
  mul_surj : ∀ g : G, ∃ (k : K) (a : A) (n : N),
    g = (k : G) * (a : G) * (n : G)
  mul_inj : ∀ (k₁ k₂ : K) (a₁ a₂ : A) (n₁ n₂ : N),
    (k₁ : G) * (a₁ : G) * (n₁ : G) = (k₂ : G) * (a₂ : G) * (n₂ : G) →
    k₁ = k₂ ∧ a₁ = a₂ ∧ n₁ = n₂

namespace IwasawaData

variable {G : Type*} [Group G] [TopologicalSpace G]
variable (iw : IwasawaData G)

end IwasawaData


end
