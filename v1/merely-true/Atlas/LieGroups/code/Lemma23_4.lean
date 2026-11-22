/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.GrothendieckGroupO

noncomputable section

universe u

variable {R : Type u} [CommRing R]
         {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

def IsDominantCorootNonneg {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) [LinearOrder R] [IsStrictOrderedRing R]
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ α ∈ rd.posRoots, (0 : R) ≤ rd.corootPairing lam α

variable {Δ : TriangularDecomposition R 𝔤}
variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)


theorem form_posRoot_pos_of_WeightBilinForm [LinearOrder R] [IsStrictOrderedRing R]
    (B : WeightBilinForm wg) (alpha : Δ.𝔥 →ₗ[R] R) (halpha_pos : alpha ∈ rd.posRoots) :
    (0 : R) < B.form alpha alpha :=
  B.form_posRoot_pos rd alpha halpha_pos





end
