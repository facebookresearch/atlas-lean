/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option maxHeartbeats 400000

open AlgebraicGeometry

/-- Lemma 18: the structure morphism `Proj 𝒜 → Spec (𝒜_0)` is separated. -/
theorem lemma18_proj_isSeparated {σ A : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    IsSeparated (Proj.toSpecZero 𝒜) :=
  Proj.isSeparated 𝒜
