/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Spectrum.Prime.Topology

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ProjectiveComplete

/-- **Proposition 12 (Lecture 8): Projective space is complete.** For a graded ring
`A = ⨁_n 𝒜_n` that is of finite type over its degree-zero piece `𝒜 0`, the structure
morphism `Proj 𝒜 → Spec(𝒜 0)` is proper. In particular `ℙ^n_k → Spec k` is proper, so
projective space over a field is complete. -/
theorem proj_isProper {σ A : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    [Algebra.FiniteType (𝒜 0) A] :
    IsProper (Proj.toSpecZero 𝒜) := inferInstance

end ProjectiveComplete
