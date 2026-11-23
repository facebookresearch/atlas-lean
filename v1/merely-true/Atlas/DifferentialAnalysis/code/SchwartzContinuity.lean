/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution

noncomputable section

open scoped SchwartzMap
open SchwartzMap

namespace TemperedDistributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A linear map between Schwartz spaces is continuous if it is bounded with respect to
the canonical Schwartz seminorm family. One direction of Melrose's Lemma 7.4. -/
theorem continuous_of_isBounded_schwartz
    (T : 𝓢(E, G) →ₗ[ℝ] 𝓢(E, G))
    (hbound : Seminorm.IsBounded (schwartzSeminormFamily ℝ E G)
      (schwartzSeminormFamily ℝ E G) T) :
    Continuous T :=
  WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms ℝ E G)
    (schwartz_withSeminorms ℝ E G) T hbound

/-- A continuous linear map between Schwartz spaces is bounded with respect to the
canonical Schwartz seminorm family. Reverse direction of Melrose's Lemma 7.4. -/
theorem isBounded_schwartz_of_continuous
    (T : 𝓢(E, G) →L[ℝ] 𝓢(E, G)) :
    Seminorm.IsBounded (schwartzSeminormFamily ℝ E G)
      (schwartzSeminormFamily ℝ E G) T.toLinearMap := by
  intro i
  have hcont : Continuous ((schwartzSeminormFamily ℝ E G i).comp T.toLinearMap) := by
    show Continuous (fun x => schwartzSeminormFamily ℝ E G i (T x))
    exact ((schwartz_withSeminorms ℝ E G).continuous_seminorm i).comp T.continuous
  obtain ⟨s, C, _, hle⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ E G)
      ((schwartzSeminormFamily ℝ E G i).comp T.toLinearMap) hcont
  exact ⟨s, C, hle⟩

/-- Melrose's Lemma 7.4: a linear map between Schwartz spaces is continuous iff it is
bounded with respect to the canonical Schwartz seminorm family. -/
theorem continuous_linearMap_schwartz_iff
    (T : 𝓢(E, G) →ₗ[ℝ] 𝓢(E, G)) :
    Continuous T ↔
      Seminorm.IsBounded (schwartzSeminormFamily ℝ E G)
        (schwartzSeminormFamily ℝ E G) T := by
  constructor
  · intro hcont
    exact isBounded_schwartz_of_continuous ⟨T, hcont⟩
  · exact continuous_of_isBounded_schwartz T

end TemperedDistributions

end
