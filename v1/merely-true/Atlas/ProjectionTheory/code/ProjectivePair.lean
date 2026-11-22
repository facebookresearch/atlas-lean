/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace ProjectivePair

variable {P : Type*} {T : Type*} {D : Type*}

/-- The set of tubes from a collection `𝕋` that pass through a given point `x`,
where membership is given by an abstract relation `mem : P → T → Prop`. -/
def tubesThrough (mem : P → T → Prop) (𝕋 : Set T) (x : P) : Set T :=
  {t ∈ 𝕋 | mem x t}

/-- The set of directions of a family of tubes `S ⊆ T`, where each tube `t : T`
has a direction `dir t : D`. -/
def tubeDirections (dir : T → D) (S : Set T) : Set D :=
  dir '' S

/-- A pair `(E, 𝕋)` of points and tubes is *projective* if the set of directions
of tubes through `x₁` and through `x₂` agree, for all `x₁, x₂ ∈ E`. Equivalently,
every point of `E` "sees" the same directions of tubes from `𝕋`. -/
def IsProjective (mem : P → T → Prop) (dir : T → D) (E : Set P) (𝕋 : Set T) : Prop :=
  ∀ x₁ ∈ E, ∀ x₂ ∈ E,
    tubeDirections dir (tubesThrough mem 𝕋 x₁) = tubeDirections dir (tubesThrough mem 𝕋 x₂)

end ProjectivePair
