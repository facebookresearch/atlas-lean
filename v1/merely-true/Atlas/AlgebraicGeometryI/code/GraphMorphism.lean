/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Graph morphism `Γ_f : X → X × Y` of `f : X → Y`, given by `(𝟙 X, f)`
(Def 18, Lec 7 in the absolute case). -/
noncomputable abbrev graphMor : X ⟶ X ⨯ Y :=
  prod.lift (𝟙 X) f

/-- First projection of the graph morphism is the identity on `X`. -/
@[simp]
theorem graphMor_comp_fst : graphMor f ≫ prod.fst = 𝟙 X := by
  simp [graphMor, prod.lift_fst]

/-- Second projection of the graph morphism is `f`. -/
@[simp]
theorem graphMor_comp_snd : graphMor f ≫ prod.snd = f := by
  simp [graphMor, prod.lift_snd]

/-- The graph of the identity is the diagonal `Δ_X = (𝟙, 𝟙)`. -/
theorem graphMor_of_id : graphMor (𝟙 X) = prod.lift (𝟙 X) (𝟙 X) :=
  rfl

/-- The graph morphism is a split monomorphism, with `prod.fst` as retraction. -/
noncomputable instance graphMor_splitMono :
    SplitMono (graphMor f) where
  retraction := prod.fst
  id := by simp [graphMor, prod.lift_fst]

/-- The graph morphism fits into a pullback square exhibiting `Γ_f` as the pullback of the
diagonal `Δ_Y` along `f × 𝟙_Y : X × Y → Y × Y`. -/
theorem isPullback_graphMor :
    IsPullback f (graphMor f) (prod.lift (𝟙 Y) (𝟙 Y)) (prod.map f (𝟙 Y)) := by
  refine ⟨⟨by ext <;> simp⟩,
    ⟨PullbackCone.IsLimit.mk _ (fun s => s.snd ≫ prod.fst) ?_ ?_ ?_⟩⟩
  ·
    intro s
    have h1 := congr_arg (· ≫ prod.fst) s.condition
    simp [Category.assoc, prod.lift_fst, prod.map_fst] at h1
    exact h1.symm
  ·
    intro s
    have h1 := congr_arg (· ≫ prod.fst) s.condition
    simp [Category.assoc, prod.lift_fst, prod.map_fst] at h1
    have h2 := congr_arg (· ≫ prod.snd) s.condition
    simp [Category.assoc, prod.lift_snd, prod.map_snd] at h2
    apply prod.hom_ext
    · simp [prod.lift_fst]
    · simp [prod.lift_snd, Category.assoc]; rw [← h1, h2]
  ·
    intro s m hfst hsnd
    have := congr_arg (· ≫ prod.fst) hsnd
    simp [prod.lift_fst] at this
    exact this

/-- The graph morphism is always an immersion. -/
instance isImmersion_graphMor : IsImmersion (graphMor f) :=
  MorphismProperty.of_isPullback (isPullback_graphMor f) inferInstance

/-- If `Y` is separated, the graph morphism is a closed immersion. -/
instance isClosedImmersion_graphMor [Y.IsSeparated] :
    IsClosedImmersion (graphMor f) :=
  MorphismProperty.of_isPullback (isPullback_graphMor f) inferInstance

end AlgebraicGeometry.Scheme
