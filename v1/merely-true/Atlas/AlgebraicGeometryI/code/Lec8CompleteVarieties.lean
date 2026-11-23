/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ValuativeCriterion

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Formalization.Lec8CompleteVarieties


/-- A morphism `f : X ⟶ Y` is complete if it is separated and
universally closed (Lec 8, Def 19). -/
class IsComplete {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  isSeparated : IsSeparated f
  universallyClosed : UniversallyClosed f


/-- A proper morphism is complete. -/
instance isComplete_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    IsComplete f where
  isSeparated := inferInstance
  universallyClosed := inferInstance


/-- Lec 8, Lem 19(ii): if `X` is proper over `S` and `Z` is separated
over `S`, then the image of `f : X ⟶ Z` is a closed subscheme and
`X ↠ im(f)` is proper. -/
theorem lemma19_ii_image_complete
    {X Z S : Scheme.{u}} (f : X ⟶ Z) (hX : X ⟶ S) (hZ : Z ⟶ S)
    [hXp : IsProper hX] [IsSeparated hZ] (hcomm : f ≫ hZ = hX) :
    IsClosedImmersion f.imageι ∧ IsProper f.toImage := by
  have hfhZ_proper : IsProper (f ≫ hZ) := hcomm ▸ hXp
  have hf_proper : IsProper f := @IsProper.of_comp _ _ _ f hZ hfhZ_proper _
  have hfi : IsProper (f.toImage ≫ f.imageι) := by
    rw [f.toImage_imageι]
    exact hf_proper
  exact ⟨inferInstance, @IsProper.of_comp _ _ _ f.toImage f.imageι hfi inferInstance⟩

/-- Two schemes are birational if they share a common dense open
subscheme (Lec 9 / Chow's lemma setting). -/
def IsBirational (X Y : Scheme.{u}) : Prop :=
  ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧
    Dense (Set.range f.base) ∧ Dense (Set.range g.base)

/-- A scheme `X` is projective if it admits a closed immersion into
some `Proj 𝒜` for a graded ring `𝒜` with finite-type degree-zero
piece (Lec 8/9, used for Chow's lemma). -/
def IsProjective (X : Scheme.{u}) : Prop :=
  ∃ (σ : Type u) (A : Type u)
    (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A)
    (𝒜 : ℕ → σ) (_ : GradedRing 𝒜) (_ : Algebra.FiniteType (𝒜 0) A)
    (i : X ⟶ Proj 𝒜), IsClosedImmersion i








end Formalization.Lec8CompleteVarieties
