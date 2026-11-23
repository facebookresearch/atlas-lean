/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace QuasiprojectiveSeparated

/-- An open subscheme of a separated scheme is separated. -/
theorem separated_of_openImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] [Y.IsSeparated] : X.IsSeparated := by
  constructor
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _]
  infer_instance

/-- A closed subscheme of a separated scheme is separated. -/
theorem separated_of_closedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [Y.IsSeparated] : X.IsSeparated := by
  constructor
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _]
  infer_instance

/-- A scheme admitting a locally closed immersion (closed-in-open) into a
separated scheme is itself separated. -/
theorem separated_of_locally_closed_immersion_to_separated
    {X Z Y : Scheme.{u}} (f : X ⟶ Z) (g : Z ⟶ Y)
    [IsClosedImmersion f] [IsOpenImmersion g] [Y.IsSeparated] :
    X.IsSeparated := by

  have : Z.IsSeparated := separated_of_openImmersion g

  exact separated_of_closedImmersion f

/-- Def 6 (Lec 3): `X` is quasi-projective if it admits a locally closed immersion
into some projective scheme `Proj 𝒜`. -/
class IsQuasiProjective (X : Scheme.{u}) : Prop where
  exists_locally_closed_immersion :
    ∃ (σ : Type u) (A : Type u) (_ : CommRing A) (_ : SetLike σ A)
      (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ) (_ : GradedRing 𝒜)
      (Z : Scheme.{u}) (f : X ⟶ Z) (g : Z ⟶ Proj 𝒜),
      IsClosedImmersion f ∧ IsOpenImmersion g

/-- Cor 12 (Lec 3): every quasi-projective variety is separated, obtained by
combining `Proj 𝒜` separated with the locally closed immersion of Def 6. -/
theorem quasiprojective_isSeparated (X : Scheme.{u}) [IsQuasiProjective X] :
    X.IsSeparated := by
  obtain ⟨σ, A, hCR, hSL, hASG, 𝒜, hGR, Z, f, g, hf, hg⟩ :=
    IsQuasiProjective.exists_locally_closed_immersion (X := X)

  have hProj : (Proj 𝒜).IsSeparated := inferInstance

  exact @separated_of_locally_closed_immersion_to_separated _ Z (Proj 𝒜) f g hf hg hProj

end QuasiprojectiveSeparated
