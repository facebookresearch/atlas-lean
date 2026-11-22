/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.RationalMap
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Tactic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

namespace Lec7

/-- Lec 7, Lem 17 / Cor 12: an open subscheme of a separated scheme is
separated. -/
theorem separated_of_open_immersion_to_separated {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] [Y.IsSeparated] : X.IsSeparated := by
  constructor
  have : IsSeparated f := inferInstance
  have : IsSeparated (terminal.from Y) := Scheme.IsSeparated.isSeparated_terminal_from
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _]
  infer_instance

/-- Lec 7, Prop 9 (forward direction): on a separated scheme, the
intersection of two affine opens is affine. -/
theorem prop9_forward
    {X : Scheme.{u}} [X.IsSeparated]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) :=
  hU.inf hV

/-- Lec 7, Prop 9: characterization of separatedness via affine
intersections plus surjectivity of the diagonal on affine opens of the
fiber product. -/
theorem prop9_separated_iff
    {X : Scheme.{u}} :
    X.IsSeparated ↔
    (∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) ∧
    (∀ (W : (pullback (terminal.from X) (terminal.from X)).Opens),
      IsAffineOpen W →
      Function.Surjective ((pullback.diagonal (terminal.from X)).app W)) := by
  rw [Scheme.isSeparated_iff, isSeparated_iff, isClosedImmersion_iff_isAffineHom]
  constructor
  · rintro ⟨hAff, hSurj⟩
    constructor
    · rw [isAffineHom_diagonal_iff] at hAff
      intro U V hU hV
      exact hAff ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV
    · exact hSurj
  · rintro ⟨hAff, hSurj⟩
    constructor
    · rw [isAffineHom_diagonal_iff]
      intro U _ V₁ _ V₂ _ hV₁ hV₂
      exact hAff V₁ V₂ hV₁ hV₂
    · exact hSurj

/-- Lec 7, Lem 18: `Proj 𝒜` (in particular `ℙⁿ`) is separated. -/
theorem proj_is_separated {A : Type u} {σ : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    IsSeparated (Proj.toSpecZero 𝒜) :=
  Proj.isSeparated 𝒜

/-- Lec 7: a closed subscheme of a separated scheme is separated. -/
theorem separated_of_closed_immersion_to_separated {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] [Y.IsSeparated] : X.IsSeparated := by
  constructor
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _]
  infer_instance

/-- Lec 7, Lem 17: a locally closed subscheme of a separated scheme
is separated. -/
theorem separated_of_locally_closed_immersion {X Z Y : Scheme.{u}}
    (f : X ⟶ Z) (g : Z ⟶ Y)
    [IsClosedImmersion f] [IsOpenImmersion g] [Y.IsSeparated] :
    X.IsSeparated := by

  have : Z.IsSeparated := separated_of_open_immersion_to_separated g

  exact separated_of_closed_immersion_to_separated f

end Lec7
