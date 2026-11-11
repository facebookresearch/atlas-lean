/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.AffineScheme

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

namespace ChowHelperBlowupProjective

/-- Two schemes are birational when they share a common dense open `Z`, i.e. there exist open
immersions `f : Z ↪ X` and `g : Z ↪ Y` with dense images. -/
def IsBirational (X Y : Scheme.{u}) : Prop :=
  ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧
    Dense (Set.range f.base) ∧ Dense (Set.range g.base)

/-- A scheme is projective if it admits a closed immersion into some `Proj 𝒜` for a
finitely-generated graded `(𝒜 0)`-algebra. -/
def IsProjectiveScheme (X : Scheme.{u}) : Prop :=
  ∃ (σ : Type u) (A : Type u)
    (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A)
    (𝒜 : ℕ → σ) (_ : GradedRing 𝒜) (_ : Algebra.FiniteType (𝒜 0) A)
    (i : X ⟶ Proj 𝒜), IsClosedImmersion i




/-- Birationality is reflexive: every scheme is birational to itself via the identity. -/
theorem isBirational_refl (X : Scheme.{u}) : IsBirational X X :=
  ⟨X, 𝟙 X, 𝟙 X, inferInstance, inferInstance,
   by have h : Function.Surjective (𝟙 X : X ⟶ X).base := fun x => ⟨x, rfl⟩
      rw [Set.range_eq_univ.mpr h]; exact dense_univ,
   by have h : Function.Surjective (𝟙 X : X ⟶ X).base := fun x => ⟨x, rfl⟩
      rw [Set.range_eq_univ.mpr h]; exact dense_univ⟩

/-- Birationality is symmetric: swap the roles of `X` and `Y` in the witnessing common open. -/
theorem isBirational_symm {X Y : Scheme.{u}} (h : IsBirational X Y) :
    IsBirational Y X := by
  obtain ⟨Z, f, g, hf, hg, hdf, hdg⟩ := h
  exact ⟨Z, g, f, hg, hf, hdg, hdf⟩

end ChowHelperBlowupProjective
