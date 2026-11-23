/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- A morphism of schemes is an *isomorphism* (Lecture 3) if it has a two-sided inverse. -/
def IsIsomorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y

/-- Our definition of `IsIsomorphism` agrees with the categorical predicate `IsIso`. -/
theorem isIsomorphism_iff_isIso {X Y : Scheme} (f : X ⟶ Y) :
    IsIsomorphism f ↔ IsIso f := by
  constructor
  · rintro ⟨g, hfg, hgf⟩
    exact ⟨⟨g, hfg, hgf⟩⟩
  · intro h
    exact ⟨inv f, IsIso.hom_inv_id f, IsIso.inv_hom_id f⟩

/-- The two-sided inverse of an isomorphism of schemes is unique. -/
theorem IsIsomorphism.inverse_unique {X Y : Scheme} {f : X ⟶ Y}
    (_hf : IsIsomorphism f) {g₁ g₂ : Y ⟶ X}
    (hg₁ : f ≫ g₁ = 𝟙 X ∧ g₁ ≫ f = 𝟙 Y)
    (hg₂ : f ≫ g₂ = 𝟙 X ∧ g₂ ≫ f = 𝟙 Y) :
    g₁ = g₂ := by
  calc g₁ = 𝟙 Y ≫ g₁ := by simp
    _ = (g₂ ≫ f) ≫ g₁ := by rw [hg₂.2]
    _ = g₂ ≫ (f ≫ g₁) := by rw [Category.assoc]
    _ = g₂ ≫ 𝟙 X := by rw [hg₁.1]
    _ = g₂ := by simp

/-- The identity morphism of a scheme is an isomorphism. -/
theorem isIsomorphism_id (X : Scheme) : IsIsomorphism (𝟙 X) :=
  ⟨𝟙 X, Category.comp_id _, Category.comp_id _⟩

/-- The composition of two isomorphisms of schemes is again an isomorphism. -/
theorem IsIsomorphism.comp {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsIsomorphism f) (hg : IsIsomorphism g) :
    IsIsomorphism (f ≫ g) := by
  obtain ⟨f', hff', hf'f⟩ := hf
  obtain ⟨g', hgg', hg'g⟩ := hg
  refine ⟨g' ≫ f', ?_, ?_⟩
  · calc (f ≫ g) ≫ (g' ≫ f')
        = f ≫ (g ≫ g') ≫ f' := by simp [Category.assoc]
      _ = f ≫ 𝟙 Y ≫ f' := by rw [hgg']
      _ = f ≫ f' := by simp
      _ = 𝟙 X := hff'
  · calc (g' ≫ f') ≫ (f ≫ g)
        = g' ≫ (f' ≫ f) ≫ g := by simp [Category.assoc]
      _ = g' ≫ 𝟙 Y ≫ g := by rw [hf'f]
      _ = g' ≫ g := by simp
      _ = 𝟙 Z := hg'g

/-- The inverse of an isomorphism is itself an isomorphism. -/
theorem IsIsomorphism.inverse {X Y : Scheme} {f : X ⟶ Y}
    (hf : IsIsomorphism f) : ∃ g : Y ⟶ X, IsIsomorphism g := by
  obtain ⟨g, hfg, hgf⟩ := hf
  exact ⟨g, f, hgf, hfg⟩

end AlgebraicGeometry
