/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Abelian

open CategoryTheory

universe v u

theorem proposition_23_57
    {C : Type u} [Category.{v} C] [Abelian C]
    {M N : C} (f : M ⟶ N)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (∃ α : P.complex ⟶ Q.complex,
      α ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) ∧
    (∀ (g h : P.complex ⟶ Q.complex),
      g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f →
      h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f →
      Nonempty (Homotopy g h)) :=
  ⟨⟨ProjectiveResolution.lift f P Q, ProjectiveResolution.lift_commutes f P Q⟩,
    fun g h hg hh => ⟨ProjectiveResolution.liftHomotopy f g h hg hh⟩⟩

theorem proposition_23_57_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    {M N : C} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    (∃ α : I.cocomplex ⟶ J.cocomplex,
      I.ι ≫ α = (CochainComplex.single₀ C).map f ≫ J.ι) ∧
    (∀ (g h : I.cocomplex ⟶ J.cocomplex),
      I.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι →
      I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι →
      Nonempty (Homotopy g h)) :=
  ⟨⟨InjectiveResolution.desc f J I, InjectiveResolution.desc_commutes f J I⟩,
    fun g h hg hh => ⟨InjectiveResolution.descHomotopy f g h hg hh⟩⟩

theorem resolution_comparison_unique_up_to_homotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    {M N : C} (f : M ⟶ N)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    ((∃ α : P.complex ⟶ Q.complex,
        α ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) ∧
     (∀ (g h : P.complex ⟶ Q.complex),
        g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f →
        h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f →
        Nonempty (Homotopy g h))) ∧
    ((∃ α : I.cocomplex ⟶ J.cocomplex,
        I.ι ≫ α = (CochainComplex.single₀ C).map f ≫ J.ι) ∧
     (∀ (g h : I.cocomplex ⟶ J.cocomplex),
        I.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι →
        I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι →
        Nonempty (Homotopy g h))) :=
  ⟨proposition_23_57 f P Q, proposition_23_57_injective f I J⟩
