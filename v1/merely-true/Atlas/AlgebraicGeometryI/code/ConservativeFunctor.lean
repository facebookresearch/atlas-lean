/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Definition 27 (Lec 13): a functor is *conservative* if it reflects isomorphisms. -/
abbrev Functor.IsConservative (F : C ⥤ D) : Prop := F.ReflectsIsomorphisms

/-- A fully faithful left adjoint with a conservative right adjoint gives an equivalence of
categories. -/
noncomputable def adjunction_equivalence_of_fullyFaithful_conservative
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Full] [L.Faithful]
    [R.ReflectsIsomorphisms] : C ≌ D := by


  have : ∀ Y, IsIso (adj.counit.app Y) :=
    fun Y => isIso_of_reflects_iso (adj.counit.app Y) R

  exact adj.toEquivalence

/-- A single conservative functor (indexed by a singleton) jointly reflects isomorphisms. -/
lemma jointlyReflectIsomorphisms_of_conservative
    (R : C ⥤ D) [R.ReflectsIsomorphisms] :
    JointlyReflectIsomorphisms (fun (_ : PUnit.{1}) => R) where
  isIso f h := by
    haveI := h PUnit.unit
    exact isIso_of_reflects_iso f R

/-- A conservative exact functor between abelian categories reflects exactness of short
complexes: `S.Exact ↔ (S.map R).Exact`. -/
theorem conservative_exact_functor_reflects_exact_iff
    [Abelian C] [Abelian D]
    (R : C ⥤ D) [R.PreservesZeroMorphisms] [R.PreservesHomology] [R.ReflectsIsomorphisms]
    (S : ShortComplex C) :
    S.Exact ↔ (S.map R).Exact := by
  have hJ := jointlyReflectIsomorphisms_of_conservative R
  rw [hJ.exact_iff (I := PUnit.{1}) S]
  exact ⟨fun h => h PUnit.unit, fun h _ => h⟩
