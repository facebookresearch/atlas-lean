/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.HomologySequenceLemmas

open CategoryTheory Category

theorem homology_les_exact
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    (HomologicalComplex.HomologySequence.composableArrows₅ hS i j hij).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact hS i j hij

theorem homology_les_naturality
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {S₁ S₂ : ShortComplex (HomologicalComplex C c)}
    (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    hS₁.δ i j hij ≫ HomologicalComplex.homologyMap φ.τ₁ j =
      HomologicalComplex.homologyMap φ.τ₃ i ≫ hS₂.δ i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality φ hS₁ hS₂ i j hij

theorem homology_les
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {S₁ S₂ : ShortComplex (HomologicalComplex C c)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (φ : S₁ ⟶ S₂)
    (i j : ι) (hij : c.Rel i j) :

    (HomologicalComplex.HomologySequence.composableArrows₅ hS₁ i j hij).Exact

    ∧ (hS₁.δ i j hij ≫ HomologicalComplex.homologyMap φ.τ₁ j =
        HomologicalComplex.homologyMap φ.τ₃ i ≫ hS₂.δ i j hij) :=
  ⟨homology_les_exact hS₁ i j hij,
   homology_les_naturality φ hS₁ hS₂ i j hij⟩
