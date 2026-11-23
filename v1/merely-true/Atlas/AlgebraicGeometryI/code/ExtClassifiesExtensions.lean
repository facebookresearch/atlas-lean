/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.Exact

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.ShortComplex

universe w v u

namespace ExtClassifiesExtensions

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

section SplittingCriterion

/-- Splitting criterion: a short exact sequence `0 → X₁ → X₂ → X₃ → 0` splits
when `Ext¹(X₃, X₁) = 0`, recovering the classification of extensions by `Ext¹`. -/
noncomputable def splitting_of_ext1_zero
    {S : ShortComplex C} (hS : S.ShortExact)
    (hExt : ∀ (e : Ext.{w} S.X₃ S.X₁ 1), e = 0) :
    S.Splitting := by


  have hex := Ext.covariant_sequence_exact₃ S.X₃ hS
    (Ext.mk₀ (𝟙 S.X₃)) (zero_add 1) (by simp [hExt])


  let x₂ := hex.choose
  have hx₂ := hex.choose_spec


  let s := Ext.addEquiv₀ x₂

  have hs : s ≫ S.g = 𝟙 S.X₃ := by
    have hx₂' : Ext.mk₀ s = x₂ := by simp [s, Ext.addEquiv₀]
    have : Ext.mk₀ (s ≫ S.g) = Ext.mk₀ (𝟙 S.X₃) := by
      rw [← Ext.mk₀_comp_mk₀ s S.g, hx₂', hx₂]
    exact (Ext.mk₀_bijective S.X₃ S.X₃).injective this

  exact Splitting.ofExactOfSection S hS.exact s hs hS.mono_f

end SplittingCriterion

section GBApplication

end GBApplication

section ProjectiveVanishing

end ProjectiveVanishing

/-- The covariant connecting homomorphism `Ext^{n₀}(X, X₃) → Ext^{n₁}(X, X₁)`
associated to a short exact sequence, given by post-composition with the
extension class. -/
noncomputable def covariantConnecting
    {S : ShortComplex C} (hS : S.ShortExact)
    (X : C) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    Ext.{w} X S.X₃ n₀ →+ Ext.{w} X S.X₁ n₁ :=
  hS.extClass.postcomp X h

end ExtClassifiesExtensions
