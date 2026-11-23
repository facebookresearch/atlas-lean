/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open AlgebraicGeometry CategoryTheory TopologicalSpace Order Set

/-- A smooth projective curve: an integral nonempty scheme of topological Krull dimension $1$ such that every morphism out of it is universally closed (encoding properness/completeness). -/
class SmoothProjectiveCurve (C : Scheme) : Prop where
  isIntegral : AlgebraicGeometry.IsIntegral C
  krullDim_eq : topologicalKrullDim C = 1
  nonempty : Nonempty C
  morphism_universallyClosed : ∀ {Y : Scheme} (f : C ⟶ Y), UniversallyClosed f


attribute [instance] SmoothProjectiveCurve.isIntegral SmoothProjectiveCurve.nonempty

/-- The underlying continuous map of a morphism out of a smooth projective curve is closed. -/
lemma SmoothProjectiveCurve.morphism_isClosedMap
    {C : Scheme} [SmoothProjectiveCurve C] {Y : Scheme} (f : C ⟶ Y) :
    IsClosedMap f.base := by
  haveI := morphism_universallyClosed f
  exact Scheme.Hom.isClosedMap f


/-- A morphism of schemes is constant if its underlying map factors through a single point of the target. -/
def IsConstantMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∃ y : Y, ∀ x : X, f.base x = y



/-- In an irreducible T0 space of Krull dimension at most $1$, any irreducible closed subset that is not a singleton must be the whole space. -/
lemma irreducible_closed_eq_univ_of_not_subsingleton
    {Y : Type*} [TopologicalSpace Y] [T0Space Y] [IrreducibleSpace Y]
    (hdim : topologicalKrullDim Y ≤ 1)
    {S : Set Y} (hS_irred : IsIrreducible S) (hS_closed : IsClosed S)
    (hS_not_sub : ¬ S.Subsingleton) : S = Set.univ := by
  by_contra hS_ne_univ
  rw [Set.not_subsingleton_iff] at hS_not_sub
  obtain ⟨x, hx, y, hy, hne⟩ := hS_not_sub


  suffices ∃ z, z ∈ S ∧ closure ({z} : Set Y) ⊂ S by
    obtain ⟨z, _, hcz_ssubset_S⟩ := this
    let a : IrreducibleCloseds Y :=
      ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    let b : IrreducibleCloseds Y := ⟨S, hS_irred, hS_closed⟩
    let c : IrreducibleCloseds Y :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩

    have hab : a < b := hcz_ssubset_S
    have hbc : b < c := ⟨subset_univ _, fun h' => hS_ne_univ (eq_univ_of_univ_subset h')⟩

    let s : LTSeries (IrreducibleCloseds Y) :=
      ⟨2, ![a, b, c], fun i => by fin_cases i <;> simpa⟩
    exact absurd (le_trans s.length_le_krullDim hdim) (by norm_num)


  by_contra hall
  simp only [not_exists, not_and] at hall
  have hcl_eq : ∀ z ∈ S, closure ({z} : Set Y) = S := by
    intro z hz
    have hle : closure ({z} : Set Y) ⊆ S :=
      closure_minimal (singleton_subset_iff.mpr hz) hS_closed
    exact le_antisymm hle (by
      by_contra h
      exact hall z hz ⟨hle, h⟩)
  exact hne (Inseparable.eq ((inseparable_iff_closure_eq).mpr
    ((hcl_eq x hx).trans (hcl_eq y hy).symm)))

/-- A morphism between smooth projective curves is either constant or surjective. -/
theorem SmoothProjectiveCurve.morphism_constant_or_surjective
    {C₁ C₂ : Scheme} [SmoothProjectiveCurve C₁] [SmoothProjectiveCurve C₂]
    (φ : C₁ ⟶ C₂) :
    IsConstantMorphism φ ∨ Function.Surjective φ.base := by
  by_cases h : (range φ.base).Subsingleton
  ·
    left
    obtain ⟨x₀⟩ := SmoothProjectiveCurve.nonempty (C := C₁)
    exact ⟨φ.base x₀, fun x => h ⟨x, rfl⟩ ⟨x₀, rfl⟩⟩
  ·
    right

    have hclosed_range : IsClosed (range φ.base) := by
      rw [← image_univ]
      exact SmoothProjectiveCurve.morphism_isClosedMap φ _ isClosed_univ

    have hirred_range : IsIrreducible (range φ.base) := by
      rw [← image_univ]
      exact (IrreducibleSpace.isIrreducible_univ C₁).image φ.base
        (Scheme.Hom.continuous φ).continuousOn

    have hdim : topologicalKrullDim C₂ ≤ 1 := le_of_eq krullDim_eq
    have hrange_eq : range φ.base = Set.univ :=
      irreducible_closed_eq_univ_of_not_subsingleton hdim hirred_range hclosed_range h
    exact fun y => by rw [← mem_range]; simp [hrange_eq]

/-- A rational map between smooth projective curves (or rather, its unique extending morphism) is either constant or surjective. -/
theorem SmoothProjectiveCurve.rationalMap_constant_or_surjective
    {C₁ C₂ : Scheme} [SmoothProjectiveCurve C₁] [SmoothProjectiveCurve C₂]
    (φ : C₁ ⤏ C₂) (f : C₁ ⟶ C₂) (_hf : f.toRationalMap = φ) :
    IsConstantMorphism f ∨ Function.Surjective f.base :=
  morphism_constant_or_surjective f


