/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.DerivedFunctorsDefs

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace DerivedFunctorsDefs

variable {C : Type u} [Category.{v} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

/-- A cohomological δ-functor `F` is effaceable when every object `X` admits a
mono into an `I` killed by `F^{n+1}` for every `n`. -/
def CohomDeltaFunctor.IsEffaceable (F : CohomDeltaFunctor C D) : Prop :=
  ∀ (n : ℕ) (X : C), ∃ (I : C) (i : X ⟶ I), Mono i ∧ IsZero ((F.T (n + 1)).obj I)

/-- A weaker form of effaceability: every `X` admits a mono into some `I` such
that `F^{n+1}` sends `i` to zero, without requiring `F^{n+1}(I)` itself to vanish. -/
def CohomDeltaFunctor.IsEffaceableMorphism (F : CohomDeltaFunctor C D) : Prop :=
  ∀ (n : ℕ) (X : C), ∃ (I : C) (i : X ⟶ I), Mono i ∧ (F.T (n + 1)).map i = 0

/-- Pointwise effaceability: for any test morphism into `F^{n+1}(X)`, we can find
a mono `φ : X ⟶ N` after composition with which the morphism becomes zero. -/
def CohomDeltaFunctor.IsEffaceablePointwise (F : CohomDeltaFunctor C D) : Prop :=
  ∀ (n : ℕ) (X : C) (Y : D) (m : Y ⟶ (F.T (n + 1)).obj X),
    ∃ (N : C) (φ : X ⟶ N), Mono φ ∧ m ≫ (F.T (n + 1)).map φ = 0

/-- Effaceable implies effaceable-morphism: if `F^{n+1}(I)` is zero then so is
any map into it. -/
lemma CohomDeltaFunctor.IsEffaceable.toIsEffaceableMorphism {F : CohomDeltaFunctor C D}
    (hF : F.IsEffaceable) : F.IsEffaceableMorphism := by
  intro n X
  obtain ⟨I, i, hi_mono, hI_zero⟩ := hF n X
  exact ⟨I, i, hi_mono, hI_zero.eq_of_tgt _ _⟩

/-- Effaceable-morphism implies pointwise effaceable: precompose by the test
morphism. -/
lemma CohomDeltaFunctor.IsEffaceableMorphism.toPointwise {F : CohomDeltaFunctor C D}
    (hF : F.IsEffaceableMorphism) : F.IsEffaceablePointwise := by
  intro n X Y m
  obtain ⟨N, φ, hφ_mono, hφ_map⟩ := hF n X
  exact ⟨N, φ, hφ_mono, by rw [hφ_map, comp_zero]⟩

/-- Converse: pointwise effaceability specialized to the identity recovers
effaceable-morphism. -/
lemma CohomDeltaFunctor.IsEffaceablePointwise.toMorphism {F : CohomDeltaFunctor C D}
    (hF : F.IsEffaceablePointwise) : F.IsEffaceableMorphism := by
  intro n X
  obtain ⟨N, φ, hφ_mono, hφ_eq⟩ := hF n X _ (𝟙 ((F.T (n + 1)).obj X))
  exact ⟨N, φ, hφ_mono, by rwa [Category.id_comp] at hφ_eq⟩

/-- Effaceable implies pointwise effaceable via the morphism formulation. -/
lemma CohomDeltaFunctor.IsEffaceable.toPointwise {F : CohomDeltaFunctor C D}
    (hF : F.IsEffaceable) : F.IsEffaceablePointwise :=
  hF.toIsEffaceableMorphism.toPointwise

/-- The two intermediate effaceability notions are equivalent. -/
lemma CohomDeltaFunctor.isEffaceableMorphism_iff_pointwise (F : CohomDeltaFunctor C D) :
    F.IsEffaceableMorphism ↔ F.IsEffaceablePointwise :=
  ⟨CohomDeltaFunctor.IsEffaceableMorphism.toPointwise,
   CohomDeltaFunctor.IsEffaceablePointwise.toMorphism⟩

/-- If `F^{n+1}` kills the monomorphism `S.f`, then the connecting morphism
`δ_n` is an epimorphism, by exactness of the long exact sequence. -/
lemma delta_epi_of_map_zero {F : CohomDeltaFunctor C D}
    (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact)
    (hf : (F.T (n + 1)).map S.f = 0) : Epi (F.δ n S hS) :=
  (F.exact_left n S hS).epi_f hf

/-- If `F^{n+1}` vanishes on the middle term `S.X₂`, the connecting morphism
`δ_n` is an epimorphism. -/
lemma delta_epi_of_vanishing {F : CohomDeltaFunctor C D}
    (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact)
    (hI : IsZero ((F.T (n + 1)).obj S.X₂)) : Epi (F.δ n S hS) :=
  (F.exact_left n S hS).epi_f (hI.eq_of_tgt _ _)

/-- Uniqueness for effaceable δ-functors: a morphism `F → G` of δ-functors out
of an effaceable `F` is determined by its degree-zero component. -/
theorem effaceable_morphism_unique (F G : CohomDeltaFunctor C D) (hF : F.IsEffaceable)
    (m₁ m₂ : F.Morphism G) (h₀ : m₁.η 0 = m₂.η 0) :
    ∀ n, m₁.η n = m₂.η n := by
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
    apply NatTrans.ext
    funext X

    obtain ⟨I, i, hi_mono, hI_zero⟩ := hF n X
    haveI : Mono i := hi_mono

    let S : ShortComplex C := ShortComplex.cokernelSequence i
    have hSE : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
        (show Mono i from inferInstance) (show Epi (cokernel.π i) from inferInstance)

    have hδ_epi : Epi (F.δ n S hSE) := delta_epi_of_vanishing n S hSE hI_zero

    have h1 := m₁.comm_δ n S hSE
    have h2 := m₂.comm_δ n S hSE

    rw [show (m₁.η n).app S.X₃ = (m₂.η n).app S.X₃ from congr_fun
      (congr_arg NatTrans.app ih) S.X₃] at h1

    have hrhs : F.δ n S hSE ≫ (m₁.η (n + 1)).app S.X₁ =
        F.δ n S hSE ≫ (m₂.η (n + 1)).app S.X₁ := by rw [← h1, ← h2]

    exact (cancel_epi (F.δ n S hSE)).mp hrhs

/-- Uniqueness under the weaker effaceable-morphism hypothesis: the degree-zero
component still pins down the entire morphism of δ-functors. -/
theorem effaceable_morphism_unique_of_effaceableMorphism (F G : CohomDeltaFunctor C D)
    (hF : F.IsEffaceableMorphism)
    (m₁ m₂ : F.Morphism G) (h₀ : m₁.η 0 = m₂.η 0) :
    ∀ n, m₁.η n = m₂.η n := by
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
    apply NatTrans.ext
    funext X

    obtain ⟨I, i, hi_mono, hI_map⟩ := hF n X
    haveI : Mono i := hi_mono

    let S : ShortComplex C := ShortComplex.cokernelSequence i
    have hSE : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
        (show Mono i from inferInstance) (show Epi (cokernel.π i) from inferInstance)


    have hδ_epi : Epi (F.δ n S hSE) := delta_epi_of_map_zero n S hSE hI_map

    have h1 := m₁.comm_δ n S hSE
    have h2 := m₂.comm_δ n S hSE

    rw [show (m₁.η n).app S.X₃ = (m₂.η n).app S.X₃ from congr_fun
      (congr_arg NatTrans.app ih) S.X₃] at h1

    have hrhs : F.δ n S hSE ≫ (m₁.η (n + 1)).app S.X₁ =
        F.δ n S hSE ≫ (m₂.η (n + 1)).app S.X₁ := by rw [← h1, ← h2]

    exact (cancel_epi (F.δ n S hSE)).mp hrhs

/-- Uniqueness in the pointwise formulation, deduced from the morphism version. -/
theorem effaceable_morphism_unique_of_pointwise (F G : CohomDeltaFunctor C D)
    (hF : F.IsEffaceablePointwise)
    (m₁ m₂ : F.Morphism G) (h₀ : m₁.η 0 = m₂.η 0) :
    ∀ n, m₁.η n = m₂.η n :=
  effaceable_morphism_unique_of_effaceableMorphism F G hF.toMorphism m₁ m₂ h₀

/-- Compatibility condition needed to inductively define the next component of a
morphism of δ-functors: the composite `(F^n)(g) ; η_n ; δ_n^G` vanishes. -/
lemma effaceable_step_zero_condition {F G : CohomDeltaFunctor C D}
    (n : ℕ) (X : C) {I : C} (i : X ⟶ I) [Mono i]
    (_hI_map : (F.T (n + 1)).map i = 0)
    (η_n : F.T n ⟶ G.T n) :
    let S := ShortComplex.cokernelSequence i
    let hSE := ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
      (show Mono i from inferInstance) (show Epi (cokernel.π i) from inferInstance)
    (F.T n).map S.g ≫ (η_n.app S.X₃ ≫ G.δ n S hSE) = 0 := by
  simp only

  rw [← Category.assoc, η_n.naturality]

  rw [Category.assoc]

  rw [G.comp_δ_zero, comp_zero]







end DerivedFunctorsDefs
