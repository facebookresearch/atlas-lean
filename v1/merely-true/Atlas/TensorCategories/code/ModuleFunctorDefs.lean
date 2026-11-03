/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

set_option maxHeartbeats 400000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- Alias for `ModuleFunctor` matching the textbook numbering of Definition 2.1.2 (the
notion of a module functor between left `C`-module categories) in EGNO. -/
abbrev Definition_2_1_2_ModuleFunctor
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
    (N : Type u₃) [Category.{v₃} N] [LeftModuleCategory C N] :=
  ModuleFunctor C M N

/-- A morphism of module functors between two left `C`-module categories: a natural
transformation `F.toFunctor ⟶ G.toFunctor` whose components are compatible with the module
structure isomorphisms of `F` and `G`. -/
structure ModuleFunctorHom
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]
    (F G : ModuleFunctor C M N) where
  natTrans : F.toFunctor ⟶ G.toFunctor
  compat : ∀ (X : C) (A : M),
    natTrans.app (X ⊗ᵐ A) ≫ (G.strIso X A).hom =
      (F.strIso X A).hom ≫ X ◁ᵐ (natTrans.app A)

attribute [reassoc] ModuleFunctorHom.compat

namespace ModuleFunctorHom

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
  {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]

/-- Two module functor homs are equal whenever their underlying natural transformations are
equal. -/
@[ext]
theorem ext {F G : ModuleFunctor C M N} {η θ : ModuleFunctorHom F G}
    (h : η.natTrans = θ.natTrans) : η = θ := by
  cases η; cases θ; congr

/-- The identity module functor hom on `F`, given by the identity natural transformation. -/
@[simps]
protected def id (F : ModuleFunctor C M N) : ModuleFunctorHom F F where
  natTrans := 𝟙 F.toFunctor
  compat X A := by simp

/-- Composition of module functor homs: the underlying natural transformations are composed
and the compatibility square is verified. -/
@[simps]
protected def comp {F G H : ModuleFunctor C M N}
    (η : ModuleFunctorHom F G) (θ : ModuleFunctorHom G H) :
    ModuleFunctorHom F H where
  natTrans := η.natTrans ≫ θ.natTrans
  compat X A := by
    simp only [NatTrans.comp_app, assoc]
    rw [θ.compat X A, ← assoc, η.compat X A, assoc]
    congr 1


    have := LeftModuleCategory.actTensorHom_comp (𝟙 X) (η.natTrans.app A) (𝟙 X) (θ.natTrans.app A)
    simp [LeftModuleCategory.actTensorHom_def] at this
    exact this

end ModuleFunctorHom

/-- The category structure on `ModuleFunctor C M N` with module functor homs as morphisms,
identity and composition as defined by `ModuleFunctorHom.id` and `ModuleFunctorHom.comp`. -/
instance moduleFunctorCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
    (N : Type u₃) [Category.{v₃} N] [LeftModuleCategory C N] :
    Category (ModuleFunctor C M N) where
  Hom F G := ModuleFunctorHom F G
  id F := ModuleFunctorHom.id F
  comp η θ := ModuleFunctorHom.comp η θ
  id_comp η := by
    apply ModuleFunctorHom.ext
    simp [ModuleFunctorHom.comp, ModuleFunctorHom.id]
  comp_id η := by
    apply ModuleFunctorHom.ext
    simp [ModuleFunctorHom.comp, ModuleFunctorHom.id]
  assoc η θ ξ := by
    apply ModuleFunctorHom.ext
    simp [ModuleFunctorHom.comp]

/-- A module functor is exact if its underlying functor preserves both monomorphisms and
epimorphisms. -/
class ModuleFunctorIsExact
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]
    (F : ModuleFunctor C M N) : Prop where
  preserves_mono : ∀ {A B : M} (f : A ⟶ B), Mono f → Mono (F.toFunctor.map f)
  preserves_epi : ∀ {A B : M} (f : A ⟶ B), Epi f → Epi (F.toFunctor.map f)

/-- In an exact module category, whiskering a monomorphism `f` by a projective object `P`
yields a split monomorphism, witnessed by an explicit retraction. -/
theorem moduleCat_action_split_mono_of_exact
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M]
    [ExactModuleCategory.ActionRightExact C M]
    (P : C) [Projective P] {A B : M} (f : A ⟶ B) (hf : Mono f) :
    ∃ (r : P ⊗ᵐ B ⟶ P ⊗ᵐ A), (P ◁ᵐ f) ≫ r = 𝟙 (P ⊗ᵐ A) := by
  haveI := hf
  have sm := ExactModuleCategory.action_projective_split_mono P f
  exact ⟨sm.retraction, sm.id⟩

/-- A morphism `g` in a module category is a monomorphism if whiskering by every projective
object of `C` (in particular the projective unit) yields a monomorphism. -/
theorem moduleAction_reflects_mono
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [Projective (𝟙_ C)]
    {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]
    {A B : N} (g : A ⟶ B)
    (h : ∀ (P : C), Projective P → Mono (P ◁ᵐ g)) : Mono g := by

  haveI hunit : Mono ((𝟙_ C) ◁ᵐ g) := h (𝟙_ C) inferInstance


  have hnat := LeftModuleCategory.actLeftUnitor_naturality (C := C) (M := N) g
  have hf : g = (actℓ_ A).inv ≫ ((𝟙_ C) ◁ᵐ g) ≫ (actℓ_ B).hom := by
    rw [← hnat.symm, Iso.inv_hom_id_assoc]
  rw [hf]
  exact mono_comp _ _

/-- A morphism `g` in a module category is an epimorphism if whiskering by every projective
object of `C` (in particular the projective unit) yields an epimorphism. -/
theorem moduleAction_reflects_epi
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [Projective (𝟙_ C)]
    {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]
    {A B : N} (g : A ⟶ B)
    (h : ∀ (P : C), Projective P → Epi (P ◁ᵐ g)) : Epi g := by
  haveI hunit : Epi ((𝟙_ C) ◁ᵐ g) := h (𝟙_ C) inferInstance
  have hnat := LeftModuleCategory.actLeftUnitor_naturality (C := C) (M := N) g
  have hf : g = (actℓ_ A).inv ≫ ((𝟙_ C) ◁ᵐ g) ≫ (actℓ_ B).hom := by
    rw [← hnat.symm, Iso.inv_hom_id_assoc]
  rw [hf]
  exact epi_comp _ _

/-- Alias of `moduleAction_reflects_mono`: the action of `C` reflects monomorphisms when
the unit is projective. -/
theorem moduleCat_action_reflects_mono
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [Projective (𝟙_ C)]
    {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]
    {A B : N} (g : A ⟶ B)
    (h : ∀ (P : C), Projective P → Mono (P ◁ᵐ g)) : Mono g :=
  moduleAction_reflects_mono g h

/-- An epimorphism `e : A ⟶ B` with projective target `B` splits, i.e. admits a section
`s : B ⟶ A` with `s ≫ e = 𝟙 B`. -/
theorem moduleCat_splitEpi_of_projective
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    {A B : M} (e : A ⟶ B) (he : Epi e) (hB : Projective B) :
    ∃ (s : B ⟶ A), s ≫ e = 𝟙 B := by
  haveI := he
  haveI := hB
  exact ⟨Projective.factorThru (𝟙 B) e, Projective.factorThru_comp (𝟙 B) e⟩

/-- Alias of `moduleAction_reflects_epi`: the action of `C` reflects epimorphisms when
the unit is projective. -/
theorem moduleCat_action_reflects_epi
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [Projective (𝟙_ C)]
    {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]
    {A B : N} (g : A ⟶ B)
    (h : ∀ (P : C), Projective P → Epi (P ◁ᵐ g)) : Epi g :=
  moduleAction_reflects_epi g h

/-- In an exact module category with biexact action, left whiskering by any object `P : C`
preserves epimorphisms. -/
theorem moduleCat_action_preserves_epi
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M]
    [ExactModuleCategory.BiexactAction C M]
    (P : C) {A B : M} (f : A ⟶ B) (hf : Epi f) : Epi (P ◁ᵐ f) := by
  haveI := hf
  exact ExactModuleCategory.actWhiskerLeft_preserves_epi P f

/-- Any module functor `F` whose source is an exact module category (with biexact action and
projective unit) is automatically exact, i.e. preserves monomorphisms and epimorphisms. -/
theorem moduleFunctorExactBetweenExact
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [Projective (𝟙_ C)]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M]
    [ExactModuleCategory.ActionRightExact C M]
    [ExactModuleCategory.BiexactAction C M]
    {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]
    (F : ModuleFunctor C M N) :
    ModuleFunctorIsExact F where
  preserves_mono := fun {A B} f hf => by

    apply moduleCat_action_reflects_mono (C := C)
    intro P hP
    haveI := hP

    obtain ⟨r, hfr⟩ := moduleCat_action_split_mono_of_exact (C := C) P f hf

    have hFsplit : F.toFunctor.map (P ◁ᵐ f) ≫ F.toFunctor.map r =
        𝟙 (F.toFunctor.obj (P ⊗ᵐ A)) := by
      rw [← F.toFunctor.map_comp, hfr, F.toFunctor.map_id]

    have hnat := F.strIso_natural (𝟙 P) f
    simp at hnat
    have eq1 : P ◁ᵐ F.toFunctor.map f =
      (F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom := by
      rw [← cancel_epi (F.strIso P A).hom, hnat]; simp
    let s := (F.strIso P B).inv ≫ F.toFunctor.map r ≫ (F.strIso P A).hom
    have hsplit : (P ◁ᵐ F.toFunctor.map f) ≫ s = 𝟙 _ := by
      calc (P ◁ᵐ F.toFunctor.map f) ≫ s
          = ((F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom) ≫
            ((F.strIso P B).inv ≫ F.toFunctor.map r ≫ (F.strIso P A).hom) := by rw [eq1]
        _ = (F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫
            ((F.strIso P B).hom ≫ (F.strIso P B).inv) ≫
            F.toFunctor.map r ≫ (F.strIso P A).hom := by simp only [assoc]
        _ = (F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫
            F.toFunctor.map r ≫ (F.strIso P A).hom := by
              rw [(F.strIso P B).hom_inv_id]; simp only [id_comp]
        _ = (F.strIso P A).inv ≫ (F.toFunctor.map (P ◁ᵐ f) ≫ F.toFunctor.map r) ≫
            (F.strIso P A).hom := by simp only [assoc]
        _ = (F.strIso P A).inv ≫ 𝟙 _ ≫ (F.strIso P A).hom := by rw [hFsplit]
        _ = 𝟙 _ := by simp

    constructor
    intro Z g h hgh
    have h1 : (g ≫ (P ◁ᵐ F.toFunctor.map f)) ≫ s = g := by rw [assoc, hsplit, comp_id]
    have h2 : (h ≫ (P ◁ᵐ F.toFunctor.map f)) ≫ s = h := by rw [assoc, hsplit, comp_id]
    rw [← h1, ← h2, hgh]
  preserves_epi := fun {A B} f hf => by

    apply moduleCat_action_reflects_epi (C := C)
    intro P hP
    haveI := hP

    have hPB : Projective (P ⊗ᵐ B) := ExactModuleCategory.action_preserves_projective P B

    have hPf : Epi (P ◁ᵐ f) := moduleCat_action_preserves_epi (C := C) P f hf

    obtain ⟨t, hft⟩ := moduleCat_splitEpi_of_projective (C := C) (P ◁ᵐ f) hPf hPB

    have hFsplit : F.toFunctor.map t ≫ F.toFunctor.map (P ◁ᵐ f) =
        𝟙 (F.toFunctor.obj (P ⊗ᵐ B)) := by
      rw [← F.toFunctor.map_comp, hft, F.toFunctor.map_id]

    have hnat := F.strIso_natural (𝟙 P) f
    simp at hnat
    have eq1 : P ◁ᵐ F.toFunctor.map f =
      (F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom := by
      rw [← cancel_epi (F.strIso P A).hom, hnat]; simp
    let sec := (F.strIso P B).inv ≫ F.toFunctor.map t ≫ (F.strIso P A).hom
    have hsplit : sec ≫ (P ◁ᵐ F.toFunctor.map f) = 𝟙 _ := by
      calc sec ≫ (P ◁ᵐ F.toFunctor.map f)
          = ((F.strIso P B).inv ≫ F.toFunctor.map t ≫ (F.strIso P A).hom) ≫
            ((F.strIso P A).inv ≫ F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom) := by
              rw [eq1]
        _ = (F.strIso P B).inv ≫ F.toFunctor.map t ≫
            ((F.strIso P A).hom ≫ (F.strIso P A).inv) ≫
            F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom := by simp only [assoc]
        _ = (F.strIso P B).inv ≫ F.toFunctor.map t ≫
            F.toFunctor.map (P ◁ᵐ f) ≫ (F.strIso P B).hom := by
              rw [(F.strIso P A).hom_inv_id]; simp only [id_comp]
        _ = (F.strIso P B).inv ≫ (F.toFunctor.map t ≫ F.toFunctor.map (P ◁ᵐ f)) ≫
            (F.strIso P B).hom := by simp only [assoc]
        _ = (F.strIso P B).inv ≫ 𝟙 _ ≫ (F.strIso P B).hom := by rw [hFsplit]
        _ = 𝟙 _ := by simp

    constructor
    intro Z g h hgh
    have h1 : sec ≫ (P ◁ᵐ F.toFunctor.map f) ≫ g = g := by rw [← assoc, hsplit, id_comp]
    have h2 : sec ≫ (P ◁ᵐ F.toFunctor.map f) ≫ h = h := by rw [← assoc, hsplit, id_comp]
    rw [← h1, ← h2, hgh]

/-- Baseline assumption for a finite multitensor category: the monoidal unit `𝟙_ C` is
projective. -/
class FiniteMultitensorBase (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] : Prop where
  unit_projective : Projective (𝟙_ C)

/-- Bundle of the standard exactness infrastructure on a module category `M`: abelianness,
right-exactness of the action, and biexactness of the action bifunctor. -/
class ExactModuleInfra (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [ExactModuleCategory C M] where
  abelian : Abelian M
  actionRightExact : ExactModuleCategory.ActionRightExact C M
  biexact : ExactModuleCategory.BiexactAction C M

attribute [instance] FiniteMultitensorBase.unit_projective
attribute [instance] ExactModuleInfra.abelian ExactModuleInfra.actionRightExact
  ExactModuleInfra.biexact

/-- Proposition 2.7.8 (EGNO): Any module functor from an exact module category over a finite
multitensor category to another module category is exact. -/
theorem proposition_2_7_8
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [FiniteMultitensorBase C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [ExactModuleInfra C M]
    {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]
    (F : ModuleFunctor C M N) :
    ModuleFunctorIsExact F :=
  moduleFunctorExactBetweenExact F

/-- Post-composition leg of the biexactness of the composition bifunctor: post-composing a
module natural transformation `η : F₁ ⟶ F₂` with an exact module functor `G` preserves both
monomorphism and epimorphism components. -/
theorem compositionBifunctorBiexact_postcomp
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [Projective (𝟙_ C)]
    {M₁ : Type u₂} [Category.{v₂} M₁] [ExactModuleCategory C M₁]
    {M₂ : Type u₃} [Category.{v₃} M₂] [ExactModuleCategory C M₂] [Abelian M₂]
    [ExactModuleCategory.ActionRightExact C M₂]
    [ExactModuleCategory.BiexactAction C M₂]
    {M₃ : Type u₄} [Category.{v₄} M₃] [ExactModuleCategory C M₃]
    (G : ModuleFunctor C M₂ M₃)
    {F₁ F₂ : ModuleFunctor C M₁ M₂} (η : F₁ ⟶ F₂) :

    (∀ (A : M₁), Mono (η.natTrans.app A) → Mono (G.toFunctor.map (η.natTrans.app A))) ∧

    (∀ (A : M₁), Epi (η.natTrans.app A) → Epi (G.toFunctor.map (η.natTrans.app A))) :=

  let hG := moduleFunctorExactBetweenExact G
  ⟨fun A hm => hG.preserves_mono (η.natTrans.app A) hm,
   fun A he => hG.preserves_epi (η.natTrans.app A) he⟩

/-- Pre-composition leg of the biexactness of the composition bifunctor: pre-composing a
module natural transformation `η : G₁ ⟶ G₂` with a module functor `F : M₁ ⥤ M₂` transports
the mono/epi component conditions appropriately. -/
theorem compositionBifunctorBiexact_precomp
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M₁ : Type u₂} [Category.{v₂} M₁] [ExactModuleCategory C M₁]
    {M₂ : Type u₃} [Category.{v₃} M₂] [ExactModuleCategory C M₂] [Abelian M₂]
    {M₃ : Type u₄} [Category.{v₄} M₃] [ExactModuleCategory C M₃]
    (F : ModuleFunctor C M₁ M₂)
    {G₁ G₂ : ModuleFunctor C M₂ M₃} (η : G₁ ⟶ G₂) :

    ((∀ (B : M₂), Mono (η.natTrans.app B)) →
      ∀ (A : M₁), Mono (η.natTrans.app (F.toFunctor.obj A))) ∧

    ((∀ (B : M₂), Epi (η.natTrans.app B)) →
      ∀ (A : M₁), Epi (η.natTrans.app (F.toFunctor.obj A))) :=
  ⟨fun hm A => hm (F.toFunctor.obj A), fun he A => he (F.toFunctor.obj A)⟩








end CategoryTheory
