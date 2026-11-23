/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Atlas.TensorCategories.code.FiniteTensorCategory
import Atlas.TensorCategories.code.ExactModuleCategory

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w

namespace CategoryTheory

/-- `Q` is a retract of `Y` in `C` when there exist morphisms `i : Q ⟶ Y` and
`r : Y ⟶ Q` with `i ≫ r = 𝟙 Q`. -/
def IsRetractOf {C : Type u} [Category.{v} C] (Q Y : C) : Prop :=
  ∃ (i : Q ⟶ Y) (r : Y ⟶ Q), i ≫ r = 𝟙 Q

/-- A retract of a projective object is projective. -/
theorem Projective.of_retract_categorical
    {C : Type u} [Category.{v} C]
    {Q Y : C} (i : Q ⟶ Y) (r : Y ⟶ Q) (hir : i ≫ r = 𝟙 Q)
    [hY : Projective Y] : Projective Q where
  factors := by
    intro E X f e he
    haveI := he
    obtain ⟨h', hh'⟩ := Projective.factors (r ≫ f) e
    exact ⟨i ≫ h', by rw [Category.assoc, hh', ← Category.assoc, hir, Category.id_comp]⟩

/-- A category satisfies `ProjectiveIsInjective` when every projective object is
also injective. -/
class ProjectiveIsInjective (C : Type u) [Category.{v} C] : Prop where
  injective_of_projective : ∀ (P : C), Projective P → Injective P

/-- In a rigid abelian monoidal category whose unit object is injective, every
projective object is injective. -/
noncomputable instance projectiveIsInjective_of_rigid
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [Abelian C]
    [Injective (𝟙_ C)] :
    ProjectiveIsInjective C where
  injective_of_projective P _ := by
    exact Injective.mk (fun {A B : C} (f : A ⟶ P) (m : A ⟶ B) => by
      intro

      haveI : Mono (Pᘁ ◁ m) := by
        have adj := tensorLeftAdjunction (Pᘁ) ((Pᘁ)ᘁ)
        haveI := adj.rightAdjoint_preservesLimits
        haveI : (tensorLeft (Pᘁ)).PreservesMonomorphisms :=
          preservesMonomorphisms_of_preservesLimitsOfShape _
        exact (tensorLeft (Pᘁ)).map_mono m

      set f' : Pᘁ ⊗ A ⟶ 𝟙_ C :=
        (tensorLeftHomEquiv A P (Pᘁ) (𝟙_ C)).symm (f ≫ (ρ_ P).inv)

      obtain ⟨g', hg'⟩ := Injective.factors f' (Pᘁ ◁ m)

      refine ⟨(tensorLeftHomEquiv B P (Pᘁ) (𝟙_ C)) g' ≫ (ρ_ P).hom, ?_⟩
      rw [← cancel_mono (ρ_ P).inv]
      apply (tensorLeftHomEquiv A P (Pᘁ) (𝟙_ C)).symm.injective
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [tensorLeftHomEquiv_symm_naturality]
      simp only [Equiv.symm_apply_apply]
      exact hg')

/-- Any category satisfying `ProjectiveIsInjective` automatically satisfies the
mathlib `HasProjectiveImpliesInjective` typeclass. -/
noncomputable instance (priority := 100) hasProjectiveImpliesInjective_of_rigid
    (C : Type u) [Category.{v} C] [ProjectiveIsInjective C] :
    HasProjectiveImpliesInjective C where
  injective_of_projective P := ProjectiveIsInjective.injective_of_projective P inferInstance

/-- In a rigid abelian monoidal category whose unit object is projective, every
injective object is projective. -/
noncomputable instance injectiveIsProjective_of_rigid
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [Abelian C]
    [Projective (𝟙_ C)] :
    ∀ (I : C), Injective I → Projective I := by
  intro I _
  exact Projective.mk (fun {A B : C} (f : I ⟶ B) (e : A ⟶ B) => by
    intro

    haveI : Epi (e ▷ (Iᘁ : C)) := by
      have adj := tensorRightAdjunction (Iᘁ : C) ((Iᘁ : C)ᘁ)
      haveI := adj.leftAdjoint_preservesColimits
      haveI : (tensorRight (Iᘁ : C)).PreservesEpimorphisms :=
        preservesEpimorphisms_of_preservesColimitsOfShape _
      exact (tensorRight (Iᘁ : C)).map_epi e

    set f' : 𝟙_ C ⟶ B ⊗ (Iᘁ : C) :=
      (tensorRightHomEquiv (𝟙_ C) I (Iᘁ : C) B) ((λ_ I).hom ≫ f)

    obtain ⟨g', hg'⟩ := Projective.factors f' (e ▷ (Iᘁ : C))

    refine ⟨(λ_ I).inv ≫ (tensorRightHomEquiv (𝟙_ C) I (Iᘁ : C) A).symm g', ?_⟩
    rw [Category.assoc, ← cancel_epi (λ_ I).hom,
        ← Category.assoc (λ_ I).hom, Iso.hom_inv_id, Category.id_comp]
    apply (tensorRightHomEquiv (𝟙_ C) I (Iᘁ : C) B).injective
    rw [tensorRightHomEquiv_naturality]
    simp only [Equiv.apply_symm_apply]
    exact hg')

/-- A rigid abelian monoidal category whose unit is both projective and injective
satisfies the quasi-Frobenius property: projectives coincide with injectives. -/
noncomputable instance quasiFrobeniusProperty_of_rigid
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [Abelian C]
    [Injective (𝟙_ C)] [Projective (𝟙_ C)] :
    ExactModuleCategory.QuasiFrobeniusProperty C where
  projective_is_injective X _ :=
    (projectiveIsInjective_of_rigid C).injective_of_projective X inferInstance
  injective_is_projective X _ :=
    injectiveIsProjective_of_rigid C X inferInstance

/-- The monoidal category `C` has a nonzero unit object. -/
class HasNonZeroUnit (C : Type u) [Category.{v} C] [MonoidalCategory C] : Prop where
  unit_nonzero : ¬IsZero (𝟙_ C)

/-- If `End(𝟙_ C)` is nontrivial then the unit object of `C` is nonzero. -/
instance hasNonZeroUnit_of_nontrivial_endUnit
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [h : Nontrivial (End (𝟙_ C))] : HasNonZeroUnit C where
  unit_nonzero := by
    intro hZ
    exact absurd (⟨fun a b => hZ.eq_of_src a b⟩ : Subsingleton (End (𝟙_ C)))
      (not_subsingleton (End (𝟙_ C)))

/-- An abelian monoidal category with enough projectives and a nonzero unit object
admits a nonzero projective object: the projective cover of the unit. -/
lemma exists_nonzero_projective
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    [EnoughProjectives C] [HasNonZeroUnit C] :
    ∃ (Q : C), Projective Q ∧ ¬IsZero Q := by
  refine ⟨Projective.over (𝟙_ C), Projective.projective_over _, ?_⟩
  intro hZ
  apply HasNonZeroUnit.unit_nonzero (C := C)
  rw [IsZero.iff_id_eq_zero]
  have hπ : Projective.π (𝟙_ C) = 0 := hZ.eq_of_src _ _
  rw [← cancel_epi (Projective.π (𝟙_ C)), hπ, zero_comp, comp_zero]

/-- A functor `F : C ⥤ D` is surjective (in the sense used here) if every object
of `D` is a subquotient of some `F.obj X`: there exist a monomorphism into
`F.obj X` and an epimorphism onto `Y` sharing a common source. -/
class Functor.IsSurjective {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ D) : Prop where
  surj : ∀ (Y : D), ∃ (X : C) (A : D) (m : A ⟶ F.obj X) (e : A ⟶ Y), Mono m ∧ Epi e

/-- A quasi-tensor functor between abelian monoidal categories, packaged here as a
class: an additive monoidal functor preserving monomorphisms and epimorphisms. -/
class QuasiTensorFunctor (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] where
  F : C ⥤ D
  monoidal : F.Monoidal
  additive : F.Additive
  preservesMono : F.PreservesMonomorphisms
  preservesEpi : F.PreservesEpimorphisms

/-- A surjective quasi-tensor functor is one whose underlying functor is surjective. -/
class SurjectiveQuasiTensorFunctor (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
    extends QuasiTensorFunctor k C D where
  surjective : F.IsSurjective

/-- Given a surjective quasi-tensor functor `QTF`, every nonzero projective object
`Q` of the target is a retract of the image `QTF.F.obj P` of some projective `P`
in the source. -/
theorem covers_proj_by_proj
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    [EnoughProjectives C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
    [ProjectiveIsInjective D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (Q : D) (hQ_proj : Projective Q) (_hQ_nz : ¬IsZero Q) :
    ∃ (P : C), Projective P ∧ IsRetractOf Q (QTF.F.obj P) := by
  haveI := QTF.surjective
  haveI := QTF.preservesMono
  haveI := QTF.preservesEpi

  obtain ⟨X, A, m, e, hm, he⟩ := Functor.IsSurjective.surj (F := QTF.F) Q
  haveI := hm; haveI := he

  set P := Projective.over X
  set π := Projective.π X
  haveI : Projective P := Projective.projective_over X
  haveI : Epi π := Projective.π_epi X

  have hFπ_epi : Epi (QTF.F.map π) := inferInstance


  haveI := hQ_proj
  haveI : Injective Q := ProjectiveIsInjective.injective_of_projective Q hQ_proj

  obtain ⟨s, hs⟩ := Projective.factors (𝟙 Q) e

  obtain ⟨t, ht⟩ := Projective.factors (s ≫ m) (QTF.F.map π)

  haveI : Mono s := (SplitMono.mk e hs).mono
  haveI : Mono (s ≫ m) := mono_comp s m
  have htMono : Mono t := by
    constructor
    intro Z f g h
    have h1 : f ≫ (s ≫ m) = g ≫ (s ≫ m) := by
      rw [← ht]
      simp only [← Category.assoc]
      rw [h]
    exact (cancel_mono (s ≫ m)).mp h1
  haveI := htMono

  obtain ⟨r, hr⟩ := Injective.factors (𝟙 Q) t
  exact ⟨P, Projective.projective_over X, t, r, hr⟩


/-- The second alternative of the defect dichotomy is impossible when the target
contains a nonzero projective: this follows from `covers_proj_by_proj`. -/
theorem defectDichotomy_not_right
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    [EnoughProjectives C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
    [ProjectiveIsInjective D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (hD_nontrivial : ∃ (Q : D), Projective Q ∧ ¬IsZero Q) :
    ¬(∀ (P : C), Projective P →
      ∀ (Q : D), Projective Q → ¬IsZero Q → ¬IsRetractOf Q (QTF.F.obj P)) := by
  intro h_no_summand
  obtain ⟨Q, hQ_proj, hQ_nz⟩ := hD_nontrivial
  obtain ⟨P', hP'_proj, hRetract⟩ := covers_proj_by_proj QTF Q hQ_proj hQ_nz
  exact h_no_summand P' hP'_proj Q hQ_proj hQ_nz hRetract


end CategoryTheory
