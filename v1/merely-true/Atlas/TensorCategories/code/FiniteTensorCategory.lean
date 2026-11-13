/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Atlas.TensorCategories.code.QuasiBialgebra
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.Projective
import Atlas.TensorCategories.code.FrobeniusPerron
import Atlas.TensorCategories.code.QuasiTensorFunctor

import Atlas.TensorCategories.code.RegularObject

set_option maxHeartbeats 800000

universe w₀

namespace CategoryTheory

open MonoidalCategory

/-- A monoidal category satisfies `TensorPreservesProjective` if tensoring any object
with a projective object on the left yields a projective object. -/
class TensorPreservesProjective (C : Type*) [Category C] [MonoidalCategory C] : Prop where
  tensor_projective : ∀ (P N : C), [Projective P] → Projective (P ⊗ N)

set_option backward.isDefEq.respectTransparency false in
/-- In a rigid monoidal category the right-tensoring functor has a right adjoint, so
tensoring with a projective object on the left preserves projectivity. -/
noncomputable instance tensorPreservesProjective_of_rigid
    (C : Type*) [Category C] [MonoidalCategory C] [RigidCategory C] :
    TensorPreservesProjective C where
  tensor_projective P N := by
    intro hP
    haveI : (tensorRight (Nᘁ : C)).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction (tensorRightAdjunction (Nᘁ : C) ((Nᘁ : C)ᘁ))
    exact (tensorRightAdjunction N (Nᘁ)).map_projective P hP

end CategoryTheory

open scoped TensorProduct

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u w

namespace CategoryTheory

/-- A finite tensor category over `k` is a `k`-linear rigid abelian monoidal category
with enough projectives and finite-dimensional Hom spaces (EGNO Definition 4.1). -/
class FiniteTensorCategory (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    extends MonoidalCategory C, Abelian C, Linear k C, RigidCategory C where
  enoughProj : EnoughProjectives C
  homFiniteDim : ∀ (X Y : C), FiniteDimensional k (X ⟶ Y)

section FiniteTensorCategoryLemmas

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [FiniteTensorCategory k C]

include k in
/-- A finite tensor category has enough projectives. -/
theorem FiniteTensorCategory.enough_projectives : EnoughProjectives C :=
  FiniteTensorCategory.enoughProj k

/-- Hom spaces in a finite tensor category are finite-dimensional over the base field. -/
theorem FiniteTensorCategory.hom_finite_dimensional (X Y : C) :
    FiniteDimensional k (X ⟶ Y) :=
  FiniteTensorCategory.homFiniteDim X Y

end FiniteTensorCategoryLemmas

/-- A projective cover of `X` is a projective object `P` with an epimorphism `π : P ⟶ X`
that is minimal: any endomorphism of `P` commuting with `π` is an isomorphism. -/
structure IsProjectiveCover {C : Type u} [Category.{v} C] (P X : C) where
  π : P ⟶ X
  proj : Projective P
  epi_π : Epi π
  minimal : ∀ (f : P ⟶ P), f ≫ π = π → IsIso f

/-- `P` is an indecomposable projective if it is both projective and indecomposable. -/
def IsIndecomposableProjective {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasBinaryBiproducts C] (P : C) : Prop :=
  Projective P ∧ Indecomposable P

section SimpleLemmas

variable {C : Type u} [Category.{v} C]

/-- A simple object in an abelian category is indecomposable. -/
theorem Simple.indecomposable' [Abelian C] (X : C) [Simple X] : Indecomposable X :=
  indecomposable_of_simple X

end SimpleLemmas

/-- A preadditive category has local endomorphism rings of projectives if `End P` is a
local ring for every projective `P`. -/
class HasLocalEndomorphismRings (C : Type u) [Category.{v} C] [Preadditive C] : Prop where
  isLocalRing_end : ∀ (P : C) [Projective P], IsLocalRing (End P)

/-- If `End P` is local, `P` is projective, and `X` is simple, then any endomorphism
`f` of `P` satisfying `f ≫ π = π` for an epi `π : P ⟶ X` is automatically an
isomorphism. -/
theorem endo_isIso_of_comp_epi_eq_of_localEnd
    {C : Type u} [Category.{v} C] [Abelian C]
    {P X : C} [Projective P] [Simple X]
    [IsLocalRing (End P)]
    (π : P ⟶ X) [Epi π] (f : End P) (hf : f ≫ π = π) : IsIso f := by
  set g : End P := 1 - f with hg_def

  have h1 : g ≫ π = 0 := by
    have key : g ≫ π = 𝟙 P ≫ π - f ≫ π := by
      show (1 - f) ≫ π = 𝟙 P ≫ π - f ≫ π
      rw [show (1 : End P) = (𝟙 P : End P) from rfl]
      exact Preadditive.sub_comp (𝟙 P) f π
    rw [key, Category.id_comp, hf, sub_self]

  have hlocal : IsUnit f ∨ IsUnit g := by
    apply IsLocalRing.isUnit_or_isUnit_of_add_one
    show f + (1 - f) = 1; simp
  cases hlocal with
  | inl hu =>

    rwa [isUnit_iff_isIso] at hu
  | inr hu =>

    rw [isUnit_iff_isIso] at hu
    exfalso
    have hπ_zero : π = 0 := by
      calc π = 𝟙 P ≫ π := (Category.id_comp π).symm
        _ = (inv g ≫ g) ≫ π := by rw [IsIso.inv_hom_id]
        _ = inv g ≫ (g ≫ π) := (Category.assoc _ _ _)
        _ = inv g ≫ 0 := by rw [h1]
        _ = 0 := comp_zero

    exact (indecomposable_of_simple X).1
      (by rw [IsZero.iff_id_eq_zero, ← cancel_epi π, hπ_zero, zero_comp, comp_zero])

/-- A category has projective covers of simples if the minimality condition for
projective covers holds for all simple targets. -/
class HasProjectiveCoversOfSimples (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :
    Prop where
  endo_isIso_of_comp_epi_eq :
    ∀ (P X : C) [Projective P] [Simple X] (π : P ⟶ X) [Epi π] (f : P ⟶ P),
      f ≫ π = π → IsIso f

/-- Local endomorphism rings of projectives imply the projective cover minimality
condition for all simple targets. -/
instance (priority := 100) hasProjectiveCoversOfSimples_of_localEnd
    (C : Type u) [Category.{v} C] [Abelian C] [HasLocalEndomorphismRings C] :
    HasProjectiveCoversOfSimples C where
  endo_isIso_of_comp_epi_eq := by
    intro P X _ _ π _ f hf
    haveI : IsLocalRing (End P) := HasLocalEndomorphismRings.isLocalRing_end P
    exact endo_isIso_of_comp_epi_eq_of_localEnd π (f : End P) hf

/-- Existence of a projective cover for any simple object, given enough projectives and
the projective cover minimality property. -/
noncomputable def exists_projective_cover_of_simple
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    [HasProjectiveCoversOfSimples C]
    (X : C) [Simple X] : Σ P, IsProjectiveCover P X :=
  haveI : Projective (Projective.over X) := Projective.projective_over X
  haveI : Epi (Projective.π X) := Projective.π_epi X
  ⟨Projective.over X,
    { π := Projective.π X
      proj := inferInstance
      epi_π := inferInstance
      minimal := fun f hf =>
        HasProjectiveCoversOfSimples.endo_isIso_of_comp_epi_eq _ X _ f hf }⟩

/-- The projective cover of a simple object is indecomposable. -/
theorem projective_cover_simple_indecomposable
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    [HasProjectiveCoversOfSimples C]
    (X : C) [Simple X] :
    Indecomposable (exists_projective_cover_of_simple X).1 := by
  set cover := exists_projective_cover_of_simple X
  set P := cover.1
  set pc := cover.2
  set π := pc.π
  haveI : Projective P := pc.proj
  haveI : Epi π := pc.epi_π
  refine ⟨?_, ?_⟩
  ·
    exact fun hP => (indecomposable_of_simple X).1 (IsZero.of_epi π hP)
  ·
    intro A B φ
    set gA : A ⟶ X := biprod.inl ≫ φ.inv ≫ π
    set gB : B ⟶ X := biprod.inr ≫ φ.inv ≫ π

    have aux_B_zero : Epi gA → IsZero B := by
      intro _
      obtain ⟨s, hs⟩ := Projective.factors π gA
      set f : P ⟶ P := s ≫ biprod.inl ≫ φ.inv
      have hfπ : f ≫ π = π := by simp only [f, Category.assoc]; exact hs
      haveI := pc.minimal f hfπ
      have key : (f ≫ φ.hom) ≫ biprod.snd = 0 := by
        simp only [f, Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_snd, comp_zero]
      haveI : IsIso (f ≫ φ.hom) := inferInstance
      have hsnd : (biprod.snd : A ⊞ B ⟶ B) = 0 := by
        rw [show (biprod.snd : A ⊞ B ⟶ B) = 𝟙 _ ≫ biprod.snd from (Category.id_comp _).symm,
            show 𝟙 (A ⊞ B) = inv (f ≫ φ.hom) ≫ (f ≫ φ.hom) from (IsIso.inv_hom_id _).symm,
            Category.assoc, key, comp_zero]
      rw [IsZero.iff_id_eq_zero]
      calc 𝟙 B = biprod.inr ≫ biprod.snd := biprod.inr_snd.symm
        _ = biprod.inr ≫ 0 := by rw [hsnd]
        _ = 0 := comp_zero

    have aux_A_zero : Epi gB → IsZero A := by
      intro _
      obtain ⟨s, hs⟩ := Projective.factors π gB
      set f : P ⟶ P := s ≫ biprod.inr ≫ φ.inv
      have hfπ : f ≫ π = π := by simp only [f, Category.assoc]; exact hs
      haveI := pc.minimal f hfπ
      have key : (f ≫ φ.hom) ≫ biprod.fst = 0 := by
        simp only [f, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_fst, comp_zero]
      haveI : IsIso (f ≫ φ.hom) := inferInstance
      have hfst : (biprod.fst : A ⊞ B ⟶ A) = 0 := by
        rw [show (biprod.fst : A ⊞ B ⟶ A) = 𝟙 _ ≫ biprod.fst from (Category.id_comp _).symm,
            show 𝟙 (A ⊞ B) = inv (f ≫ φ.hom) ≫ (f ≫ φ.hom) from (IsIso.inv_hom_id _).symm,
            Category.assoc, key, comp_zero]
      rw [IsZero.iff_id_eq_zero]
      calc 𝟙 A = biprod.inl ≫ biprod.fst := biprod.inl_fst.symm
        _ = biprod.inl ≫ 0 := by rw [hfst]
        _ = 0 := comp_zero

    by_cases hgA : gA = 0
    · have hgB : gB ≠ 0 := by
        intro hgB0
        have h0 : φ.inv ≫ π = 0 := by
          apply biprod.hom_ext'
          · simp [show biprod.inl ≫ (φ.inv ≫ π) = gA from by simp [gA], hgA]
          · simp [show biprod.inr ≫ (φ.inv ≫ π) = gB from by simp [gB], hgB0]
        exact (indecomposable_of_simple X).1
          (IsZero.of_epi_eq_zero π
            (by rw [show π = φ.hom ≫ (φ.inv ≫ π) from by simp, h0, comp_zero]))
      left; exact aux_A_zero (epi_of_nonzero_to_simple hgB)
    · right; exact aux_B_zero (epi_of_nonzero_to_simple hgA)

/-- Any epimorphism onto a simple object is nonzero. -/
lemma nonzero_of_epi_to_simple {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} [Simple Y] (f : X ⟶ Y) [Epi f] : f ≠ 0 := by
  intro hf
  exact id_nonzero Y ((cancel_epi f).mp (by rw [hf]; simp))

/-- Tensoring with a projective object on either side preserves projectivity. -/
class HasTensorProjectiveProperty (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasZeroMorphisms C] : Prop where
  tensor_projective_right : ∀ (P X : C) [Projective P], Projective (P ⊗ X)
  tensor_projective_left : ∀ (X P : C) [Projective P], Projective (X ⊗ P)

/-- In a rigid monoidal category, the tensor product preserves projectives on both
sides via the appropriate adjunctions. -/
noncomputable instance (priority := 100) hasTensorProjectiveProperty_of_rigid
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]
    [RigidCategory C] :
    HasTensorProjectiveProperty C where
  tensor_projective_right P X := by
    intro
    exact (tensorPreservesProjective_of_rigid C).tensor_projective P X
  tensor_projective_left X P := by
    intro

    have adj := tensorLeftAdjunction (ᘁX) X

    have adj2 := tensorLeftAdjunction (ᘁ(ᘁX : C)) (ᘁX : C)
    haveI : (tensorLeft (ᘁX : C)).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction adj2
    exact adj.map_projective P inferInstance

/-- Both the left and right duals of a projective object are projective. -/
class HasDualProjectiveProperty (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasZeroMorphisms C] [RigidCategory C] : Prop where
  rightDual_projective : ∀ (P : C) [Projective P], Projective (Pᘁ)
  leftDual_projective : ∀ (P : C) [Projective P], Projective (ᘁP)

/-- In a rigid monoidal category with projective unit, both duals of any projective
object are again projective. -/
noncomputable instance (priority := 100) hasDualProjectiveProperty_of_rigid
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] [HasZeroMorphisms C] [Projective (𝟙_ C)] :
    HasDualProjectiveProperty C where
  rightDual_projective P := Projective.mk (fun {E X} f e => by
    intro
    let Φ := tensorLeftHomEquiv (𝟙_ C) P (HasRightDual.rightDual P)
    let f₁ : HasRightDual.rightDual P ⊗ 𝟙_ C ⟶ X := (ρ_ _).hom ≫ f
    let f₂ : 𝟙_ C ⟶ P ⊗ X := Φ X f₁
    have adj : tensorLeft P ⊣ tensorLeft (ᘁP) := tensorLeftAdjunction (ᘁP) P
    haveI : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
      adj.leftAdjoint_preservesColimits
    haveI : (tensorLeft P).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape _
    have : Epi (P ◁ e) := (tensorLeft P).map_epi e
    obtain ⟨g₂, hg₂⟩ := Projective.factors f₂ (P ◁ e)
    let g₁ : HasRightDual.rightDual P ⊗ 𝟙_ C ⟶ E := (Φ E).symm g₂
    refine ⟨(ρ_ _).inv ≫ g₁, ?_⟩
    have key : g₁ ≫ e = f₁ := by
      apply (Φ X).injective
      rw [tensorLeftHomEquiv_naturality g₁ e]
      change (Φ E) g₁ ≫ P ◁ e = (Φ X) f₁
      simp only [g₁, Equiv.apply_symm_apply]
      exact hg₂
    simp only [Category.assoc, key, f₁, Iso.inv_hom_id_assoc])
  leftDual_projective P := Projective.mk (fun {E X} f e => by
    intro
    let Φ := tensorRightHomEquiv (𝟙_ C) (ᘁP) P
    let f₁ : 𝟙_ C ⊗ HasLeftDual.leftDual P ⟶ X := (λ_ _).hom ≫ f
    let f₂ : 𝟙_ C ⟶ X ⊗ P := Φ X f₁
    have adj : tensorRight P ⊣ tensorRight (Pᘁ) := tensorRightAdjunction P (Pᘁ)
    haveI : PreservesColimitsOfSize.{0, 0} (tensorRight P) :=
      adj.leftAdjoint_preservesColimits
    haveI : (tensorRight P).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape _
    have : Epi (e ▷ P) := (tensorRight P).map_epi e
    obtain ⟨g₂, hg₂⟩ := Projective.factors f₂ (e ▷ P)
    let g₁ : 𝟙_ C ⊗ HasLeftDual.leftDual P ⟶ E := (Φ E).symm g₂
    refine ⟨(λ_ _).inv ≫ g₁, ?_⟩
    have key : g₁ ≫ e = f₁ := by
      apply (Φ X).injective
      rw [tensorRightHomEquiv_naturality g₁ e]
      change (Φ E) g₁ ≫ e ▷ P = (Φ X) f₁
      simp only [g₁, Equiv.apply_symm_apply]
      exact hg₂
    simp only [Category.assoc, key, f₁, Iso.inv_hom_id_assoc])

/-- A category in which every projective object is injective (the quasi-Frobenius
property at the level of `C`). -/
class HasProjectiveImpliesInjective (C : Type u) [Category.{v} C] : Prop where
  injective_of_projective : ∀ (P : C) [Projective P], Injective P

/-- A rigid abelian monoidal category with enough projectives is asserted to also have
enough injectives. -/
class HasEnoughInjectivesFromRigid (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [EnoughProjectives C] : Prop where
  enoughInj : EnoughInjectives C

/-- Axiomatic Jordan-Hölder multiplicity of a simple object `X` in `Y`. -/
class HasJordanHolderMultiplicity (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] where
  multiplicity : (X : C) → [Simple X] → (Y : C) → ℕ
  multiplicity_self : ∀ (X : C) [Simple X], multiplicity X X = 1

/-- The formula relating Hom-space dimension to Jordan-Hölder multiplicity:
`dim_k Hom(P_X, Y) = [Y : X]` for the projective cover `P_X` of a simple `X`. -/
class HasHomMultiplicityFormula (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [EnoughProjectives C]
    [HasJordanHolderMultiplicity k C] where
  dim_hom_projCover_eq :
    ∀ (X : C) [Simple X] (Y : C),
      Module.finrank k (Projective.over X ⟶ Y) =
        HasJordanHolderMultiplicity.multiplicity (k := k) X Y

/-- Combinatorial data attached to a finite tensor category: an index set `ι` for the
simple objects together with their Frobenius-Perron dimensions, the FP-dimensions of
their projective covers, the Cartan matrix entries, and the relevant positivity and
compatibility hypotheses. -/
structure FiniteTensorCategoryData where
  ι : Type*
  [ι_fintype : Fintype ι]
  [ι_decidableEq : DecidableEq ι]
  [ι_nonempty : Nonempty ι]
  fpDimSimple : ι → ℝ
  fpDimProjCover : ι → ℝ
  cartanEntry : ι → ι → ℕ
  fpDimSimple_pos : ∀ i, fpDimSimple i > 0
  fpDimProjCover_pos : ∀ i, fpDimProjCover i > 0
  cartanEntry_diag_pos : ∀ i, cartanEntry i i ≥ 1
  proj_dim_eq_sum : ∀ i,
    (∑ j : ι, (cartanEntry i j : ℝ) * fpDimSimple j) = fpDimProjCover i

attribute [instance] FiniteTensorCategoryData.ι_fintype
  FiniteTensorCategoryData.ι_decidableEq FiniteTensorCategoryData.ι_nonempty

namespace FiniteTensorCategoryData

variable (D : FiniteTensorCategoryData)

/-- The coefficient of the `i`th simple in the regular object: it is the FP-dimension of
the simple. -/
def regularObjectCoeff (i : D.ι) : ℝ := D.fpDimSimple i

/-- The Frobenius-Perron dimension of the category, given by
`∑_i FPdim(X_i) · FPdim(P_{X_i})`. -/
noncomputable def catFPdim : ℝ :=
  ∑ i : D.ι, D.fpDimSimple i * D.fpDimProjCover i

/-- A property capturing the "key equation" relating multiplicities and FP-dimensions
of simples in a fixed object `Z`. -/
def keyEquation_prop : Prop :=
  ∀ (mult : D.ι → ℕ), ∀ (fpDimZ : ℝ),
    (fpDimZ = ∑ j : D.ι, (mult j : ℝ) * D.fpDimSimple j) →
    (∑ i : D.ι, D.fpDimSimple i * (mult i : ℝ)) = fpDimZ

end FiniteTensorCategoryData

/-- The categorical Frobenius-Perron dimension of a monoidal category, packaged with the
data witnessing positivity. -/
class HasCategoricalFPdim (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  data : FiniteTensorCategoryData
  fpdimCat : ℝ := data.catFPdim
  fpdimCat_eq : fpdimCat = data.catFPdim := by rfl
  fpdimCat_pos : fpdimCat > 0 := by rw [fpdimCat_eq]; exact data.catFPdim_pos

/-- Definition 1.47.5 (EGNO): The categorical Frobenius-Perron dimension. Alias of
`HasCategoricalFPdim`. -/
abbrev Definition_1_47_5_CategoricalFPdim := @HasCategoricalFPdim

section FPdim

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A Frobenius-Perron dimension function: a positive real-valued function on `C` that
is `1` on the unit, multiplicative on tensor products, and invariant under
isomorphisms. -/
structure FPdimFunction where
  fpDim : C → ℝ
  fpDim_unit : fpDim (𝟙_ C) = 1
  fpDim_pos : ∀ (X : C), fpDim X > 0
  fpDim_tensor : ∀ (X Y : C), fpDim (X ⊗ Y) = fpDim X * fpDim Y
  fpDim_iso : ∀ (X Y : C), Nonempty (X ≅ Y) → fpDim X = fpDim Y

end FPdim

section GrothendieckFPdim

/-- A monoidal category equipped with a Grothendieck fusion ring structure and a
compatible Frobenius-Perron dimension function lifted from the abstract fusion ring data.
-/
class HasGrothendieckFusionRing (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  ι : Type*
  [ι_decidableEq : DecidableEq ι]
  [ι_fintype : Fintype ι]
  [ι_nonempty : Nonempty ι]
  [ι_hasPF : FusionRing.HasPerronFrobeniusProperty ι]
  fusionRing : FusionRing ι
  liftFPdimData : fusionRing.FPdimData → FPdimFunction (C := C)
  fpDimFunction_eq : ∀ (fpd : fusionRing.FPdimData) (d : FPdimFunction (C := C)) (X : C),
    d.fpDim X = (liftFPdimData fpd).fpDim X

end GrothendieckFPdim

section FPdimProperties

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace FPdimFunction

variable (d : FPdimFunction (C := C))

/-- A Frobenius-Perron dimension function is integral if it takes integer values on
every object. -/
def IsIntegral : Prop :=
  ∀ (X : C), ∃ (n : ℤ), d.fpDim X = ↑n

end FPdimFunction

end FPdimProperties

/-- A bimodule structure on the Grothendieck group `K₀`: tensoring with a projective
object on either side stays in the projective ideal. -/
class HasK0BimoduleStructure (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasZeroMorphisms C] : Prop where
  tensor_proj_in_K0_left : ∀ (P X : C) [Projective P], Projective (P ⊗ X)
  tensor_proj_in_K0_right : ∀ (X P : C) [Projective P], Projective (X ⊗ P)

/-- `HasTensorProjectiveProperty` implies the `K₀` bimodule structure. -/
instance (priority := 100) hasK0Bimodule_of_tensorProjective
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]
    [HasTensorProjectiveProperty C] : HasK0BimoduleStructure C where
  tensor_proj_in_K0_left := HasTensorProjectiveProperty.tensor_projective_right
  tensor_proj_in_K0_right := HasTensorProjectiveProperty.tensor_projective_left

/-- Every indecomposable projective object contains a simple subobject (its socle is
simple). -/
class HasSimpleSocleProperty (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C] : Prop where
  simple_socle : ∀ (P : C) [Projective P],
    Indecomposable P → ∃ (S : C) (_ : Simple S) (ι : S ⟶ P), Mono ι

/-- A monoidal category equipped with the FP data needed to define a regular object. -/
class HasRegularObject (C : Type u) [Category.{v} C]
    [MonoidalCategory C] where
  fpData : FiniteTensorCategoryFPData

/-- The index set of simples in a category equipped with a regular object. -/
abbrev HasRegularObject.ι {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] := h.fpData.I

/-- The index set of simples is finite. -/
instance {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [h : HasRegularObject C] : Fintype h.ι := h.fpData.I_fintype

/-- The index set of simples is nonempty. -/
instance {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [h : HasRegularObject C] : Nonempty h.ι := h.fpData.I_nonempty

/-- The regular object of `C`, viewed as a formal projective sum of simples. -/
noncomputable def HasRegularObject.regularObj {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] :
    FormalProjectiveSum h.ι := h.fpData.regularObject

/-- The `i`th coefficient of the regular object equals the FP-dimension of the
corresponding simple. -/
@[simp]
theorem HasRegularObject.regularObj_coeff {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] (i : h.ι) :
    h.regularObj.coeff i = h.fpData.fpDimSimple i := by
  simp [regularObj]

/-- Convenience accessor for the `i`th coefficient of the regular object. -/
noncomputable def HasRegularObject.regularCoeff {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] (i : h.ι) : ℝ :=
  h.regularObj.coeff i

/-- The FP-dimension of the projective cover of the `i`th simple. -/
def HasRegularObject.fpDimProjCover {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] (i : h.ι) : ℝ :=
  h.fpData.fpDimProjCover i

/-- Each coefficient of the regular object is strictly positive. -/
theorem HasRegularObject.regularCoeff_pos {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] (i : h.ι) :
    h.regularCoeff i > 0 := by
  simp only [regularCoeff, regularObj_coeff]
  exact h.fpData.fpDimSimple_pos i

/-- Each FP-dimension of a projective cover is strictly positive. -/
theorem HasRegularObject.fpDimProjCover_pos {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] (i : h.ι) :
    h.fpDimProjCover i > 0 := h.fpData.fpDimProjCover_pos i

/-- Definition 1.47.4 (EGNO): The regular object of a finite tensor category. -/
noncomputable abbrev Definition_1_47_4_RegularObject := @HasRegularObject.regularObj

/-- The FP-dimension of the regular object: a real-valued invariant of the category. -/
noncomputable def HasRegularObject.fpdimRegular {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] : ℝ :=
  h.regularObj.fpdim h.fpData.fpDimProjCover

/-- The FP-dimension of the regular object is the sum
`∑_i (regularCoeff_i) · (FPdim of projective cover_i)`. -/
theorem HasRegularObject.fpdimRegular_eq {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] :
    HasRegularObject.fpdimRegular (C := C) =
      ∑ i : h.ι, h.regularCoeff i * h.fpDimProjCover i := by
  unfold fpdimRegular FormalProjectiveSum.fpdim regularCoeff fpDimProjCover
  rfl

/-- The FP-dimension of the regular object is strictly positive. -/
theorem HasRegularObject.fpdimRegular_pos {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] :
    HasRegularObject.fpdimRegular (C := C) > 0 := by
  rw [fpdimRegular_eq]
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (h.regularCoeff_pos i) (h.fpDimProjCover_pos i)
  · exact Finset.univ_nonempty

/-- Regularity of the regular object: all coefficients are positive and the FP-dimension
of the regular object is nonzero. -/
class HasRegularObjectRegularity (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] : Prop where
  regularCoeff_allPos : ∀ i : h.ι,
    h.regularCoeff i > 0
  fpdimRegular_ne_zero : HasRegularObject.fpdimRegular (C := C) ≠ 0

/-- The FP-dimension of the regular object is nonzero, since it is positive. -/
theorem fpdimRegular_ne_zero_of_pos {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [HasRegularObject C] :
    HasRegularObject.fpdimRegular (C := C) ≠ 0 :=
  ne_of_gt HasRegularObject.fpdimRegular_pos

/-- Any `HasRegularObject` automatically satisfies the regularity hypotheses. -/
instance (priority := 100) hasRegularObjectRegularity_of_hasRegularObject
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [h : HasRegularObject C] : HasRegularObjectRegularity C where
  regularCoeff_allPos := h.regularCoeff_pos
  fpdimRegular_ne_zero := fpdimRegular_ne_zero_of_pos

/-- Hypothesis package giving the inequality
`fpdimCat C > numSimples · fpdimProjUnit` together with positivity of the witnesses. -/
class HasFPdimInequality (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [EnoughProjectives C]
    [HasCategoricalFPdim C] where
  numSimples : ℕ
  numSimples_pos : numSimples > 0
  fpdimProjUnit : ℝ
  fpdimProjUnit_pos : fpdimProjUnit > 0
  fpdim_gt_numSimples_mul_fpdimProjUnit :
    HasCategoricalFPdim.fpdimCat (C := C) > ↑numSimples * fpdimProjUnit

section FPdimInequalityLemmas

variable {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [EnoughProjectives C]
    [HasCategoricalFPdim C] [h : HasFPdimInequality C]

/-- Consequence of `HasFPdimInequality`: the categorical FP-dimension is strictly
greater than the FP-dimension of the projective cover of the unit. -/
theorem fpdimCat_ge_fpdimProjUnit :
    HasCategoricalFPdim.fpdimCat (C := C) > h.fpdimProjUnit := by
  have hN : (↑h.numSimples : ℝ) ≥ 1 := by exact_mod_cast h.numSimples_pos
  calc HasCategoricalFPdim.fpdimCat (C := C)
      > ↑h.numSimples * h.fpdimProjUnit :=
        h.fpdim_gt_numSimples_mul_fpdimProjUnit
    _ ≥ 1 * h.fpdimProjUnit := by
        apply mul_le_mul_of_nonneg_right hN (le_of_lt h.fpdimProjUnit_pos)
    _ = h.fpdimProjUnit := one_mul _

end FPdimInequalityLemmas

/-- Witnesses that the categorical FP-dimension equals the dimension of an associated
finite-dimensional algebra. -/
class HasFPdimEqDimAlgebra (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasCategoricalFPdim C] where
  dimAlgebra : ℕ
  fpdimCat_eq_dimAlgebra : HasCategoricalFPdim.fpdimCat (C := C) = ↑dimAlgebra

/-- A Cartan matrix structure on a `k`-linear category with Jordan-Hölder multiplicities:
a finite index set `ι` and integer entries with positive diagonal. -/
class HasCartanMatrix (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [HasJordanHolderMultiplicity k C] where
  ι : Type*
  [ι_fintype : Fintype ι]
  cartanEntry : ι → ι → ℕ
  cartanEntry_diag_pos : ∀ (i : ι), cartanEntry i i ≥ 1

section FPdimCatConsequences

variable {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [EnoughProjectives C]
    [HasCategoricalFPdim C] [h : HasFPdimInequality C]

end FPdimCatConsequences

section IntegralTensorCategories

open TensorCategories

/-- `C` admits a quasi-fiber functor to `ModuleCat k`. -/
def HasQuasiFiberFunctor (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] : Prop :=
  Nonempty (QuasiFiberFunctor k C)

open scoped TensorProduct

/-- Two finite-dimensional quasi-Hopf algebras `H₁` and `H₂` over `k` are twist-isomorphic
if there exists an algebra isomorphism `φ : H₁ ≃ₐ[k] H₂` together with an invertible
twist `J ∈ (H₂ ⊗ H₂)ˣ` intertwining the counits and conjugating the comultiplications. -/
def QuasiHopfTwistIsoEquiv
    (k : Type u) [Field k]
    (H₁ : Type u) [Ring H₁] [Algebra k H₁] [QuasiHopfAlgebra k H₁]
    (H₂ : Type u) [Ring H₂] [Algebra k H₂] [QuasiHopfAlgebra k H₂] : Prop :=
  ∃ (φ : H₁ ≃ₐ[k] H₂) (J : (H₂ ⊗[k] H₂)ˣ),

    (∀ x : H₂,
      QuasiBialgebra.counit (R := k) (H := H₂) x =
      QuasiBialgebra.counit (R := k) (H := H₁) (φ.symm x)) ∧

    (∀ x : H₂,
      (QuasiBialgebra.comul (R := k) (H := H₂)) x =
      (↑J⁻¹ : H₂ ⊗[k] H₂) *
      (Algebra.TensorProduct.map (φ : H₁ →ₐ[k] H₂) (φ : H₁ →ₐ[k] H₂))
        ((QuasiBialgebra.comul (R := k) (H := H₁)) (φ.symm x)) *
      (↑J : H₂ ⊗[k] H₂))

end IntegralTensorCategories

section QuasiTensorFPdim

end QuasiTensorFPdim

section FPdimCategoryAlgInt

end FPdimCategoryAlgInt

section FGModuleCatInstance

universe u_fgm

variable (K : Type u_fgm) [Field K]

/-- Every finite-dimensional `K`-module is a projective object in `FGModuleCat K`, by
transferring projectivity from `ModuleCat K` along the forgetful functor. -/
noncomputable instance fgModuleCat_projective (V : FGModuleCat.{u_fgm} K) :
    Projective V := by
  constructor
  intro E X f e he
  set F := forget₂ (FGModuleCat K) (ModuleCat K)
  haveI : Projective (F.obj V) := inferInstance
  haveI : Epi (F.map e) := Functor.map_epi F e
  obtain ⟨g, hg⟩ := Projective.factors (F.map f) (F.map e)
  haveI : F.Full := inferInstance
  obtain ⟨g', rfl⟩ := F.map_surjective g
  refine ⟨g', ?_⟩
  haveI : F.Faithful := inferInstance
  exact F.map_injective (by rw [F.map_comp, hg])

/-- The category `FGModuleCat K` has enough projectives: every object is itself projective,
so it serves as its own projective presentation via the identity morphism. -/
noncomputable instance fgModuleCat_enoughProjectives :
    EnoughProjectives (FGModuleCat.{u_fgm} K) where
  presentation V := ⟨{
    p := V
    f := 𝟙 V
  }⟩

/-- The category `FGModuleCat K` of finite-dimensional `K`-vector spaces is the prototypical
example of a finite tensor category over `K`. -/
noncomputable instance instFiniteTensorCategoryFGModuleCat :
    FiniteTensorCategory K (FGModuleCat.{u_fgm} K) where
  enoughProj := inferInstance
  homFiniteDim _ _ := inferInstance

end FGModuleCatInstance

end CategoryTheory
