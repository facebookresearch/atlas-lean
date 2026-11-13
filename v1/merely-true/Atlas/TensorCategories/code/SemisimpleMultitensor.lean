/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Atlas.TensorCategories.code.PivotalSpherical

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

section Semisimple

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

def IsSemisimpleObject (X : C) : Prop :=
  ∃ (n : ℕ) (f : Fin n → C) (_ : HasBiproduct f),
    (∀ i, Simple (f i)) ∧ Nonempty (X ≅ @biproduct _ _ _ _ f ‹HasBiproduct f›)

class IsSemisimpleCategory : Prop where
  semisimple : ∀ (X : C), IsSemisimpleObject C X

variable {C}

theorem isSemisimpleObject_of_iso {X Y : C} (i : X ≅ Y) (h : IsSemisimpleObject C Y) :
    IsSemisimpleObject C X := by
  obtain ⟨n, f, hb, hsimp, ⟨iso⟩⟩ := h
  exact ⟨n, f, hb, hsimp, ⟨i ≪≫ iso⟩⟩

end Semisimple

section MultitensorDef

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

class IsMultitensorCategory : Type max u v extends RigidCategory C

class IsMultifusionCategory : Type max u v extends IsMultitensorCategory C where
  [isSemisimple : IsSemisimpleCategory C]

attribute [instance] IsMultifusionCategory.isSemisimple

end MultitensorDef

section UnitSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

theorem unit_isSemisimpleObject [IsSemisimpleCategory C] :
    IsSemisimpleObject C (𝟙_ C) :=
  IsSemisimpleCategory.semisimple (𝟙_ C)

end UnitSemisimple

lemma isZero_tensor_left {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] {A B : C} (h : IsZero A) :
    IsZero (A ⊗ B) := by
  rw [IsZero.iff_id_eq_zero]
  have hA : 𝟙 A = 0 := h.eq_of_src (𝟙 A) 0
  have : 𝟙 (A ⊗ B) = 𝟙 A ▷ B ≫ A ◁ 𝟙 B := by simp
  rw [this, hA]
  simp [MonoidalPreadditive.zero_whiskerRight]

lemma isZero_tensor_right {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] {A B : C} (h : IsZero B) :
    IsZero (A ⊗ B) := by
  rw [IsZero.iff_id_eq_zero]
  have hB : 𝟙 B = 0 := h.eq_of_src (𝟙 B) 0
  have : 𝟙 (A ⊗ B) = 𝟙 A ▷ B ≫ A ◁ 𝟙 B := by simp
  rw [this, hB]
  simp [MonoidalPreadditive.whiskerLeft_zero]

section ComponentSubcategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

omit [HasZeroMorphisms C] in
/-- The `(i, j)`-component object `f i ⊗ X ⊗ f j` formed by sandwiching `X` between two
chosen simple summands of the unit. -/
def componentObj {n : ℕ} (f : Fin n → C) (X : C) (i j : Fin n) : C :=
  f i ⊗ X ⊗ f j

omit [HasZeroMorphisms C] in
/-- The family of all `(i, j)`-component objects of `X`, indexed by pairs in `Fin n × Fin n`. -/
def componentFamily {n : ℕ} (f : Fin n → C) (X : C) : Fin n × Fin n → C :=
  fun p => componentObj f X p.1 p.2

/-- The property that an object lies in the `(i, j)`-component subcategory: it is isomorphic
to `f i ⊗ Y ⊗ f j` for some `Y`. -/
def IsInComponentSubcategory {n : ℕ} (f : Fin n → C) (i j : Fin n) :
    ObjectProperty C :=
  fun X => ∃ (Y : C), Nonempty (X ≅ f i ⊗ Y ⊗ f j)

/-- Definition 1.15.4: the component subcategory `C_{ij} = 𝟙_i ⊗ C ⊗ 𝟙_j` realised as a full
subcategory of `C`. -/
abbrev Definition_1_15_4_ComponentSubcategory {n : ℕ} (f : Fin n → C) (i j : Fin n) :=
  (IsInComponentSubcategory f i j).FullSubcategory

omit [HasZeroMorphisms C] in
/-- Coherence helper: the chain through the unitors and a whiskering collapses to the
composition `s ≫ r`. -/
lemma whisker_unitor_calc {A B : C} (s : A ⟶ 𝟙_ C) (r : 𝟙_ C ⟶ B) :
    (ρ_ A).inv ≫ A ◁ r ≫ s ▷ B ≫ (λ_ B).hom = s ≫ r := by
  slice_lhs 2 3 => rw [whisker_exchange s r]
  slice_lhs 1 2 => rw [← rightUnitor_inv_naturality]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 2 3 => rw [unitors_equal, Iso.inv_hom_id]
  simp

/-- If `𝟙_ C` decomposes as a sum of distinct simple summands `f i`, then the cross tensor
products `f i ⊗ f j` with `i ≠ j` are zero. -/
theorem unitComponent_tensor_zero {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    {i j : Fin n} (hij : i ≠ j) :
    IsZero (f i ⊗ f j) := by

  let r_i : 𝟙_ C ⟶ f i := hiso.hom ≫ biproduct.π f i
  let s_i : f i ⟶ 𝟙_ C := biproduct.ι f i ≫ hiso.inv
  let r_j : 𝟙_ C ⟶ f j := hiso.hom ≫ biproduct.π f j
  let s_j : f j ⟶ 𝟙_ C := biproduct.ι f j ≫ hiso.inv

  have s_r_i : s_i ≫ r_i = 𝟙 (f i) := by
    simp [s_i, r_i, Category.assoc, Iso.inv_hom_id_assoc]
  have s_r_j : s_j ≫ r_j = 𝟙 (f j) := by
    simp [s_j, r_j, Category.assoc, Iso.inv_hom_id_assoc]

  let ret : f i ⊗ f j ⟶ f j := s_i ▷ (f j) ≫ (λ_ (f j)).hom
  let sec : f j ⟶ f i ⊗ f j := (λ_ (f j)).inv ≫ r_i ▷ (f j)

  let ret' : f i ⊗ f j ⟶ f i := (f i) ◁ s_j ≫ (ρ_ (f i)).hom
  let sec' : f i ⟶ f i ⊗ f j := (ρ_ (f i)).inv ≫ (f i) ◁ r_j

  have retract_id : ret ≫ sec = 𝟙 (f i ⊗ f j) := by
    simp only [ret, sec, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.comp_whiskerRight, s_r_i, MonoidalCategory.id_whiskerRight]

  have retract_id' : ret' ≫ sec' = 𝟙 (f i ⊗ f j) := by
    simp only [ret', sec', Category.assoc, Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp, s_r_j, MonoidalCategory.whiskerLeft_id]

  have ret_mono : Mono ret := (SplitMono.mk sec retract_id).mono

  have h_sec'_ret_zero : sec' ≫ ret = 0 := by
    simp only [sec', ret, Category.assoc]
    rw [whisker_unitor_calc s_i r_j]
    simp only [s_i, r_j, Category.assoc, Iso.inv_hom_id_assoc]
    exact biproduct.ι_π_ne (f := f) hij

  rw [IsZero.iff_id_eq_zero]
  by_cases h_ret : IsIso ret
  ·
    have hsec'_zero : sec' = 0 := by rw [← cancel_mono ret]; simp [h_sec'_ret_zero]
    calc 𝟙 (f i ⊗ f j) = ret' ≫ sec' := retract_id'.symm
      _ = ret' ≫ 0 := by rw [hsec'_zero]
      _ = 0 := by simp
  ·
    have hret_zero : ret = 0 := by
      rwa [Simple.mono_isIso_iff_nonzero ret, not_not] at h_ret
    calc 𝟙 (f i ⊗ f j) = ret ≫ sec := retract_id.symm
      _ = 0 ≫ sec := by rw [hret_zero]
      _ = 0 := by simp

/-- When `𝟙_ C` decomposes as a sum of distinct simple summands `f i`, each diagonal
component `f i ⊗ f i` is canonically isomorphic to `f i`. -/
def component_diagonal_unit_iso {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (i : Fin n) :
    f i ⊗ f i ≅ f i := by
  haveI : Simple (f i) := hsimp i

  let r_i : 𝟙_ C ⟶ f i := hiso.hom ≫ biproduct.π f i
  let s_i : f i ⟶ 𝟙_ C := biproduct.ι f i ≫ hiso.inv

  have s_r_i : s_i ≫ r_i = 𝟙 (f i) := by
    simp [s_i, r_i, Category.assoc, Iso.inv_hom_id_assoc]

  let ret : f i ⊗ f i ⟶ f i := s_i ▷ (f i) ≫ (λ_ (f i)).hom
  let sec : f i ⟶ f i ⊗ f i := (λ_ (f i)).inv ≫ r_i ▷ (f i)

  have retract_id : ret ≫ sec = 𝟙 (f i ⊗ f i) := by
    simp only [ret, sec, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.comp_whiskerRight, s_r_i, MonoidalCategory.id_whiskerRight]

  let sec' : f i ⟶ f i ⊗ f i := (ρ_ (f i)).inv ≫ (f i) ◁ r_i

  have cross_id : sec' ≫ ret = 𝟙 (f i) := by
    simp only [sec', ret, Category.assoc]
    rw [whisker_unitor_calc s_i r_i]
    exact s_r_i

  have ret_mono : Mono ret := (SplitMono.mk sec retract_id).mono

  have ret_nonzero : ret ≠ 0 := by
    intro h
    have : 𝟙 (f i) = 0 := by rw [← cross_id, h, Limits.comp_zero]
    exact id_nonzero (f i) this

  have ret_iso : IsIso ret := (Simple.mono_isIso_iff_nonzero ret).mpr ret_nonzero
  exact asIso ret


/-- Proposition 1.15.5 (2): tensor products between component subcategories vanish off the
diagonal — `C_{ij} ⊗ C_{kl} = 0` unless `j = k`. -/
theorem tensor_component_zero
    [Preadditive C] [MonoidalPreadditive C]
    {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (X Y : C) (i j k l : Fin n) (hjk : j ≠ k) :
    IsZero (componentObj f X i j ⊗ componentObj f Y k l) := by
  unfold componentObj


  have iso : (f i ⊗ (X ⊗ f j)) ⊗ (f k ⊗ (Y ⊗ f l)) ≅
      (f i ⊗ X) ⊗ ((f j ⊗ f k) ⊗ (Y ⊗ f l)) :=
    (whiskerRightIso (α_ (f i) X (f j)).symm (f k ⊗ (Y ⊗ f l))) ≪≫
    (α_ (f i ⊗ X) (f j) (f k ⊗ (Y ⊗ f l))) ≪≫
    (whiskerLeftIso (f i ⊗ X) (α_ (f j) (f k) (Y ⊗ f l)).symm)

  have hzero : IsZero (f j ⊗ f k) := unitComponent_tensor_zero f hiso hsimp hjk

  exact (isZero_tensor_right (isZero_tensor_left hzero)).of_iso iso

/-- Proposition 1.15.5 (2): on the diagonal `j = k`, the tensor product `C_{ij} ⊗ C_{jl}`
lands in `C_{il}`, exhibited via an explicit isomorphism. -/
noncomputable def tensor_component_compatible {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (X Y : C) (i j l : Fin n) :
    componentObj f X i j ⊗ componentObj f Y j l ≅ componentObj f ((X ⊗ f j) ⊗ Y) i l := by
  unfold componentObj


  exact
    (α_ (f i) (X ⊗ f j) (f j ⊗ (Y ⊗ f l))) ≪≫
    whiskerLeftIso (f i) (
      (α_ (X ⊗ f j) (f j) (Y ⊗ f l)).symm ≪≫
      whiskerRightIso (
        (α_ X (f j) (f j)) ≪≫
        whiskerLeftIso X (component_diagonal_unit_iso f hiso hsimp j)
      ) (Y ⊗ f l) ≪≫
      (α_ (X ⊗ f j) Y (f l)).symm
    )

section RigidDuals

variable [RigidCategory C]

/-- The right adjoint mate of any endomorphism of the unit `𝟙_ C` equals the endomorphism itself,
since the unit is canonically self-dual in a rigid category. -/
theorem rightAdjointMate_unit_endo (g : 𝟙_ C ⟶ 𝟙_ C) :
    rightAdjointMate g = g := by
  show (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C) ◁ (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C) ◁ g ▷ (𝟙_ C) ≫
    (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv ≫ (ρ_ (𝟙_ C)).hom ▷ (𝟙_ C) ≫ (λ_ (𝟙_ C)).hom = g
  calc _ = 𝟙 _ ⊗≫ (𝟙_ C) ◁ g ▷ (𝟙_ C) ⊗≫ 𝟙 _ := by monoidal
       _ = g := by monoidal

/-- Each simple summand `f i` of a decomposition of the unit is canonically isomorphic to its own
right dual, via the mates of the structural inclusion and projection maps. -/
def unitComponent_selfDual {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (i : Fin n) :
    f i ≅ (f i)ᘁ := by
  set s : f i ⟶ 𝟙_ C := biproduct.ι f i ≫ hiso.inv
  set r : 𝟙_ C ⟶ f i := hiso.hom ≫ biproduct.π f i
  have h_sr : s ≫ r = 𝟙 (f i) := by
    simp [s, r, Category.assoc, Iso.inv_hom_id_assoc]
  have h_rs_mate_eq : rightAdjointMate s ≫ rightAdjointMate r = r ≫ s := by
    rw [← comp_rightAdjointMate]
    exact rightAdjointMate_unit_endo (r ≫ s)
  have h_rs_mate_id : rightAdjointMate r ≫ rightAdjointMate s = 𝟙 (f i)ᘁ := by
    rw [← comp_rightAdjointMate, h_sr, rightAdjointMate_id]
  refine ⟨s ≫ rightAdjointMate s, rightAdjointMate r ≫ r, ?_, ?_⟩
  ·
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [h_rs_mate_eq]
    simp only [Category.assoc, r, s, Iso.inv_hom_id_assoc, biproduct.ι_π_self, Category.comp_id]
  ·
    rw [Category.assoc, ← Category.assoc r s _, h_rs_mate_eq.symm, Category.assoc,
        ← Category.assoc (rightAdjointMate r) (rightAdjointMate s) _, h_rs_mate_id, Category.id_comp]

/-- The right dual of a tensor product is canonically isomorphic to the reversed tensor product of
right duals, `(A ⊗ B)ᘁ ≅ Bᘁ ⊗ Aᘁ`, constructed via uniqueness of right adjoints. -/
def rightDualTensorIso (A B : C) : (A ⊗ B)ᘁ ≅ (Bᘁ : C) ⊗ (Aᘁ : C) := by
  have adj1 := tensorRightAdjunction (A ⊗ B) ((A ⊗ B)ᘁ)
  have comp_adj := (tensorRightAdjunction A (Aᘁ : C)).comp (tensorRightAdjunction B (Bᘁ : C))
  have assoc1 : tensorRight A ⋙ tensorRight B ≅ tensorRight (A ⊗ B) :=
    NatIso.ofComponents (fun X => (α_ X A B)) (by intros; simp [tensorRight])
  have assoc2 : tensorRight (Bᘁ : C) ⋙ tensorRight (Aᘁ : C) ≅
      tensorRight ((Bᘁ : C) ⊗ (Aᘁ : C)) :=
    NatIso.ofComponents (fun X => (α_ X Bᘁ Aᘁ)) (by intros; simp [tensorRight])
  have adj2 := (comp_adj.ofNatIsoLeft assoc1).ofNatIsoRight assoc2
  exact (λ_ ((A ⊗ B)ᘁ)).symm ≪≫
    (Adjunction.rightAdjointUniq adj1 adj2).app (𝟙_ C) ≪≫
    (λ_ ((Bᘁ : C) ⊗ (Aᘁ : C)))

/-- The left dual of a tensor product is canonically isomorphic to the reversed tensor product of
left duals, `ᘁ(A ⊗ B) ≅ ᘁB ⊗ ᘁA`, constructed via uniqueness of right adjoints. -/
def leftDualTensorIso (A B : C) : (ᘁ(A ⊗ B) : C) ≅ (ᘁB : C) ⊗ (ᘁA : C) := by
  have adj1 := tensorLeftAdjunction (ᘁ(A ⊗ B) : C) (A ⊗ B)
  have comp_adj := (tensorLeftAdjunction (ᘁB : C) B).comp
    (tensorLeftAdjunction (ᘁA : C) A)
  have assoc1 : tensorLeft B ⋙ tensorLeft A ≅ tensorLeft (A ⊗ B) :=
    NatIso.ofComponents (fun Z => (α_ A B Z).symm) (by intros; simp [tensorLeft])
  have assoc2 : tensorLeft (ᘁA : C) ⋙ tensorLeft (ᘁB : C) ≅
      tensorLeft ((ᘁB : C) ⊗ (ᘁA : C)) :=
    NatIso.ofComponents (fun Z => (α_ (ᘁB : C) (ᘁA : C) Z).symm)
      (by intros; simp [tensorLeft])
  have adj2 := (comp_adj.ofNatIsoLeft assoc1).ofNatIsoRight assoc2
  exact (ρ_ (ᘁ(A ⊗ B) : C)).symm ≪≫
    (Adjunction.rightAdjointUniq adj1 adj2).app (𝟙_ C) ≪≫
    (ρ_ ((ᘁB : C) ⊗ (ᘁA : C)))

/-- Given a self-duality isomorphism `V ≅ Vᘁ`, transport it through left adjoint mates to
produce an isomorphism `ᘁV ≅ V`. -/
def leftDualSelfDual {V : C} (selfDual : V ≅ Vᘁ) : (ᘁV : C) ≅ V where
  hom := ᘁ(selfDual.inv)
  inv := ᘁ(selfDual.hom)
  hom_inv_id := by rw [← comp_leftAdjointMate]; simp
  inv_hom_id := by rw [← comp_leftAdjointMate]; simp

/-- The right dual of an `(i, j)`-component object `f i ⊗ X ⊗ f j` is identified with the
`(j, i)`-component object on the dual `Xᘁ`, swapping the indices. -/
def rightDual_component {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (X : C) (i j : Fin n) :
    (componentObj f X i j)ᘁ ≅ componentObj f (Xᘁ) j i := by
  unfold componentObj
  exact rightDualTensorIso (f i) (X ⊗ f j) ≪≫
    tensorIso (rightDualTensorIso X (f j)) (Iso.refl _) ≪≫
    (α_ (f j)ᘁ (Xᘁ : C) (f i)ᘁ) ≪≫
    tensorIso (unitComponent_selfDual f hiso hsimp j).symm
              (tensorIso (Iso.refl (Xᘁ : C)) (unitComponent_selfDual f hiso hsimp i).symm)

/-- The left dual of an `(i, j)`-component object `f i ⊗ X ⊗ f j` is identified with the
`(j, i)`-component object on the left dual `ᘁX`, swapping the indices. -/
def leftDual_component {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (X : C) (i j : Fin n) :
    (ᘁ(componentObj f X i j) : C) ≅ componentObj f (ᘁX : C) j i := by
  unfold componentObj
  exact leftDualTensorIso (f i) (X ⊗ f j) ≪≫
    tensorIso (leftDualTensorIso X (f j)) (Iso.refl _) ≪≫
    (α_ (ᘁ(f j) : C) (ᘁX : C) (ᘁ(f i) : C)) ≪≫
    tensorIso (leftDualSelfDual (unitComponent_selfDual f hiso hsimp j))
              (tensorIso (Iso.refl (ᘁX : C)) (leftDualSelfDual (unitComponent_selfDual f hiso hsimp i)))

end RigidDuals

end ComponentSubcategories

section ObjectDecomposition

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- Canonical isomorphism flattening a double biproduct over `Fin n × Fin n` into a single biproduct
indexed by the product type. -/
def biproductFlattenIso {n : ℕ} (g : Fin n → Fin n → C) :
    (⨁ fun i => ⨁ fun j => g i j) ≅ (⨁ fun p : Fin n × Fin n => g p.1 p.2) where
  hom := biproduct.desc fun i => biproduct.desc fun j =>
    biproduct.ι (fun p : Fin n × Fin n => g p.1 p.2) ⟨i, j⟩
  inv := biproduct.desc fun (p : Fin n × Fin n) =>
    biproduct.ι (fun j => g p.1 j) p.2 ≫ biproduct.ι (fun i => ⨁ fun j => g i j) p.1
  hom_inv_id := by ext i j; simp
  inv_hom_id := by ext ⟨i, j⟩; simp

/-- Every object `X` decomposes as a biproduct of its `(i, j)`-component objects
`f i ⊗ X ⊗ f j`, where `f` is the chosen decomposition of the unit into simple summands. -/
theorem object_componentDecomposition {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (X : C) :
    ∃ (_ : HasBiproduct (componentFamily f X)),
      Nonempty (X ≅ ⨁ (componentFamily f X)) := by
  refine ⟨inferInstance, ⟨?_⟩⟩

  have step1 : X ≅ (⨁ f) ⊗ (X ⊗ ⨁ f) :=
    (λ_ X).symm ≪≫ tensorIso (Iso.refl (𝟙_ C)) (ρ_ X).symm ≪≫
    tensorIso hiso (tensorIso (Iso.refl X) hiso)

  have step2 : (⨁ f) ⊗ (X ⊗ ⨁ f) ≅ ⨁ (fun i => f i ⊗ (X ⊗ ⨁ f)) :=
    rightDistributor f (X ⊗ ⨁ f)

  have step3 : (⨁ fun i => f i ⊗ (X ⊗ ⨁ f)) ≅ (⨁ fun i => ⨁ fun j => f i ⊗ (X ⊗ f j)) :=
    biproduct.mapIso fun i =>
      tensorIso (Iso.refl (f i)) (leftDistributor X f) ≪≫
      leftDistributor (f i) (fun j => X ⊗ f j)

  have step4 : (⨁ fun i => ⨁ fun j => f i ⊗ (X ⊗ f j)) ≅ ⨁ componentFamily f X :=
    biproductFlattenIso (fun i j => f i ⊗ (X ⊗ f j))
  exact step1 ≪≫ step2 ≪≫ step3 ≪≫ step4

end ObjectDecomposition

section DualityAux

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- Functoriality of right duals on isomorphisms: an iso `V ≅ W` gives `Wᘁ ≅ Vᘁ` via right adjoint
mates. -/
def rightDualIsoOfIso {V W : C} (i : V ≅ W) : Wᘁ ≅ Vᘁ where
  hom := (i.hom)ᘁ
  inv := (i.inv)ᘁ
  hom_inv_id := by rw [← comp_rightAdjointMate]; simp
  inv_hom_id := by rw [← comp_rightAdjointMate]; simp

/-- Functoriality of left duals on isomorphisms: an iso `V ≅ W` gives `ᘁW ≅ ᘁV` via left adjoint
mates. -/
def leftDualIsoOfIso {V W : C} (i : V ≅ W) :
    (ᘁW : C) ≅ (ᘁV : C) where
  hom := ᘁ(i.hom)
  inv := ᘁ(i.inv)
  hom_inv_id := by rw [← comp_leftAdjointMate]; simp
  inv_hom_id := by rw [← comp_leftAdjointMate]; simp

/-- Any object is isomorphic to the right dual of its own left dual, `V ≅ (ᘁV)ᘁ`, via the
uniqueness of right duals on the rigid pairings. -/
def isoRightDualOfLeftDual (V : C) : V ≅ (ᘁV : C)ᘁ :=
  rightDualIso (HasLeftDual.exact (Y := V)) (HasRightDual.exact (X := (ᘁV : C)))

end DualityAux

section CompatibleDuals

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- In a braided rigid category the right dual `Vᘁ` also forms an exact pairing with `V` on the
other side, obtained by transporting the canonical pairing through the braiding. -/
@[reducible]
def exactPairing_rightDual_of_braided [BraidedCategory C] (V : C) :
    ExactPairing (Vᘁ) V :=
  @BraidedCategory.exactPairing_swap C _ _ _ V Vᘁ HasRightDual.exact

/-- Given a compatible exact pairing `ExactPairing Vᘁ V`, the left and right duals of `V` are
canonically isomorphic, `ᘁV ≅ Vᘁ`. -/
def leftDualIsoRightDual_of_compatibleDuals (V : C) (ep : ExactPairing (Vᘁ) V) : (ᘁV : C) ≅ Vᘁ :=

  leftDualIso HasLeftDual.exact ep

/-- Given a compatible exact pairing `ExactPairing Vᘁ V`, the object `V` is canonically isomorphic
to its double right dual `(Vᘁ)ᘁ`. -/
def doubleDualIso (V : C) (ep : ExactPairing (Vᘁ) V) : V ≅ (Vᘁ)ᘁ :=
  rightDualIso ep HasRightDual.exact

end CompatibleDuals

section TransportExactPairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Transport an exact pairing `ExactPairing X Y` along an isomorphism `X ≅ X'` of the left
component to obtain an exact pairing `ExactPairing X' Y`. -/
@[reducible] noncomputable def ExactPairing.ofIsoLeft {X X' Y : C}
    (ep : ExactPairing X Y) (f : X ≅ X') : ExactPairing X' Y where
  coevaluation' := η_ X Y ≫ (f.hom ▷ Y)
  evaluation' := (Y ◁ f.inv) ≫ ε_ X Y
  coevaluation_evaluation' := by
    rw [whiskerLeft_comp, comp_whiskerRight]
    simp only [Category.assoc]
    rw [associator_inv_naturality_middle_assoc Y f.hom Y]
    rw [← comp_whiskerRight_assoc (Y ◁ f.hom) (Y ◁ f.inv) Y,
        ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, id_whiskerRight,
        Category.id_comp]
    exact ep.coevaluation_evaluation'
  evaluation_coevaluation' := by
    rw [comp_whiskerRight, whiskerLeft_comp]
    simp only [Category.assoc]
    rw [associator_naturality_left_assoc]
    rw [← whisker_exchange_assoc f.hom (Y ◁ f.inv)]
    rw [← whisker_exchange f.hom (ε_ X Y)]
    rw [← associator_naturality_right_assoc X Y f.inv]
    rw [← whisker_exchange_assoc (η_ X Y) f.inv]
    change (𝟙_ C) ◁ f.inv ≫ ep.coevaluation' ▷ X ≫ (α_ X Y X).hom ≫
      X ◁ ep.evaluation' ≫ f.hom ▷ (𝟙_ C) = _
    rw [reassoc_of% ep.evaluation_coevaluation']
    rw [leftUnitor_naturality_assoc, ← rightUnitor_inv_naturality]
    simp [Iso.inv_hom_id_assoc]

end TransportExactPairing

section Prop_1_41_1_Semisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]






end Prop_1_41_1_Semisimple

section TraceNonzero

universe w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]




/-- Auxiliary helper: in a preadditive abelian category, the cokernel projection of any split
monomorphism is itself a split epimorphism, with explicit splitting via `𝟙 Y - retraction ≫ f`. -/
lemma isSplitEpi_cokernel_π_of_isSplitMono_aux
    [Preadditive C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] :
    IsSplitEpi (Limits.cokernel.π f) := by
  obtain ⟨⟨retraction, hretraction⟩⟩ := hf.exists_splitMono
  have hcomp : f ≫ (𝟙 Y - retraction ≫ f) = 0 := by
    simp [reassoc_of% hretraction]
  constructor
  refine ⟨⟨Limits.cokernel.desc f (𝟙 Y - retraction ≫ f) hcomp, ?_⟩⟩
  rw [← cancel_epi (Limits.cokernel.π f)]
  simp only [Limits.cokernel.π_desc_assoc, Category.comp_id]
  simp [Limits.cokernel.condition]


/-- The coevaluation `η_ V Vᘁ` is nonzero for a simple object `V` in a preadditive monoidal
category: otherwise the rigidity triangle would force `𝟙 V = 0`, contradicting simplicity. -/
lemma coevaluation_ne_zero_of_simple
    [Preadditive C] [MonoidalPreadditive C]
    {V : C} [Simple V] : η_ V (Vᘁ) ≠ 0 := by
  intro h_zero
  have h_triangle := ExactPairing.evaluation_coevaluation' (X := V) (Y := Vᘁ)
  change ExactPairing.coevaluation' = (0 : 𝟙_ C ⟶ V ⊗ Vᘁ) at h_zero
  rw [h_zero, MonoidalPreadditive.zero_whiskerRight] at h_triangle
  simp at h_triangle
  apply id_nonzero V
  have h_lam_zero : (λ_ V).hom = 0 := by
    rw [← cancel_mono (ρ_ V).inv, Limits.zero_comp]; exact h_triangle.symm
  calc 𝟙 V = (λ_ V).inv ≫ (λ_ V).hom := by simp
    _ = (λ_ V).inv ≫ 0 := by rw [h_lam_zero]
    _ = 0 := by simp

/-- The evaluation `ε_ Vᘁ (Vᘁ)ᘁ` is nonzero for a simple object `V`: a vanishing evaluation would
force `𝟙 Vᘁ = 0` and in turn `η_ V Vᘁ = 0`, contradicting `coevaluation_ne_zero_of_simple`. -/
lemma evaluation_ne_zero_of_simple
    [Preadditive C] [MonoidalPreadditive C]
    {V : C} [Simple V] : ε_ (Vᘁ) ((Vᘁ)ᘁ) ≠ 0 := by
  intro h_eps_zero
  have h_triangle := ExactPairing.evaluation_coevaluation' (X := Vᘁ) (Y := (Vᘁ)ᘁ)
  change ExactPairing.evaluation' = (0 : (Vᘁ)ᘁ ⊗ Vᘁ ⟶ 𝟙_ C) at h_eps_zero
  rw [h_eps_zero, MonoidalPreadditive.whiskerLeft_zero] at h_triangle
  simp at h_triangle
  have h_lam_zero : (λ_ (Vᘁ)).hom = 0 := by
    rw [← cancel_mono (ρ_ (Vᘁ)).inv, Limits.zero_comp]; exact h_triangle.symm
  have h_id_Vd_zero : 𝟙 (Vᘁ) = 0 := by
    calc 𝟙 (Vᘁ) = (λ_ (Vᘁ)).inv ≫ (λ_ (Vᘁ)).hom := by simp
      _ = (λ_ (Vᘁ)).inv ≫ 0 := by rw [h_lam_zero]
      _ = 0 := by simp
  have h_eta_zero : η_ V (Vᘁ) = 0 := by
    calc η_ V (Vᘁ) = η_ V (Vᘁ) ≫ 𝟙 (V ⊗ Vᘁ) := by simp
      _ = η_ V (Vᘁ) ≫ (V ◁ 𝟙 (Vᘁ)) := by rw [whiskerLeft_id]
      _ = η_ V (Vᘁ) ≫ (V ◁ (0 : Vᘁ ⟶ Vᘁ)) := by rw [h_id_Vd_zero]
      _ = η_ V (Vᘁ) ≫ 0 := by rw [MonoidalPreadditive.whiskerLeft_zero]
      _ = 0 := by simp
  exact coevaluation_ne_zero_of_simple h_eta_zero




end TraceNonzero

section Corollary_1_15_9

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Corollary 1.15.9 form: the evaluation `ε_ X Xᘁ` is nonzero for any nonzero object `X` in a
preadditive right-rigid monoidal category. -/
lemma evaluation_ne_zero_of_nonzero_obj
    [Preadditive C] [RightRigidCategory C]
    [MonoidalPreadditive C] (X : C) (hX : ¬ IsZero X) : ε_ X Xᘁ ≠ 0 := by
  intro h
  apply hX; rw [IsZero.iff_id_eq_zero]
  have zig := ExactPairing.evaluation_coevaluation X Xᘁ
  rw [h] at zig
  simp [MonoidalPreadditive.whiskerLeft_zero] at zig
  have hlam : (λ_ X).hom = 0 := by rw [← cancel_mono (ρ_ X).inv]; simp [zig]
  calc 𝟙 X = (λ_ X).inv ≫ (λ_ X).hom := by simp
    _ = (λ_ X).inv ≫ 0 := by rw [hlam]
    _ = 0 := by simp

/-- Corollary 1.15.9 form: the coevaluation `η_ X Xᘁ` is nonzero for any nonzero object `X` in a
preadditive right-rigid monoidal category. -/
lemma coevaluation_ne_zero_of_nonzero_obj
    [Preadditive C] [RightRigidCategory C]
    [MonoidalPreadditive C] (X : C) (hX : ¬ IsZero X) : η_ X Xᘁ ≠ 0 := by
  intro h
  apply hX; rw [IsZero.iff_id_eq_zero]
  have zig := ExactPairing.evaluation_coevaluation X Xᘁ
  rw [h] at zig
  simp [MonoidalPreadditive.zero_whiskerRight] at zig
  have hlam : (λ_ X).hom = 0 := by rw [← cancel_mono (ρ_ X).inv]; simp [zig]
  calc 𝟙 X = (λ_ X).inv ≫ (λ_ X).hom := by simp
    _ = (λ_ X).inv ≫ 0 := by rw [hlam]
    _ = 0 := by simp

end Corollary_1_15_9

end CategoryTheory
