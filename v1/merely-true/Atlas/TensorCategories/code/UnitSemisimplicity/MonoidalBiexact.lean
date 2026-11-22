/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.RingTheory.Idempotents
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u w

noncomputable section

namespace TensorCategories

section EndUnitComm

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Endomorphisms of the unit object of a monoidal category commute (Proposition 1.2.7).
The proof uses coherence to identify the left and right unitors of the unit object. -/
theorem endUnit_comm (f g : 𝟙_ C ⟶ 𝟙_ C) : f ≫ g = g ≫ f := by
  have hom_eq : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by monoidal_coherence
  have inv_eq : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by monoidal_coherence
  have h1 : (ρ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (ρ_ (𝟙_ C)).hom = f ≫ g := by
    rw [rightUnitor_inv_comp_tensorHom_assoc, ← hom_eq, leftUnitor_naturality, hom_eq]; simp
  have h2 : (ρ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (ρ_ (𝟙_ C)).hom = g ≫ f := by
    rw [← inv_eq, leftUnitor_inv_comp_tensorHom_assoc, rightUnitor_naturality]; simp [inv_eq]
  rw [← h1, h2]

/-- The monoid `End(𝟙_ C)` of endomorphisms of the unit object of a monoidal category is
commutative, packaged as a `CommMonoid` instance (Proposition 1.2.7). -/
instance endUnit_commMonoid : CommMonoid (End (𝟙_ C)) where
  mul_comm f g := by
    show g ≫ f = f ≫ g
    exact (endUnit_comm f g).symm

end EndUnitComm

section EndUnitCommRing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]

/-- In a preadditive monoidal category, the endomorphism ring of the unit object is
commutative; this upgrades the ring structure on `End(𝟙_ C)` to a `CommRing`. -/
instance endUnit_commRing : CommRing (End (𝟙_ C)) :=
  { (inferInstance : Ring (End (𝟙_ C))) with
    mul_comm := fun f g => by
      show g ≫ f = f ≫ g
      exact (endUnit_comm f g).symm }

end EndUnitCommRing

section TensorNilpotent

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]

/-- If an endomorphism `f` of the unit object squares to zero under composition,
then its tensor square `f ⊗ₘ f` is the zero morphism. -/
theorem tensorHom_sq_of_sq_zero (f : 𝟙_ C ⟶ 𝟙_ C) (hf : f ≫ f = 0) :
    f ⊗ₘ f = 0 := by
  have hom_eq : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by monoidal_coherence
  have h1 : (ρ_ (𝟙_ C)).inv ≫ (f ⊗ₘ f) ≫ (ρ_ (𝟙_ C)).hom = f ≫ f := by
    rw [rightUnitor_inv_comp_tensorHom_assoc, ← hom_eq, leftUnitor_naturality, hom_eq]; simp
  rw [hf] at h1
  rw [← cancel_epi (ρ_ (𝟙_ C)).inv, ← cancel_mono (ρ_ (𝟙_ C)).hom]
  simp [h1]

end TensorNilpotent

/-- A monoidal abelian category is *monoidally biexact* if tensoring on either side
preserves monomorphisms and epimorphisms, and if `X ⊗ X` being zero forces `X` to be zero.
This abstracts Proposition 1.13.1 together with the nondegeneracy needed for the proof
that `End(𝟙)` is reduced. -/
class MonoidalBiexact (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Abelian C] : Prop where
  whiskerRight_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f] (Z : C), Mono (f ▷ Z)
  whiskerLeft_mono : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Mono f], Mono (Z ◁ f)
  whiskerRight_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f] (Z : C), Epi (f ▷ Z)
  whiskerLeft_epi : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Epi f], Epi (Z ◁ f)
  isZero_of_tensorObj_self_isZero : ∀ (X : C), IsZero (X ⊗ X) → IsZero X

section TensorNondegenProof

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C]

/-- Right tensoring by an object preserves zero morphisms in a monoidal preadditive
category, supplying the `PreservesZeroMorphisms` instance for `tensorRight`. -/
instance tensorRight_preservesZeroMorphisms (Y : C) :
    (tensorRight Y).PreservesZeroMorphisms where
  map_zero _ _ := MonoidalPreadditive.zero_whiskerRight

/-- Left tensoring by an object preserves zero morphisms in a monoidal preadditive
category, supplying the `PreservesZeroMorphisms` instance for `tensorLeft`. -/
instance tensorLeft_preservesZeroMorphisms (Y : C) :
    (tensorLeft Y).PreservesZeroMorphisms where
  map_zero _ _ := MonoidalPreadditive.whiskerLeft_zero

/-- In an abelian braided rigid monoidal category, if `X ⊗ X` is the zero object then
`X` itself is zero. The argument uses the zig-zag identity and duals to show that the
left unitor of `X` vanishes. -/
theorem isZero_of_tensorSelf_isZero (X : C) (h : IsZero (X ⊗ X)) : IsZero X := by

  have h1 : IsZero ((X ⊗ X) ⊗ HasRightDual.rightDual X) :=
    (tensorRight _).map_isZero h

  have h2 : IsZero (X ⊗ (X ⊗ HasRightDual.rightDual X)) :=
    h1.of_iso (α_ X X (HasRightDual.rightDual X)).symm


  have h3 : IsZero (X ⊗ (HasRightDual.rightDual X ⊗ X)) :=
    h2.of_iso ((tensorLeft X).mapIso (β_ (HasRightDual.rightDual X) X))

  have h4 : IsZero ((X ⊗ HasRightDual.rightDual X) ⊗ X) :=
    h3.of_iso (α_ X (HasRightDual.rightDual X) X)


  have hz : η_ X (HasRightDual.rightDual X) ▷ X = 0 :=
    h4.eq_of_tgt _ _


  have zigzag := ExactPairing.evaluation_coevaluation X (HasRightDual.rightDual X)

  rw [hz, zero_comp] at zigzag


  have hlam : (λ_ X).hom = 0 := by
    have : (λ_ X).hom = ((λ_ X).hom ≫ (ρ_ X).inv) ≫ (ρ_ X).hom := by simp
    rw [this, zigzag.symm, zero_comp]

  rw [IsZero.iff_id_eq_zero]
  calc 𝟙 X = (λ_ X).inv ≫ (λ_ X).hom := by simp
    _ = (λ_ X).inv ≫ 0 := by rw [hlam]
    _ = 0 := by simp

end TensorNondegenProof

/-- Any abelian rigid monoidal preadditive braided category is monoidally biexact.
The proof uses duality adjunctions to deduce that left/right tensoring preserves
monomorphisms and epimorphisms, and combines this with the nondegeneracy lemma above. -/
noncomputable instance monoidalBiexact_of_rigidCategory
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C] : MonoidalBiexact C where
  whiskerRight_mono := fun {X Y} f _inst Z => by
    have adj := tensorRightAdjunction (HasLeftDual.leftDual Z) Z
    haveI := adj.rightAdjoint_preservesLimits
    haveI : (tensorRight Z).PreservesMonomorphisms :=
      preservesMonomorphisms_of_preservesLimitsOfShape _
    exact (tensorRight Z).map_mono f
  whiskerLeft_mono := fun Z {X Y} f _inst => by
    have adj := tensorLeftAdjunction Z (HasRightDual.rightDual Z)
    haveI := adj.rightAdjoint_preservesLimits
    haveI : (tensorLeft Z).PreservesMonomorphisms :=
      preservesMonomorphisms_of_preservesLimitsOfShape _
    exact (tensorLeft Z).map_mono f
  whiskerRight_epi := fun {X Y} f _inst Z => by
    have adj := tensorRightAdjunction Z (HasRightDual.rightDual Z)
    haveI := adj.leftAdjoint_preservesColimits
    haveI : (tensorRight Z).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape _
    exact (tensorRight Z).map_epi f
  whiskerLeft_epi := fun Z {X Y} f _inst => by
    have adj := tensorLeftAdjunction (HasLeftDual.leftDual Z) Z
    haveI := adj.leftAdjoint_preservesColimits
    haveI : (tensorLeft Z).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape _
    exact (tensorLeft Z).map_epi f
  isZero_of_tensorObj_self_isZero := isZero_of_tensorSelf_isZero

section TensorBiexact

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalBiexact C]

/-- In a monoidally biexact abelian category, the tensor product of two monomorphisms
is a monomorphism. -/
lemma tensorHom_mono_of_mono {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [Mono f] [Mono g] : Mono (f ⊗ₘ g) := by
  have h : f ⊗ₘ g = f ▷ X₂ ≫ Y₁ ◁ g := MonoidalCategory.tensorHom_def f g
  rw [h]
  haveI : Mono (f ▷ X₂) := MonoidalBiexact.whiskerRight_mono f X₂
  haveI : Mono (Y₁ ◁ g) := MonoidalBiexact.whiskerLeft_mono Y₁ g
  exact mono_comp _ _

/-- In a monoidally biexact abelian category, the tensor product of two epimorphisms
is an epimorphism. -/
lemma tensorHom_epi_of_epi {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  have h : f ⊗ₘ g = f ▷ X₂ ≫ Y₁ ◁ g := MonoidalCategory.tensorHom_def f g
  rw [h]
  haveI : Epi (f ▷ X₂) := MonoidalBiexact.whiskerRight_epi f X₂
  haveI : Epi (Y₁ ◁ g) := MonoidalBiexact.whiskerLeft_epi Y₁ g
  exact epi_comp _ _

end TensorBiexact

/-- If an epi `e : A ⟶ B` followed by a mono `m : B ⟶ D` is the zero morphism, then
the intermediate object `B` is zero. -/
lemma isZero_of_epi_comp_mono_eq_zero {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : C} (e : A ⟶ B) (m : B ⟶ D)
    [Epi e] [Mono m] (h : e ≫ m = 0) : IsZero B := by
  have he : e = 0 := by rwa [← cancel_mono m, zero_comp]
  rw [IsZero.iff_id_eq_zero]
  exact (Preadditive.epi_iff_cancel_zero e).mp inferInstance B (𝟙 B) (by rw [he, zero_comp])

section TensorBiexactCont

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalBiexact C]

/-- In a monoidally biexact abelian category, if `f ⊗ₘ f = 0` for an endomorphism `f`
of the unit, then `f = 0`. The proof factors `f` through its abelian image and uses
biexactness to conclude the image is zero. -/
theorem tensorImage_zero_of_tensorHom_zero {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [MonoidalBiexact C]
    (f : 𝟙_ C ⟶ 𝟙_ C) (hf : f ⊗ₘ f = 0) : f = 0 := by

  have hfac : Abelian.factorThruImage f ≫ Abelian.image.ι f = f := Abelian.image.fac f

  have htensor : (Abelian.factorThruImage f ⊗ₘ Abelian.factorThruImage f) ≫
      (Abelian.image.ι f ⊗ₘ Abelian.image.ι f) = 0 := by
    rw [tensorHom_comp_tensorHom, hfac, hf]

  haveI : Epi (Abelian.factorThruImage f ⊗ₘ Abelian.factorThruImage f) :=
    tensorHom_epi_of_epi _ _
  haveI : Mono (Abelian.image.ι f ⊗ₘ Abelian.image.ι f) :=
    tensorHom_mono_of_mono _ _

  have hJJ : IsZero (Abelian.image f ⊗ Abelian.image f) :=
    isZero_of_epi_comp_mono_eq_zero _ _ htensor

  have hJ : IsZero (Abelian.image f) :=
    MonoidalBiexact.isZero_of_tensorObj_self_isZero _ hJJ

  rw [← hfac, hJ.eq_of_src (Abelian.image.ι f) 0, comp_zero]

end TensorBiexactCont

/-- A monoid-with-zero in which every square-zero element is zero is reduced
(has no nonzero nilpotent elements). The proof uses strong induction to reduce
nilpotency to the square-zero case. -/
lemma isReduced_of_sq_zero {R : Type*} [MonoidWithZero R]
    (h : ∀ x : R, x * x = 0 → x = 0) : IsReduced R := by
  apply IsReduced.mk
  intro x ⟨n, hn⟩
  suffices ∀ (m : ℕ) (y : R), y ^ m = 0 → y = 0 from this n x hn
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro y hym
    by_cases hm : m ≤ 1
    · interval_cases m
      · simp [pow_zero] at hym
        have : (0 : R) = 1 := hym.symm
        rw [show y = y * 1 from (mul_one y).symm, ← this, mul_zero]
      · simpa [pow_one] using hym
    · push Not at hm
      set k := (m + 1) / 2
      have hk_lt : k < m := by omega
      have hk_ge : m ≤ k + k := by omega
      have hsq : (y ^ k) * (y ^ k) = 0 := by
        rw [← pow_add]
        exact pow_eq_zero_of_le hk_ge hym
      exact ih k hk_lt y (h _ hsq)

/-- In a monoidally biexact abelian monoidal category, the endomorphism ring of the
unit object is reduced. -/
theorem endUnit_isReduced {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [Abelian C] [MonoidalBiexact C] : IsReduced (End (𝟙_ C)) := by
  apply isReduced_of_sq_zero
  intro f hf

  have hff : f ≫ f = 0 := hf

  have htensor : f ⊗ₘ f = 0 := tensorHom_sq_of_sq_zero f hff

  exact tensorImage_zero_of_tensorHom_zero f htensor

/-- Under the standing assumptions (monoidally biexact, Artinian endomorphism ring),
the commutative ring `End(𝟙_ C)` is semisimple. -/
theorem endUnit_isSemisimpleRing {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [inst_ab : Abelian C] [MonoidalBiexact C]
    [IsArtinianRing (End (𝟙_ C))] :
    IsSemisimpleRing (End (𝟙_ C)) :=
  @IsArtinianRing.isSemisimpleRing_of_isReduced (End (𝟙_ C))
    (@endUnit_commRing C _ _ inst_ab.toPreadditive)
    inferInstance endUnit_isReduced

/-- Theorem 1.15.1: in any multiring category, `End(𝟙)` is a semisimple algebra.
This formalization specializes to abelian monoidally biexact categories with an
Artinian endomorphism ring on the unit. -/
theorem Theorem_1_15_1_endUnit_semisimple {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [inst_ab : Abelian C] [MonoidalBiexact C]
    [IsArtinianRing (End (𝟙_ C))] :
    IsSemisimpleRing (End (𝟙_ C)) :=
  endUnit_isSemisimpleRing

end TensorCategories
