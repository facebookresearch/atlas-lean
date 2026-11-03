/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact
import Atlas.TensorCategories.code.FittingLemmaInstance
import Mathlib.Algebra.Group.Pi.Units

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u w

noncomputable section

namespace TensorCategories

/-- If `X` is a nonzero object of a right-rigid preadditive monoidal category, the
coevaluation morphism `η_ X Xᘁ : 𝟙_ C ⟶ X ⊗ Xᘁ` is nonzero. -/
lemma coevaluation_ne_zero_of_nonzero_obj {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Preadditive C] [RightRigidCategory C]
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

/-- A nonzero epimorphism out of a simple object in an abelian category is an
isomorphism, since its kernel is either zero or all of `X`. -/
lemma isIso_of_epi_of_simple_src {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} [Simple X] (f : X ⟶ Y) [Epi f] (hf : f ≠ 0) : IsIso f := by
  suffices Mono f from isIso_of_mono_of_epi f
  by_contra hmono
  have hne_ker : kernel.ι f ≠ 0 := by
    intro h; apply hmono; constructor
    intro Z g₁ g₂ hfg
    have hsub : (g₁ - g₂) ≫ f = 0 := by simp [hfg]
    have : g₁ - g₂ = 0 := by rw [(kernel.lift_ι f _ hsub).symm, h, comp_zero]
    exact sub_eq_zero.mp this
  haveI : IsIso (kernel.ι f) := (Simple.mono_isIso_iff_nonzero (kernel.ι f)).mpr hne_ker
  exact hf (by
    have : 𝟙 X ≫ f = 0 := by
      rw [show (𝟙 X : X ⟶ X) = inv (kernel.ι f) ≫ kernel.ι f from by simp]
      rw [assoc, kernel.condition, comp_zero]
    simpa using this)

/-- In a rigid abelian monoidal preadditive category, if `f : X ⟶ 𝟙_ C` is a
monomorphism then its right adjoint mate `Xᘁ ⟶ 𝟙_ C` is an epimorphism. -/
theorem rightAdjointMate_epi_of_mono {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [RightRigidCategory C] [LeftRigidCategory C]
    [MonoidalPreadditive C]
    {X : C} (f : X ⟶ 𝟙_ C) [Mono f] : Epi (rightAdjointMate f) := by
  constructor
  intro T g₁ g₂ h


  have adj : tensorRight (ᘁT) ⊣ tensorRight T := tensorRightAdjunction (ᘁT) T
  haveI : PreservesLimitsOfSize.{0, 0} (tensorRight T) := adj.rightAdjoint_preservesLimits
  haveI : (tensorRight T).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  haveI : Mono (f ▷ T) := (tensorRight T).map_mono f


  have key : η_ X Xᘁ ≫ (X ◁ g₁ ≫ f ▷ T) = η_ X Xᘁ ≫ (X ◁ g₂ ≫ f ▷ T) := by
    simp only [whisker_exchange]
    simp only [← assoc]
    rw [← coevaluation_comp_rightAdjointMate f]
    simp only [assoc, ← MonoidalCategory.whiskerLeft_comp]
    rw [h]

  have step3 : η_ X Xᘁ ≫ X ◁ g₁ = η_ X Xᘁ ≫ X ◁ g₂ :=
    (cancel_mono (f ▷ T)).mp (by simp only [assoc]; exact key)

  have step4 : (ρ_ Xᘁ).hom ≫ g₁ = (ρ_ Xᘁ).hom ≫ g₂ := by
    apply_fun (tensorLeftHomEquiv (𝟙_ C) X Xᘁ T)
    simp only [tensorLeftHomEquiv_naturality]
    have : (tensorLeftHomEquiv (𝟙_ C) X Xᘁ Xᘁ) (ρ_ Xᘁ).hom = η_ X Xᘁ := by
      simp [tensorLeftHomEquiv, unitors_equal.symm]
    rw [this]
    exact step3

  exact (cancel_epi (ρ_ Xᘁ).hom).mp step4

/-- Left whiskering by any object preserves epimorphisms in a left-rigid abelian
monoidal preadditive category (Proposition 1.13.1 for left exactness on the left). -/
theorem whiskerLeft_epi {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [LeftRigidCategory C] [MonoidalPreadditive C]
    {Y Z : C} (f : Y ⟶ Z) [Epi f] (W : C) : Epi (W ◁ f) := by
  have adj := tensorLeftAdjunction (ᘁW) W
  haveI : PreservesColimitsOfSize.{0, 0} (tensorLeft W) := adj.leftAdjoint_preservesColimits
  haveI : (tensorLeft W).PreservesEpimorphisms :=
    preservesEpimorphisms_of_preservesColimitsOfShape _
  exact (tensorLeft W).map_epi f

/-- Left whiskering the right adjoint mate of a mono `f : X ⟶ 𝟙_ C` by `X` yields
an epimorphism. -/
theorem whiskerLeft_rightAdjointMate_epi {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [RightRigidCategory C] [LeftRigidCategory C] [MonoidalPreadditive C]
    {X : C} (f : X ⟶ 𝟙_ C) [Mono f] :
    Epi (X ◁ rightAdjointMate f) := by
  haveI : Epi (rightAdjointMate f) := rightAdjointMate_epi_of_mono f
  exact whiskerLeft_epi (rightAdjointMate f) X

/-- If `X` is simple and `f : X ⟶ 𝟙_ C` is a nonzero monomorphism, there exists a
nonzero epimorphism `X ⟶ X ⊗ Xᘁ`, obtained from `ρ⁻¹` composed with whiskering
of the mate of `f`. -/
theorem exists_epi_to_tensor_dual {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [RightRigidCategory C] [LeftRigidCategory C] [MonoidalPreadditive C]
    {X : C} [Simple X] (f : X ⟶ 𝟙_ C) [Mono f] (hf : f ≠ 0) :
    ∃ (e : X ⟶ X ⊗ Xᘁ), Epi e ∧ e ≠ 0 := by

  have h_epi : Epi (X ◁ rightAdjointMate f) := whiskerLeft_rightAdjointMate_epi f
  refine ⟨(ρ_ X).inv ≫ X ◁ rightAdjointMate f, epi_comp _ _, ?_⟩

  intro he

  have h1 : X ◁ rightAdjointMate f = 0 := by
    rwa [← cancel_epi (ρ_ X).inv, comp_zero]

  have hid : 𝟙 (X ⊗ Xᘁ) = 0 := by
    have : (X ◁ rightAdjointMate f) ≫ 𝟙 (X ⊗ Xᘁ) =
           (X ◁ rightAdjointMate f) ≫ 0 := by simp [h1]
    exact (cancel_epi (X ◁ rightAdjointMate f)).mp this

  have hZero : IsZero (X ⊗ Xᘁ) := (IsZero.iff_id_eq_zero _).mpr hid

  have hX : ¬ IsZero X := fun hZ => hf (hZ.eq_of_src f 0)

  have hη : η_ X Xᘁ ≠ 0 := coevaluation_ne_zero_of_nonzero_obj X hX

  exact hη (hZero.eq_of_tgt _ _)

/-- If `X` is a simple subobject of the unit (via a nonzero mono `f : X ⟶ 𝟙_ C`),
then there exists a nonzero morphism `𝟙_ C ⟶ X`. This produces a candidate retraction
of `f` after passing through `End(𝟙)`. -/
theorem simple_subobj_unit_retraction {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [RightRigidCategory C] [LeftRigidCategory C] [MonoidalPreadditive C]
    {X : C} [Simple X] (f : X ⟶ 𝟙_ C) [Mono f] (hf : f ≠ 0) :
    ∃ (g : 𝟙_ C ⟶ X), g ≠ 0 := by

  have hX : ¬ IsZero X := fun hZ => hf (hZ.eq_of_src f 0)

  have hη : η_ X Xᘁ ≠ 0 := coevaluation_ne_zero_of_nonzero_obj X hX

  obtain ⟨e, he_epi, he_ne⟩ := exists_epi_to_tensor_dual f hf
  haveI := he_epi

  haveI : IsIso e := isIso_of_epi_of_simple_src e he_ne

  refine ⟨η_ X Xᘁ ≫ inv e, ?_⟩

  intro h
  apply hη
  rw [← cancel_mono (inv e)]
  simp [h]

/-- Any nonzero Artinian object in an abelian category contains a simple subobject,
realized as a nonzero monomorphism `S ⟶ X` with `S` simple. -/
theorem exists_simple_subobject {C : Type u} [Category.{v} C]
    [Abelian C] (X : C) [IsArtinianObject X] (hX : ¬ IsZero X) :
    ∃ (S : C) (_ : Simple S) (i : S ⟶ X), Mono i ∧ i ≠ 0 := by
  obtain ⟨Y, hSimple⟩ := CategoryTheory.exists_simple_subobject hX
  refine ⟨(Y : C), hSimple, Y.arrow, ⟨Subobject.arrow_mono Y, ?_⟩⟩
  intro h
  apply Simple.not_isZero (Y : C)
  rw [IsZero.iff_id_eq_zero]
  have hm : Mono Y.arrow := Subobject.arrow_mono Y
  have : (𝟙 (Y : C)) ≫ Y.arrow = 0 ≫ Y.arrow := by simp [h]
  exact (cancel_mono Y.arrow).mp this

/-- Given that every nonzero endomorphism of `𝟙_ C` is a unit in `End(𝟙_ C)`,
any nonzero endomorphism of the unit is an isomorphism. -/
theorem endUnit_isIso_of_ne_zero {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Preadditive C]
    (hEnd : ∀ (g : End (𝟙_ C)), g ≠ 0 → IsUnit g)
    (f : 𝟙_ C ⟶ 𝟙_ C) (hf : f ≠ 0) : IsIso f :=
  (isUnit_iff_isIso f).mp (hEnd f hf)

set_option maxHeartbeats 800000 in
/-- A commutative semisimple ring with no nontrivial idempotents is a field, so every
nonzero element is a unit. The proof uses the Wedderburn-Artin decomposition into
matrix algebras over division rings and rules out factors via idempotents. -/
theorem commSemisimpleRing_noNontrivialIdempotents_isUnit
    (R : Type*) [CommRing R] [IsSemisimpleRing R]
    (htriv : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    ∀ g : R, g ≠ 0 → IsUnit g := by
  obtain ⟨n, D, d, hDiv, hNe, ⟨φ⟩⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  let M := fun i => Matrix (Fin (d i)) (Fin (d i)) (D i)
  have hn_le_one : n ≤ 1 := by
    by_contra h_gt
    have h_gt : 1 < n := by omega
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have hid_prod : IsIdempotentElem (Pi.single (M := M) i0 1) := by
      show Pi.single (M := M) i0 1 * Pi.single (M := M) i0 1 = Pi.single (M := M) i0 1
      ext j; simp only [Pi.mul_apply]
      by_cases hij : j = i0
      · subst hij; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne hij]
    have hid : IsIdempotentElem (φ.symm (Pi.single (M := M) i0 1)) := by
      show φ.symm _ * φ.symm _ = φ.symm _
      rw [← map_mul]; exact congrArg _ hid_prod
    rcases htriv _ hid with h0 | h1
    · have h := φ.symm.injective (h0.trans (map_zero φ.symm).symm)
      have := congr_fun h i0; simp [Pi.single_eq_same] at this
    · have h := φ.symm.injective (h1.trans (map_one φ.symm).symm)
      have h2 := congr_fun h i1
      simp only [Pi.single_eq_of_ne hi01.symm, Pi.one_apply] at h2
      letI := hDiv i1; letI := hNe i1
      exact absurd h2.symm one_ne_zero
  interval_cases n
  · intro g hg; exfalso; apply hg
    apply φ.injective; funext i; exact Fin.elim0 i
  · intro g hg
    suffices IsUnit (φ g) by rw [← φ.symm_apply_apply g]; exact this.map φ.symm
    letI := hDiv 0; letI := hNe 0
    haveI : Nonempty (Fin (d 0)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
    have hfactor_comm : ∀ (a b : M 0), a * b = b * a := by
      intro a b
      have h := mul_comm (φ.symm (Pi.single (0 : Fin 1) a)) (φ.symm (Pi.single (0 : Fin 1) b))
      rw [← map_mul, ← map_mul] at h
      have h2 := φ.symm.injective h
      have h3 := congr_fun h2 (0 : Fin 1)
      simp [Pi.single_eq_same, Pi.mul_apply] at h3; exact h3
    haveI : IsSimpleRing (M 0) := IsSimpleRing.matrix (Fin (d 0)) (D 0)
    letI : CommRing (M 0) := { (inferInstance : Ring (M 0)) with mul_comm := hfactor_comm }
    have hField := (isSimpleRing_iff_isField (M 0)).mp ‹_›
    rw [Pi.isUnit_iff]
    intro i; fin_cases i
    have hφg_ne : φ g ≠ 0 := fun h => hg (φ.injective (h.trans (map_zero φ).symm))
    have h0_ne : (φ g) (0 : Fin 1) ≠ 0 := by
      intro h; apply hφg_ne; funext j; fin_cases j; exact h
    obtain ⟨b, hab⟩ := hField.mul_inv_cancel h0_ne
    exact ⟨⟨(φ g) 0, b, hab, hfactor_comm b _ ▸ hab⟩, rfl⟩

/-- If the unit object is indecomposable, then every idempotent in `End(𝟙_ C)` is
either `0` or `1` (i.e. there are no nontrivial idempotents). -/
theorem endUnit_trivialIdempotents {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C]
    (hIndecomp : Indecomposable (𝟙_ C))
    (e : End (𝟙_ C)) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hee : e ≫ e = e := he
  exact idem_trivial_of_indecomposable hIndecomp e hee

/-- Combining semisimplicity of `End(𝟙_ C)` with indecomposability of the unit,
every nonzero endomorphism of the unit object is a unit. -/
theorem endUnit_isUnit_of_ne_zero {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [MonoidalBiexact C]
    [IsArtinianRing (End (𝟙_ C))]
    (hIndecomp : Indecomposable (𝟙_ C))
    (g : End (𝟙_ C)) (hg : g ≠ 0) :
    IsUnit g := by
  haveI : IsSemisimpleRing (End (𝟙_ C)) := endUnit_isSemisimpleRing
  exact commSemisimpleRing_noNontrivialIdempotents_isUnit
    (End (𝟙_ C)) (endUnit_trivialIdempotents hIndecomp) g hg

/-- Theorem 1.15.8 (i): In a ring category with right duals (here modeled by the
rigid abelian monoidally biexact setting), the unit object `𝟙_ C` is simple. -/
theorem unitIsSimple (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [RightRigidCategory C] [LeftRigidCategory C] [MonoidalPreadditive C]
    [MonoidalBiexact C] [IsArtinianRing (End (𝟙_ C))] [IsArtinianObject (𝟙_ C)]
    (hIndecomp : Indecomposable (𝟙_ C)) :
    Simple (𝟙_ C) where
  mono_isIso_iff_nonzero {Y} f := by
    intro _hMono

    have hEnd : ∀ (g : End (𝟙_ C)), g ≠ 0 → IsUnit g :=
      endUnit_isUnit_of_ne_zero hIndecomp
    have h_nonzero : ¬ IsZero (𝟙_ C) := hIndecomp.1
    constructor
    ·
      intro hiso hf0
      subst hf0
      have : 𝟙 (𝟙_ C) = 0 := by
        have := IsIso.inv_hom_id (f := (0 : Y ⟶ 𝟙_ C))
        simp at this; exact this.symm
      exact h_nonzero ((IsZero.iff_id_eq_zero (𝟙_ C)).mpr this)
    ·
      intro hf

      have hY : ¬ IsZero Y := fun hZ => hf (hZ.eq_of_src f 0)

      haveI : IsArtinianObject Y := isArtinianObject_of_mono f

      obtain ⟨S, hS, i, hMono_i, hne_i⟩ := exists_simple_subobject Y hY
      haveI := hMono_i; haveI := hS

      have hne_if : i ≫ f ≠ 0 := fun h => hne_i (by rwa [← cancel_mono f, zero_comp])
      haveI : Mono (i ≫ f) := mono_comp i f

      obtain ⟨g, hg⟩ := simple_subobj_unit_retraction (i ≫ f) hne_if

      have hgif : g ≫ (i ≫ f) ≠ 0 :=
        fun h => hg (by rwa [← cancel_mono (i ≫ f), zero_comp])

      haveI : IsIso (g ≫ (i ≫ f)) := endUnit_isIso_of_ne_zero hEnd _ hgif

      have hsec : (inv (g ≫ (i ≫ f)) ≫ g ≫ i) ≫ f = 𝟙 (𝟙_ C) := by
        simp [assoc]

      haveI : IsSplitEpi f := ⟨⟨inv (g ≫ (i ≫ f)) ≫ g ≫ i, hsec⟩⟩
      haveI : Epi f := inferInstance
      exact isIso_of_mono_of_epi f

/-- Instance form of `unitIsSimple`, registering simplicity of `𝟙_ C` for typeclass
inference whenever an indecomposability hypothesis is supplied. -/
instance instSimpleUnitOfUnitIsSimple (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [RightRigidCategory C] [LeftRigidCategory C] [MonoidalPreadditive C]
    [MonoidalBiexact C] [IsArtinianRing (End (𝟙_ C))] [IsArtinianObject (𝟙_ C)]
    (hIndecomp : Indecomposable (𝟙_ C)) : Simple (𝟙_ C) :=
  unitIsSimple C hIndecomp

section UnitSimpleConsequences

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]

end UnitSimpleConsequences

end TensorCategories
