/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.HomologySequenceLemmas

noncomputable section

open CategoryTheory

universe u

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

abbrev GModule (k : Type u) [CommRing k] (G : Type u) [Group G] := Rep k G

abbrev GInvariants (A : Rep k G) : Submodule k A := A.ρ.invariants

abbrev nCochains (A : Rep k G) (n : ℕ) : ModuleCat k :=
  (groupCohomology.inhomogeneousCochains A).X n

abbrev coboundaryMap (A : Rep k G) (n : ℕ) :
    nCochains A n ⟶ nCochains A (n + 1) :=
  (groupCohomology.inhomogeneousCochains A).d n (n + 1)

theorem coboundaryMap_comp_coboundaryMap (A : Rep k G) (n : ℕ) :
    coboundaryMap A n ≫ coboundaryMap A (n + 1) = 0 := by
  exact (groupCohomology.inhomogeneousCochains A).d_comp_d n (n + 1) (n + 2)

abbrev cochainComplex (A : Rep k G) : CochainComplex (ModuleCat k) ℕ :=
  groupCohomology.inhomogeneousCochains A

abbrev nCocycles (A : Rep k G) (n : ℕ) : ModuleCat k :=
  groupCohomology.cocycles A n

abbrev CohomologyGroup (A : Rep k G) (n : ℕ) : ModuleCat k :=
  groupCohomology A n

def cochainComplexMap {A B : Rep k G} (φ : A ⟶ B) :
    cochainComplex A ⟶ cochainComplex B :=
  groupCohomology.cochainsMap (MonoidHom.id G) φ

def cohomology_map {A B : Rep k G} (φ : A ⟶ B) (n : ℕ) :
    CohomologyGroup A n ⟶ CohomologyGroup B n :=
  groupCohomology.map (MonoidHom.id G) φ n

theorem ses_cochains_exact {X : CategoryTheory.ShortComplex (Rep k G)}
    (hX : X.ShortExact) :
    (X.map (groupCohomology.cochainsFunctor k G)).ShortExact :=
  groupCohomology.map_cochainsFunctor_shortExact hX

theorem long_exact_sequence_exact₂
    {X : CategoryTheory.ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ) :
    (groupCohomology.mapShortComplex₂ X n).Exact :=
  groupCohomology.mapShortComplex₂_exact hX n

theorem long_exact_sequence_exact₁
    {X : CategoryTheory.ShortComplex (Rep k G)} (hX : X.ShortExact)
    {i j : ℕ} (hij : i + 1 = j) :
    (groupCohomology.mapShortComplex₁ hX hij).Exact :=
  groupCohomology.mapShortComplex₁_exact hX hij

end GroupCohomology

namespace DeltaFunctor

open CategoryTheory

universe w₁ w₂

variable (𝒜 : Type w₁) [Category.{w₂} 𝒜] [Abelian 𝒜]
         (ℬ : Type w₁) [Category.{w₂} ℬ] [Abelian ℬ]

structure CohomologicalDeltaFunctor where
  F : ℕ → (𝒜 ⥤ ℬ)
  additive : ∀ n, (F n).Additive
  δ : ∀ (S : ShortComplex 𝒜) (_ : S.ShortExact) (n : ℕ),
    (F n).obj S.X₃ ⟶ (F (n + 1)).obj S.X₁
  map_g_comp_δ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (F n).map S.g ≫ δ S hS n = 0
  δ_comp_map_f : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    δ S hS n ≫ (F (n + 1)).map S.f = 0
  exact₂ : ∀ (S : ShortComplex 𝒜) (_ : S.ShortExact) (n : ℕ),
    (ShortComplex.mk ((F n).map S.f) ((F n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact
  exact₃ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk ((F n).map S.g) (δ S hS n) (map_g_comp_δ S hS n)).Exact
  exact₁ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk (δ S hS n) ((F (n + 1)).map S.f) (δ_comp_map_f S hS n)).Exact
  δ_natural : ∀ {S T : ShortComplex 𝒜} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ),
    δ S hS n ≫ (F (n + 1)).map φ.τ₁ = (F n).map φ.τ₃ ≫ δ T hT n

structure HomologicalDeltaFunctor where
  F : ℕ → (𝒜 ⥤ ℬ)
  additive : ∀ n, (F n).Additive
  δ : ∀ (S : ShortComplex 𝒜) (_ : S.ShortExact) (n : ℕ),
    (F (n + 1)).obj S.X₃ ⟶ (F n).obj S.X₁
  map_g_comp_δ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (F (n + 1)).map S.g ≫ δ S hS n = 0
  δ_comp_map_f : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    δ S hS n ≫ (F n).map S.f = 0
  exact₂ : ∀ (S : ShortComplex 𝒜) (_ : S.ShortExact) (n : ℕ),
    (ShortComplex.mk ((F n).map S.f) ((F n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact
  exact₁ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk (δ S hS n) ((F n).map S.f) (δ_comp_map_f S hS n)).Exact
  exact₃ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk ((F (n + 1)).map S.g) (δ S hS n) (map_g_comp_δ S hS n)).Exact
  δ_natural : ∀ {S T : ShortComplex 𝒜} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ),
    δ S hS n ≫ (F n).map φ.τ₁ = (F (n + 1)).map φ.τ₃ ≫ δ T hT n

end DeltaFunctor

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

def standardResolution (k G : Type u) [CommRing k] [Group G] :
    ProjectiveResolution (Rep.trivial k G k) :=
  Rep.standardResolution k G

structure FreeResolution (R : Type u) [Ring R] (M : ModuleCat.{u} R) extends
    ProjectiveResolution M where
  free : ∀ n, Module.Free R (complex.X n)

attribute [instance] FreeResolution.free

def barComplex_iso_standardComplex (k G : Type u) [CommRing k] [Group G] :
    Rep.barComplex k G ≅ Rep.standardComplex k G :=
  Rep.barComplex.isoStandardComplex k G

def cohomology_iso_ext (A : Rep k G) (n : ℕ) :
    CohomologyGroup A n ≅
    ((Ext k (Rep k G) n).obj (Opposite.op (Rep.trivial k G k))).obj A :=
  groupCohomologyIsoExt A n

class IsAdditiveCategory (C : Type*) [Category C] extends Preadditive C where
  [hasFiniteBiproducts : Limits.HasFiniteBiproducts C]

attribute [instance] IsAdditiveCategory.hasFiniteBiproducts

instance (priority := 100) IsAdditiveCategory.toHasFiniteCoproducts
    (C : Type*) [Category C] [IsAdditiveCategory C] :
    Limits.HasFiniteCoproducts C :=
  inferInstance

instance (priority := 100) IsAdditiveCategory.toHasFiniteProducts
    (C : Type*) [Category C] [IsAdditiveCategory C] :
    Limits.HasFiniteProducts C :=
  inferInstance

instance (priority := 100) IsAdditiveCategory.toHasZeroObject
    (C : Type*) [Category C] [IsAdditiveCategory C] :
    Limits.HasZeroObject C :=
  Limits.hasZeroObject_of_hasFiniteBiproducts C

class IsAdditiveFunctor {C : Type*} {D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) extends F.Additive

instance cochainsFunctor_additive (k G : Type u) [CommRing k] [Group G] :
    (groupCohomology.cochainsFunctor k G).Additive := inferInstance

def cohomology_biprod_iso (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    groupCohomology (A ⊞ B) n ≅
    groupCohomology A n ⊞ groupCohomology B n := by
  open Limits in
  let F := groupCohomology.cochainsFunctor k G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n
  haveI : F.Additive := inferInstance
  haveI : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  haveI : PreservesBiproductsOfShape WalkingPair F := PreservesFiniteBiproducts.preserves
  haveI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapBiprod A B

def coinduced_def (k G : Type u) [CommRing k] [Group G] :
    Rep k ↥(⊥ : Subgroup G) ⥤ Rep k G :=
  Rep.coindFunctor k (⊥ : Subgroup G).subtype

theorem cohomology_coinduced_vanishing
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) (n : ℕ) :
    Limits.IsZero
      (groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) := by
  haveI : Subsingleton ↥(⊥ : Subgroup G) := Unique.instSubsingleton
  exact (isZero_groupCohomology_succ_of_subsingleton A n).of_iso
    (groupCohomology.coindIso A (n + 1))

def cohomology_coinduced_H0_iso
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupCohomology A 0 :=
  groupCohomology.coindIso A 0

abbrev HomologyGroup (A : Rep k G) (n : ℕ) : ModuleCat k :=
  groupHomology A n

def homology_map {A B : Rep k G} (φ : A ⟶ B) (n : ℕ) :
    HomologyGroup A n ⟶ HomologyGroup B n :=
  groupHomology.map (MonoidHom.id G) φ n

theorem homology_map_id (A : Rep k G) (n : ℕ) :
    homology_map (𝟙 A) n = 𝟙 (HomologyGroup A n) :=
  groupHomology.map_id n

theorem homology_map_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    homology_map (φ ≫ ψ) n = homology_map φ n ≫ homology_map ψ n :=
  groupHomology.map_id_comp φ ψ n

def homologyFunctor (k : Type u) [CommRing k] (G : Type u) [Group G] (n : ℕ) :
    Rep k G ⥤ ModuleCat k :=
  groupHomology.functor k G n

def induced_def (k G : Type u) [CommRing k] [Group G] :
    Rep k ↥(⊥ : Subgroup G) ⥤ Rep k G :=
  Rep.indFunctor k (⊥ : Subgroup G).subtype

section ExactFunctor

open CategoryTheory.Limits CategoryTheory.ShortComplex

variable {C' : Type*} [Category C'] [Limits.HasZeroMorphisms C']

structure IsLeftExact (S : ShortComplex C') : Prop where
  mono_f : Mono S.f
  exact : S.Exact

structure IsRightExact (S : ShortComplex C') : Prop where
  exact : S.Exact
  epi_g : Epi S.g

abbrev IsLeftExactFunctor {C' D' : Type*} [Category C'] [Category D']
    (F : C' ⥤ D') : Prop :=
  PreservesFiniteLimits F

abbrev IsRightExactFunctor {C' D' : Type*} [Category C'] [Category D']
    (F : C' ⥤ D') : Prop :=
  PreservesFiniteColimits F

abbrev LeftExact (C' D' : Type*) [Category C'] [Category D'] :=
  LeftExactFunctor C' D'

abbrev RightExact (C' D' : Type*) [Category C'] [Category D'] :=
  RightExactFunctor C' D'

end ExactFunctor

end GroupCohomology

namespace ChainComplexDef

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

abbrev ChainComplexRMod (R : Type v) [Ring R] := ChainComplex (ModuleCat.{v} R) ℕ

abbrev chainObject (C : ChainComplexRMod R) (n : ℕ) : ModuleCat R := C.X n

abbrev boundaryMap (C : ChainComplexRMod R) (n : ℕ) :
    chainObject C (n + 1) ⟶ chainObject C n :=
  C.d (n + 1) n

abbrev chainHomology (C : ChainComplexRMod R) (n : ℕ) : ModuleCat R := C.homology n

def chainHomologyFunctor (R : Type v) [Ring R] (n : ℕ) :
    ChainComplexRMod R ⥤ ModuleCat R :=
  HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ) n

end ChainComplexDef

namespace ChainHomotopy

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

abbrev ChainHomotopy {C D : ChainComplexDef.ChainComplexRMod R} (f g : C ⟶ D) := Homotopy f g

def HomotopicChainMaps {C D : ChainComplexDef.ChainComplexRMod R} (f g : C ⟶ D) : Prop :=
  Nonempty (Homotopy f g)

theorem homotopicChainMaps_refl {C D : ChainComplexDef.ChainComplexRMod R} (f : C ⟶ D) :
    HomotopicChainMaps f f :=
  ⟨Homotopy.refl f⟩

theorem homotopicChainMaps_symm {C D : ChainComplexDef.ChainComplexRMod R} {f g : C ⟶ D}
    (h : HomotopicChainMaps f g) : HomotopicChainMaps g f :=
  h.map Homotopy.symm

theorem homotopicChainMaps_trans {C D : ChainComplexDef.ChainComplexRMod R} {f₁ f₂ f₃ : C ⟶ D}
    (h₁ : HomotopicChainMaps f₁ f₂) (h₂ : HomotopicChainMaps f₂ f₃) :
    HomotopicChainMaps f₁ f₃ := by
  obtain ⟨h₁⟩ := h₁
  obtain ⟨h₂⟩ := h₂
  exact ⟨h₁.trans h₂⟩

end ChainHomotopy

namespace HomotopyHomology

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

theorem homotopic_chain_maps_induce_equal_homology
    {C D : ChainComplexDef.ChainComplexRMod R} {f g : C ⟶ D}
    (h : Homotopy f g) (n : ℕ) :
    (ChainComplexDef.chainHomologyFunctor R n).map f = (ChainComplexDef.chainHomologyFunctor R n).map g :=
  h.homologyMap_eq n

end HomotopyHomology

namespace DerivedFunctor

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

abbrev CochainComplexRMod (R : Type v) [Ring R] := CochainComplex (ModuleCat.{v} R) ℕ

abbrev cochainObject (C : CochainComplexRMod R) (n : ℕ) : ModuleCat R := C.X n

abbrev coboundaryMap (C : CochainComplexRMod R) (n : ℕ) :
    cochainObject C n ⟶ cochainObject C (n + 1) :=
  C.d n (n + 1)

theorem coboundaryMap_comp_coboundaryMap (C : CochainComplexRMod R) (n : ℕ) :
    coboundaryMap C n ≫ coboundaryMap C (n + 1) = 0 :=
  C.d_comp_d n (n + 1) (n + 2)

abbrev cochainCohomology (C : CochainComplexRMod R) (n : ℕ) : ModuleCat R := C.homology n

def cochainCohomologyFunctor (R : Type v) [Ring R] (n : ℕ) :
    CochainComplexRMod R ⥤ ModuleCat R :=
  HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℕ) n

end DerivedFunctor

namespace LongExactDerived

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

def cochainConnectingHomomorphism
    {S : ShortComplex (DerivedFunctor.CochainComplexRMod R)}
    (hS : S.ShortExact) (n : ℕ) :
    DerivedFunctor.cochainCohomology S.X₃ n ⟶ DerivedFunctor.cochainCohomology S.X₁ (n + 1) :=
  hS.δ n (n + 1) rfl

theorem cochainLES_exact
    {S : ShortComplex (DerivedFunctor.CochainComplexRMod R)}
    (hS : S.ShortExact) (n : ℕ) :
    (HomologicalComplex.HomologySequence.composableArrows₅ hS n (n + 1) rfl).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact hS n (n + 1) rfl

end LongExactDerived

namespace CochainHomotopyCohomology

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

theorem homotopic_cochain_maps_cohomology_eq
    {C D : DerivedFunctor.CochainComplexRMod R}
    {f g : C ⟶ D} (h : Homotopy f g) (n : ℕ) :
    HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap g n :=
  h.homologyMap_eq n

end CochainHomotopyCohomology

namespace Resolution

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

abbrev ProjectiveResolutionRMod (M : ModuleCat.{v} R) :=
  ProjectiveResolution M

abbrev ProjectiveResolutionRMod.complex' {M : ModuleCat.{v} R}
    (P : ProjectiveResolutionRMod M) : ChainComplex (ModuleCat.{v} R) ℕ :=
  P.complex

abbrev InjectiveResolutionRMod (M : ModuleCat.{v} R) :=
  InjectiveResolution M

theorem ProjectiveResolutionRMod.exactAt_succ {M : ModuleCat.{v} R}
    (P : ProjectiveResolutionRMod M) (n : ℕ) :
    P.complex.ExactAt (n + 1) :=
  P.complex_exactAt_succ n

theorem InjectiveResolutionRMod.exactAt_succ {M : ModuleCat.{v} R}
    (I : InjectiveResolutionRMod M) (n : ℕ) :
    I.cocomplex.ExactAt (n + 1) :=
  I.cocomplex_exactAt_succ n

end Resolution

namespace HomFunctorHomotopy

open CategoryTheory HomologicalComplex

universe v

variable {R : Type v} [Ring R]

def homotopyOp {ι : Type*} {V : Type*} [Category V] [Preadditive V]
    {c : ComplexShape ι} {C D : HomologicalComplex V c}
    {f g : C ⟶ D} (h : Homotopy f g) : Homotopy
    ((opFunctor V c).map f.op)
    ((opFunctor V c).map g.op) where
  hom i j := (h.hom j i).op
  zero i j hij := by
    have := h.zero j i hij
    rw [this]
    exact Limits.op_zero _ _
  comm i := by
    have H := h.comm i
    dsimp [dNext, prevD] at H ⊢
    change (f.f i).op =
      (h.hom i (c.prev i) ≫ D.d (c.prev i) i).op +
      (C.d i (c.next i) ≫ h.hom (c.next i) i).op +
      (g.f i).op
    rw [H]
    simp only [op_add, add_comm]

noncomputable def homStarFunctor (A : ModuleCat.{v} R) :
    (ChainComplexDef.ChainComplexRMod R)ᵒᵖ ⥤
    HomologicalComplex AddCommGrpCat.{v} (ComplexShape.down ℕ).symm :=
  opFunctor _ _ ⋙ (preadditiveYoneda.obj A).mapHomologicalComplex _

theorem hom_functor_preserves_homotopy (A : ModuleCat.{v} R)
    {C D : ChainComplexDef.ChainComplexRMod R} {f g : C ⟶ D}
    (hfg : Nonempty (Homotopy f g)) :
    Nonempty (Homotopy ((homStarFunctor A).map f.op)
                        ((homStarFunctor A).map g.op)) :=

  hfg.map (fun h => Functor.mapHomotopy (preadditiveYoneda.obj A) (homotopyOp h))

end HomFunctorHomotopy
