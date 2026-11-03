/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Support
import Atlas.LieGroups.code.DModuleApplications
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

open CategoryTheory

namespace DModulesII


def IsSupportedOn {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (I : Ideal R) : Prop :=
  ∀ (f : R), f ∈ I → ∀ (v : M), ∃ N : ℕ, (f ^ N) • v = 0

def sheafSupport (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Set (PrimeSpectrum R) :=
  ⋂ (I : Ideal R) (_ : IsSupportedOn M I), PrimeSpectrum.zeroLocus (I : Set R)

section DModules

variable {R : Type*} [CommRing R] {D : Type*} [Ring D] (ι : R →+* D)

@[reducible]
def rModuleOf (M : Type*) [AddCommGroup M] [Module D M] : Module R M :=
  Module.compHom M ι

def DModIsSupportedOn (M : Type*) [AddCommGroup M] [Module D M] (I : Ideal R) : Prop :=
  @IsSupportedOn R _ M _ (rModuleOf ι M) I

abbrev DModSupportedPred (I : Ideal R) : ObjectProperty (ModuleCat D) := fun M =>
  ∀ (f : R), f ∈ I → ∀ (v : M), ∃ N : ℕ, (ι f ^ N) • v = 0

abbrev DModSupportedCat (I : Ideal R) := (DModSupportedPred ι I).FullSubcategory

def annihilatedByIdeal (I : Ideal R) (M : Type*) [AddCommGroup M] [Module D M] : Set M :=
  {v : M | ∀ f ∈ I, (ι f) • v = 0}

def annihilatedByIdealAddSubgroup (I : Ideal R) (M : Type*) [AddCommGroup M] [Module D M] :
    AddSubgroup M where
  carrier := annihilatedByIdeal ι I M
  zero_mem' := fun f _ => smul_zero _
  add_mem' := fun {a b} ha hb f hf => by
    show (ι f) • (a + b) = 0
    rw [smul_add, ha f hf, hb f hf, add_zero]
  neg_mem' := fun {a} ha f hf => by
    show (ι f) • (-a) = 0
    rw [smul_neg, ha f hf, neg_zero]

def DModSheafSupport (M : Type*) [AddCommGroup M] [Module D M] : Set (PrimeSpectrum R) :=
  @sheafSupport R _ M _ (rModuleOf ι M)

class IsLeibnizCompatible (ι : R →+* D) (M : Type*) [AddCommGroup M] [Module D M] : Prop where
  smul_torsion : ∀ (d : D) (f : R) (m : M) (n : ℕ),
    (ι f ^ n) • m = 0 → ∃ N : ℕ, (ι f ^ N) • (d • m) = 0

lemma torsion_is_DSubmodule
    (M : Type*) [AddCommGroup M] [Module D M] [IsLeibnizCompatible ι M]
    (f : R) :
    ∃ (N : Submodule D M), ∀ v : M, v ∈ N ↔ ∃ n : ℕ, (ι f ^ n) • v = 0 := by
  refine ⟨{
    carrier := {v | ∃ n : ℕ, (ι f ^ n) • v = 0}
    add_mem' := ?_
    zero_mem' := ?_
    smul_mem' := ?_
  }, fun v => Iff.rfl⟩
  ·
    intro a b ⟨na, ha⟩ ⟨nb, hb⟩
    refine ⟨na + nb, ?_⟩
    rw [smul_add]
    have ha' : ι f ^ (na + nb) • a = 0 := by
      have : ι f ^ (na + nb) = ι f ^ nb * ι f ^ na := by
        rw [pow_add]; exact (Commute.pow_pow (Commute.refl (ι f)) na nb).eq
      rw [this, mul_smul, ha, smul_zero]
    have hb' : ι f ^ (na + nb) • b = 0 := by
      rw [pow_add, mul_smul, hb, smul_zero]
    rw [ha', hb', add_zero]
  ·
    exact ⟨0, smul_zero _⟩
  ·
    intro d v ⟨n, hn⟩
    exact IsLeibnizCompatible.smul_torsion d f v n hn

lemma sheafSupport_subset_implies_supported
    (M : Type*) [AddCommGroup M] [Module D M] [IsSimpleModule D M]
    (I : Ideal R)
    (h : DModSheafSupport ι M ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
    @IsSupportedOn R _ M _ (rModuleOf ι M) I := by
  letI : Module R M := rModuleOf ι M
  intro f hf v


  suffices hsuff : PrimeSpectrum.zeroLocus ((Submodule.span R {v}).annihilator : Set R) ⊆
      PrimeSpectrum.zeroLocus (I : Set R) by
    rw [PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hsuff
    have hfrad := hsuff hf
    rw [Ideal.mem_radical_iff] at hfrad
    obtain ⟨N, hN⟩ := hfrad
    rw [Submodule.mem_annihilator_span_singleton] at hN
    exact ⟨N, hN⟩

  calc PrimeSpectrum.zeroLocus ((Submodule.span R {v}).annihilator : Set R)
      ⊆ DModSheafSupport ι M := by
        intro p hp
        simp only [DModSheafSupport, sheafSupport, Set.mem_iInter]
        intro J hJ

        simp only [PrimeSpectrum.mem_zeroLocus] at hp ⊢
        intro g hg
        obtain ⟨N, hN⟩ := hJ g hg v
        have hmem : g ^ N ∈ (Submodule.span R {v}).annihilator := by
          rwa [Submodule.mem_annihilator_span_singleton]
        exact p.2.mem_of_pow_mem N (hp hmem)
    _ ⊆ PrimeSpectrum.zeroLocus (I : Set R) := h

theorem simple_DModule_support_preirreducible
    (M : Type*) [AddCommGroup M] [Module D M] [IsSimpleModule D M] [IsLeibnizCompatible ι M]
    (z₁ z₂ : Set (PrimeSpectrum R)) (hz₁ : IsClosed z₁) (hz₂ : IsClosed z₂)
    (hsub : DModSheafSupport ι M ⊆ z₁ ∪ z₂) :
    DModSheafSupport ι M ⊆ z₁ ∨ DModSheafSupport ι M ⊆ z₂ := by

  set I₁ := PrimeSpectrum.vanishingIdeal z₁
  set I₂ := PrimeSpectrum.vanishingIdeal z₂
  have hz₁_eq : z₁ = PrimeSpectrum.zeroLocus (I₁ : Set R) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hz₁.closure_eq]
  have hz₂_eq : z₂ = PrimeSpectrum.zeroLocus (I₂ : Set R) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hz₂.closure_eq]
  rw [hz₁_eq, hz₂_eq] at hsub ⊢

  rw [← PrimeSpectrum.zeroLocus_inf] at hsub

  have hsupp := sheafSupport_subset_implies_supported ι M (I₁ ⊓ I₂) hsub

  by_cases h₁ : @IsSupportedOn R _ M _ (rModuleOf ι M) I₁
  ·
    left; exact Set.iInter₂_subset I₁ h₁
  ·
    have h₁' : ∃ f₁ : R, f₁ ∈ I₁ ∧ ∃ v₀ : M, ∀ N : ℕ, ι (f₁ ^ N) • v₀ ≠ 0 := by
      by_contra h; push Not at h; exact h₁ (fun f hf v => h f hf v)
    obtain ⟨f₁, hf₁, v₀, hv₀⟩ := h₁'

    obtain ⟨T₁, hT₁⟩ := torsion_is_DSubmodule ι M f₁

    have hv₀_notin : v₀ ∉ T₁ := by
      rw [hT₁]; push Not; intro n
      have := hv₀ n; rwa [map_pow] at this

    have hT₁_bot : T₁ = ⊥ :=
      (IsSimpleOrder.eq_bot_or_eq_top T₁).resolve_right
        (fun h => hv₀_notin (h ▸ Submodule.mem_top))

    right; apply Set.iInter₂_subset I₂

    intro f₂ hf₂ v

    have hprod : f₁ * f₂ ∈ I₁ ⊓ I₂ :=
      ⟨Ideal.mul_mem_right f₂ I₁ hf₁, Ideal.mul_mem_left I₂ f₁ hf₂⟩

    obtain ⟨N, hN⟩ := hsupp (f₁ * f₂) hprod v

    have hcomm : Commute (ι f₁) (ι f₂) := by
      show ι f₁ * ι f₂ = ι f₂ * ι f₁
      rw [← map_mul, ← map_mul, mul_comm]


    have hmem : (ι f₂ ^ N) • v ∈ T₁ := by
      rw [hT₁]; exact ⟨N, by
        rw [← mul_smul, ← hcomm.mul_pow, ← map_mul, ← map_pow]
        exact hN⟩

    rw [hT₁_bot, Submodule.mem_bot] at hmem

    exact ⟨N, by show ι (f₂ ^ N) • v = 0; rw [map_pow]; exact hmem⟩

theorem irreducible_DModule_support_irreducible
    (M : Type*) [AddCommGroup M] [Module D M] [IsSimpleModule D M] [IsLeibnizCompatible ι M] :
    IsIrreducible (DModSheafSupport ι M) := by
  have hnt : Nontrivial M := IsSimpleModule.nontrivial D M
  constructor
  ·


    obtain ⟨v, w, hvw⟩ := hnt.exists_pair_ne
    set x := v - w
    have hx : x ≠ 0 := sub_ne_zero.mpr hvw

    let annx : Ideal R := {
      carrier := {r : R | ι r • x = 0}
      add_mem' := fun {a b} (ha : ι a • x = 0) (hb : ι b • x = 0) => by
        show ι (a + b) • x = 0; rw [map_add, add_smul, ha, hb, add_zero]
      zero_mem' := by show ι 0 • x = 0; rw [map_zero, zero_smul]
      smul_mem' := fun c {r} (hr : ι r • x = 0) => by
        show ι (c * r) • x = 0; rw [map_mul, mul_smul, hr, smul_zero]
    }
    have hannx_proper : annx ≠ ⊤ := by
      rw [Ideal.ne_top_iff_one]
      show ¬ (ι 1 • x = 0)
      rw [map_one, one_smul]; exact hx
    obtain ⟨m, hm_max, hm_le⟩ := Ideal.exists_le_maximal annx hannx_proper
    refine ⟨⟨m, hm_max.isPrime⟩, ?_⟩
    simp only [DModSheafSupport, sheafSupport, Set.mem_iInter]
    intro I hI
    rw [PrimeSpectrum.mem_zeroLocus]
    intro f hfI


    obtain ⟨N, hN⟩ := hI f hfI x
    have hfN_annx : f ^ N ∈ annx := by show ι (f ^ N) • x = 0; exact hN
    exact hm_max.isPrime.mem_of_pow_mem N (hm_le hfN_annx)
  ·


    rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro z₁ z₂ hz₁ hz₂ hsub
    exact simple_DModule_support_preirreducible ι M z₁ z₂ hz₁ hz₂ hsub

class IsKashiwaraSetup
    {R : Type*} [CommRing R] {D : Type*} [Ring D] (_ : R →+* D)
    (I : Ideal R) (D' : Type*) [Ring D'] (ι' : R ⧸ I →+* D') : Prop where
  isSmooth_X : IsNoetherian R R
  isSmooth_Z : IsNoetherian (R ⧸ I) (R ⧸ I)
  ι'_injective : Function.Injective ι'



end DModules


section GEquivariantSheafDef

universe u_sheaf

structure QCohSheafData (k : Type u_sheaf) [Field k] where
  affineIndex : Type u_sheaf
  coordRing : affineIndex → Type u_sheaf
  [instCommRing : ∀ i, CommRing (coordRing i)]
  [instAlgebra : ∀ i, Algebra k (coordRing i)]
  diffOpsRing : affineIndex → Type u_sheaf
  [instDiffRing : ∀ i, Ring (diffOpsRing i)]
  sections : affineIndex → Type u_sheaf
  [instAddCommGroup : ∀ i, AddCommGroup (sections i)]
  [instModule : ∀ i, Module (diffOpsRing i) (sections i)]
  [instModuleK : ∀ i, Module k (sections i)]

attribute [instance] QCohSheafData.instCommRing QCohSheafData.instAlgebra
  QCohSheafData.instDiffRing QCohSheafData.instAddCommGroup QCohSheafData.instModule
  QCohSheafData.instModuleK

structure GEquivariantSheaf (k : Type u_sheaf) [Field k]
    (G : Type u_sheaf) [Group G] where
  sheafData : QCohSheafData k
  [mulAction : MulAction G sheafData.affineIndex]
  phi : (g : G) → (i : sheafData.affineIndex) →
    sheafData.sections i ≃ₗ[k] sheafData.sections (g • i)
  cocycle : ∀ (g h : G) (i : sheafData.affineIndex) (v : sheafData.sections i),
    (mul_smul g h i) ▸ (phi (g * h) i v) =
    phi g (h • i) (phi h i v)
  phi_one : ∀ (i : sheafData.affineIndex) (v : sheafData.sections i),
    (one_smul G i) ▸ (phi 1 i v) = v

end GEquivariantSheafDef


section Equivariant

variable (k : Type*) [Field k]
         (G : Type*) [Group G]
         (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra k 𝔤]
         (D : Type*) [Ring D] [Algebra k D]

structure GEquivQCohSheaf
    (M : Type*) [AddCommGroup M] [Module k M] where
  groupAction : G →* (M ≃ₗ[k] M)

structure WeaklyEquivDModule
    (M : Type*) [AddCommGroup M] [Module k M] [Module D M]
    extends GEquivQCohSheaf k G M where
  groupAction_DLinear : ∀ (g : G) (d : D) (m : M),
    groupAction g (d • m) = d • (groupAction g m)

structure EquivDModule
    (M : Type*) [AddCommGroup M] [Module k M] [Module D M]
    extends WeaklyEquivDModule k G D M where
  lieToD : 𝔤 →ₗ⁅k⁆ D
  lieAction_phi : 𝔤 →ₗ[k] Module.End k M
  actions_agree : ∀ (x : 𝔤) (v : M), lieAction_phi x v = (lieToD x) • v

def rho_phi {M : Type*} [AddCommGroup M] [Module k M] [Module D M]
    (_W : WeaklyEquivDModule k G D M)
    (lieAction_phi : 𝔤 →ₗ[k] Module.End k M)
    (lieToD : 𝔤 →ₗ⁅k⁆ D) (x : 𝔤) (v : M) : M :=
  lieAction_phi x v - (lieToD x) • v

abbrev MonodromicDModule
    (T : Type*) [CommGroup T]
    (D' : Type*) [Ring D'] [Algebra k D']
    (M : Type*) [AddCommGroup M] [Module k M] [Module D' M] :=
  WeaklyEquivDModule k T D' M

def monodromic_rho_phi
    {M : Type*} [AddCommGroup M] [Module k M] [Module D M]
    (W : WeaklyEquivDModule k G D M)
    (lieAction_phi : 𝔤 →ₗ[k] Module.End k M)
    (lieToD : 𝔤 →ₗ⁅k⁆ D) (x : 𝔤) (v : M) : M :=
  rho_phi k G 𝔤 D W lieAction_phi lieToD x v

end Equivariant


section DAffine

universe u_dxmod u_aag

variable (k : Type u_aag) [Field k]
         (K : Type u_aag) [Group K]
         (𝔨 : Type u_aag) [LieRing 𝔨] [LieAlgebra k 𝔨]
         (D : Type u_aag) [Ring D] [Algebra k D]

class IsDaffine (DXMod : Type*) [Category.{u_dxmod} DXMod] (X : Type*) : Prop where
  isNoetherian_DX : IsNoetherian D D
  globalSections_equiv : Nonempty (DXMod ≌ ModuleCat.{u_dxmod} D)

structure IsAffineAlgebraicGroup (G : Type u_aag) [Group G] : Prop where
  fg : Group.FG G

class IsAntidominant {k' : Type*} [Field k'] (𝔥star : Type*)
    (posRoots : Set 𝔥star) (pairing : 𝔥star → 𝔥star → k') (lam : 𝔥star) : Prop where
  not_pos_int_pairing : ∀ α ∈ posRoots, ¬(∃ n : ℕ, n > 0 ∧ pairing lam α = (n : k'))

def StrongKEquivDModPred (lieToD : 𝔨 →ₗ⁅k⁆ D) : ObjectProperty (ModuleCat.{u_aag} D) := fun M => by
  letI : Module k M := Module.compHom M (algebraMap k D)
  exact ∃ (groupAct : K →* (M ≃ₗ[k] M))
    (_ : ∀ (g : K) (d : D) (m : M), groupAct g (d • m) = d • (groupAct g m))
    (liePhi : 𝔨 →ₗ[k] Module.End k M)
    (_ : ∀ (x y : 𝔨), liePhi ⁅x, y⁆ = liePhi x * liePhi y - liePhi y * liePhi x),
    ∀ (x : 𝔨) (v : M), liePhi x v = (lieToD x) • v

def CompatibleKActionPred (lieToD : 𝔨 →ₗ⁅k⁆ D) (Ad : K →* (𝔨 ≃ₗ[k] 𝔨)) :
    ObjectProperty (ModuleCat.{u_aag} D) := fun M => by
  letI : Module k M := Module.compHom M (algebraMap k D)
  exact ∃ (groupAct : K →* (M ≃ₗ[k] M))
    (_ : ∀ (m : M), (Submodule.span k (Set.range (fun g => (groupAct g : M ≃ₗ[k] M) m))).FG)
    (lieAct : 𝔨 →ₗ[k] Module.End k M),

    (∀ (x : 𝔨) (v : M), lieAct x v = (lieToD x) • v) ∧


    (∀ (g : K) (x : 𝔨) (v : M),
      (groupAct g) ((lieAct x) ((groupAct g).symm v)) = (lieAct (Ad g x)) v)



structure BBLocalizationData (k' : Type u_aag) [Field k'] where
  G : Type u_aag
  [grpG : Group G]
  K : Type u_aag
  [grpK : Group K]
  iK : K →* G
  𝔤 : Type u_aag
  [lieRing_𝔤 : LieRing 𝔤]
  [lieAlg_𝔤 : LieAlgebra k' 𝔤]
  𝔨 : Type u_aag
  [lieRing_𝔨 : LieRing 𝔨]
  [lieAlg_𝔨 : LieAlgebra k' 𝔨]
  ι𝔨 : 𝔨 →ₗ⁅k'⁆ 𝔤
  𝔥 : Type u_aag
  [lieRing_𝔥 : LieRing 𝔥]
  [lieAlg_𝔥 : LieAlgebra k' 𝔥]
  ι𝔥 : 𝔥 →ₗ⁅k'⁆ 𝔤
  D : Type u_aag
  [ring_D : Ring D]
  [alg_D : Algebra k' D]
  lieToD : 𝔤 →ₗ⁅k'⁆ D
  𝔥star : Type u_aag
  [add_𝔥star : AddCommGroup 𝔥star]
  [mod_𝔥star : Module k' 𝔥star]
  duality : 𝔥 →ₗ[k'] 𝔥star →ₗ[k'] k'
  roots : Set 𝔥star
  posRoots : Set 𝔥star
  lam : 𝔥star
  FlagVariety : Type u_aag
  [isNoetherian_D : IsNoetherian D D]
  aag_K : IsAffineAlgebraicGroup K
  Ad_K : K →* (𝔨 ≃ₗ[k'] 𝔨)

attribute [instance] BBLocalizationData.grpG BBLocalizationData.grpK
  BBLocalizationData.lieRing_𝔤 BBLocalizationData.lieAlg_𝔤
  BBLocalizationData.lieRing_𝔨 BBLocalizationData.lieAlg_𝔨
  BBLocalizationData.lieRing_𝔥 BBLocalizationData.lieAlg_𝔥
  BBLocalizationData.ring_D BBLocalizationData.alg_D
  BBLocalizationData.add_𝔥star BBLocalizationData.mod_𝔥star
  BBLocalizationData.isNoetherian_D




def BBLocalizationData.IsAntidominant {k' : Type u_aag} [Field k']
    (bd : BBLocalizationData k') : Prop :=
  ∀ α ∈ bd.posRoots, ∀ hv : bd.𝔥, ¬(∃ n : ℕ, n > 0 ∧ (bd.duality hv) (bd.lam - n • α) = 0)

def IsKEquivDModBB {k' : Type u_aag} [Field k']
    (bd : BBLocalizationData k') : ObjectProperty (ModuleCat.{u_aag} bd.D) := fun M =>
  let _instk : Module k' M := Module.compHom M (algebraMap k' bd.D)
  ∃ (groupAction : bd.K →* (M ≃ₗ[k'] M)),
    (∀ (g : bd.K) (d : bd.D) (m : M), groupAction g (d • m) = d • (groupAction g m)) ∧
    ∃ (lieAction : bd.𝔨 →ₗ[k'] Module.End k' M),
      (∀ (x y : bd.𝔨), lieAction ⁅x, y⁆ =
        lieAction x * lieAction y - lieAction y * lieAction x) ∧
      (∀ (x : bd.𝔨) (v : M), lieAction x v = (bd.lieToD (bd.ι𝔨 x)) • v)

def IsGKModBB {k' : Type u_aag} [Field k']
    (bd : BBLocalizationData k') : ObjectProperty (ModuleCat.{u_aag} bd.D) := fun M => by
  letI : Module k' M := Module.compHom M (algebraMap k' bd.D)
  exact ∃ (groupAct : bd.K →* (M ≃ₗ[k'] M))
    (_ : ∀ (m : M), (Submodule.span k' (Set.range (fun g => (groupAct g : M ≃ₗ[k'] M) m))).FG)
    (lieAct : bd.𝔨 →ₗ[k'] Module.End k' M),

    (∀ (x : bd.𝔨) (v : M), lieAct x v = (bd.lieToD (bd.ι𝔨 x)) • v) ∧

    (∀ (g : bd.K) (x : bd.𝔨) (v : M),
      (groupAct g) ((lieAct x) ((groupAct g).symm v)) = (lieAct (bd.Ad_K g x)) v)

lemma isKEquivDModBB_eq_strongKEquivDModPred {k' : Type u_aag} [Field k']
    (bd : BBLocalizationData k') :
    IsKEquivDModBB bd = StrongKEquivDModPred k' bd.K bd.𝔨 bd.D (bd.lieToD.comp bd.ι𝔨) := by
  ext M
  simp only [IsKEquivDModBB, StrongKEquivDModPred]
  constructor
  · rintro ⟨ga, hDlin, la, hlie, hact⟩; exact ⟨ga, hDlin, la, hlie, hact⟩
  · rintro ⟨ga, hDlin, la, hlie, hact⟩; exact ⟨ga, hDlin, la, hlie, hact⟩

lemma isGKModBB_eq_compatibleKActionPred {k' : Type u_aag} [Field k']
    (bd : BBLocalizationData k') :
    IsGKModBB bd = CompatibleKActionPred k' bd.K bd.𝔨 bd.D (bd.lieToD.comp bd.ι𝔨) bd.Ad_K := by
  ext M
  simp only [IsGKModBB, CompatibleKActionPred]
  constructor
  · rintro ⟨ga, hfin, la, hcoinc, hcompat⟩; exact ⟨ga, hfin, la, hcoinc, hcompat⟩
  · rintro ⟨ga, hfin, la, hcoinc, hcompat⟩; exact ⟨ga, hfin, la, hcoinc, hcompat⟩




end DAffine

end DModulesII
