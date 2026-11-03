/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Rank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Algebra.Lie.Weights.RootSystem

noncomputable section

universe u v

structure BorelWeilData where
  (k : Type u)
  [field_k : Field k]
  (𝔤 : Type v)
  [lieRing : LieRing 𝔤]
  [lieAlgebra : LieAlgebra k 𝔤]
  (G : Type*)
  [group_G : Group G]
  (WeightLattice : Type*)
  [wl_addCommGroup : AddCommGroup WeightLattice]
  (IsDominant : WeightLattice → Prop)
  (IrrepModule : WeightLattice → Type*)
  [irrepAddCommGroup : ∀ w, AddCommGroup (IrrepModule w)]
  [irrepModule : ∀ w, Module k (IrrepModule w)]
  [irrepFinDim : ∀ w, Module.Finite k (IrrepModule w)]
  (irrepRep : ∀ w, Representation k G (IrrepModule w))

  (FlagVar : Type*)
  (GlobalSections : WeightLattice → Type*)
  [sectionsAddCommGroup : ∀ w, AddCommGroup (GlobalSections w)]
  [sectionsModule : ∀ w, Module k (GlobalSections w)]
  (sectionsRep : ∀ w, Representation k G (GlobalSections w))

attribute [instance] BorelWeilData.field_k BorelWeilData.lieRing BorelWeilData.lieAlgebra
  BorelWeilData.group_G BorelWeilData.wl_addCommGroup BorelWeilData.irrepAddCommGroup
  BorelWeilData.irrepModule BorelWeilData.irrepFinDim BorelWeilData.sectionsAddCommGroup
  BorelWeilData.sectionsModule






structure ParabolicBorelWeilData extends BorelWeilData where
  (SimpleRoots : Type*)
  (S : Set SimpleRoots)
  (coroot_pairing : WeightLattice → SimpleRoots → ℤ)
  (PartialFlagVar : Type*)
  (projection : FlagVar → PartialFlagVar)
  (PartialFlagSections : WeightLattice → Type*)
  [pfSectionsAddCommGroup : ∀ w, AddCommGroup (PartialFlagSections w)]
  [pfSectionsModule : ∀ w, Module k (PartialFlagSections w)]
  (pfSectionsRep : ∀ w, Representation k G (PartialFlagSections w))

attribute [instance] ParabolicBorelWeilData.pfSectionsAddCommGroup
  ParabolicBorelWeilData.pfSectionsModule

def ParabolicBorelWeilData.IsOrthogonalToS (D : ParabolicBorelWeilData)
    (μ : D.WeightLattice) : Prop :=
  ∀ i : D.SimpleRoots, i ∈ D.S → D.coroot_pairing μ i = 0



def nilpotentCone (k : Type*) (𝔤 : Type*) [CommRing k] [LieRing 𝔤] [LieAlgebra k 𝔤] :
    Set 𝔤 :=
  {x : 𝔤 | IsNilpotent (LieAlgebra.ad k 𝔤 x)}

structure SpringerResolutionData where
  (k : Type u)
  [field_k : Field k]
  (𝔤 : Type v)
  [lieRing : LieRing 𝔤]
  [lieAlgebra : LieAlgebra k 𝔤]
  (FlagVar : Type*)
  (CotangentBundle : Type*)
  (springerMap : CotangentBundle → 𝔤)
  (springerMap_mem_nilpotentCone :
    ∀ y : CotangentBundle, springerMap y ∈ nilpotentCone k 𝔤)
  (bundleProjection : CotangentBundle → FlagVar)
  (cotangentBundle_ext : ∀ y₁ y₂ : CotangentBundle,
    bundleProjection y₁ = bundleProjection y₂ →
    springerMap y₁ = springerMap y₂ → y₁ = y₂)
  (IsRegularNilpotent : 𝔤 → Prop)
  (regularNilpotent_mem : ∀ e, IsRegularNilpotent e → e ∈ nilpotentCone k 𝔤)
  (regularNilpotent_nonempty : ∃ e, IsRegularNilpotent e)
  (isInBorel : 𝔤 → FlagVar → Prop)
  (isInBorel_of_springerMap : ∀ y : CotangentBundle,
    isInBorel (springerMap y) (bundleProjection y))
  (rho_dual : 𝔤)

attribute [instance] SpringerResolutionData.field_k SpringerResolutionData.lieRing
  SpringerResolutionData.lieAlgebra



def SpringerResolutionData.closedEmbedding (D : SpringerResolutionData) :
    D.CotangentBundle → D.FlagVar × D.𝔤 :=
  fun y => (D.bundleProjection y, D.springerMap y)

theorem SpringerResolutionData.closedEmbedding_eq (D : SpringerResolutionData)
    (y : D.CotangentBundle) :
    D.closedEmbedding y = (D.bundleProjection y, D.springerMap y) := rfl



theorem SpringerResolutionData.closedEmbedding_injective (D : SpringerResolutionData) :
    Function.Injective D.closedEmbedding := by
  intro y₁ y₂ h
  simp only [closedEmbedding, Prod.mk.injEq] at h
  exact D.cotangentBundle_ext y₁ y₂ h.1 h.2




noncomputable def SpringerResolutionData.mk' (k : Type*) [Field k] (𝔤 : Type*)
    [LieRing 𝔤] [LieAlgebra k 𝔤]
    (FlagVar CotangentBundle : Type*)
    (springerMap : CotangentBundle → 𝔤)
    (bundleProjection : CotangentBundle → FlagVar)
    (IsRegularNilpotent : 𝔤 → Prop)
    (hSpringerMap_mem : ∀ y : CotangentBundle, springerMap y ∈ nilpotentCone k 𝔤)
    (hCotangentBundle_ext : ∀ y₁ y₂ : CotangentBundle,
      bundleProjection y₁ = bundleProjection y₂ →
      springerMap y₁ = springerMap y₂ → y₁ = y₂)
    (hRegNilpMem : ∀ e, IsRegularNilpotent e → e ∈ nilpotentCone k 𝔤)
    (hRegNilpNonempty : ∃ e, IsRegularNilpotent e)
    (isInBorel : 𝔤 → FlagVar → Prop)
    (hIsInBorel_of_springerMap : ∀ y : CotangentBundle,
      isInBorel (springerMap y) (bundleProjection y))
    (rho_dual : 𝔤) :
    SpringerResolutionData where
  k := k
  𝔤 := 𝔤
  FlagVar := FlagVar
  CotangentBundle := CotangentBundle
  springerMap := springerMap
  springerMap_mem_nilpotentCone := hSpringerMap_mem
  bundleProjection := bundleProjection
  cotangentBundle_ext := hCotangentBundle_ext
  IsRegularNilpotent := IsRegularNilpotent
  regularNilpotent_mem := hRegNilpMem
  regularNilpotent_nonempty := hRegNilpNonempty
  isInBorel := isInBorel
  isInBorel_of_springerMap := hIsInBorel_of_springerMap
  rho_dual := rho_dual



structure SkewSymmetricBilinearForm (k : Type*) (M : Type*) [CommRing k]
    [AddCommGroup M] [Module k M] where
  bilin : M →ₗ[k] M →ₗ[k] k
  skew_symm : ∀ x y : M, bilin x y = - bilin y x

def SkewSymmetricBilinearForm.IsNondegenerate {k : Type*} {M : Type*} [CommRing k]
    [AddCommGroup M] [Module k M] (ω : SkewSymmetricBilinearForm k M) : Prop :=
  ∀ x : M, (∀ y : M, ω.bilin x y = 0) → x = 0

def kirillovKostantForm (k : Type*) (𝔤 : Type*) [CommRing k]
    [LieRing 𝔤] [LieAlgebra k 𝔤]
    (f : 𝔤 →ₗ[k] k) : SkewSymmetricBilinearForm k 𝔤 where
  bilin := {
    toFun := fun y => {
      toFun := fun z => f ⁅y, z⁆
      map_add' := by intro z₁ z₂; rw [lie_add, map_add]
      map_smul' := by
        intro r z; rw [lie_smul, map_smul]; simp [RingHom.id_apply, smul_eq_mul]
    }
    map_add' := by
      intro y₁ y₂; ext z
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
      rw [add_lie, map_add]
    map_smul' := by
      intro r y; ext z
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      rw [smul_lie, map_smul, smul_eq_mul]
  }
  skew_symm := by
    intro x y
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← lie_skew, map_neg]

def coadjointStabilizer (k : Type*) (𝔤 : Type*) [CommRing k]
    [LieRing 𝔤] [LieAlgebra k 𝔤]
    (f : 𝔤 →ₗ[k] k) : Submodule k 𝔤 where
  carrier := {x : 𝔤 | ∀ y : 𝔤, f ⁅x, y⁆ = 0}
  add_mem' := by
    intro a b ha hb y
    rw [add_lie, map_add, ha y, hb y, add_zero]
  zero_mem' := by
    intro y; rw [zero_lie, map_zero]
  smul_mem' := by
    intro r a ha y
    rw [smul_lie, map_smul, ha y, smul_zero]

theorem kirillovKostant_kernel (k : Type*) (𝔤 : Type*) [CommRing k]
    [LieRing 𝔤] [LieAlgebra k 𝔤]
    (f : 𝔤 →ₗ[k] k) (x : 𝔤) :
    (∀ y : 𝔤, (kirillovKostantForm k 𝔤 f).bilin x y = 0) ↔
    x ∈ coadjointStabilizer k 𝔤 f := by
  exact Iff.rfl

theorem kirillovKostant_closed (k : Type*) (𝔤 : Type*) [CommRing k]
    [LieRing 𝔤] [LieAlgebra k 𝔤]
    (f : 𝔤 →ₗ[k] k) (x y z : 𝔤) :
    f ⁅y, ⁅x, z⁆⁆ + f ⁅z, ⁅y, x⁆⁆ + f ⁅x, ⁅z, y⁆⁆ = 0 := by
  have jacobi := lie_jacobi x z y
  have h := congr_arg f jacobi
  simp only [map_add, map_zero] at h
  set a := f ⁅x, ⁅z, y⁆⁆
  set b := f ⁅z, ⁅y, x⁆⁆
  set c := f ⁅y, ⁅x, z⁆⁆
  calc c + b + a = a + b + c := by ring
    _ = 0 := h

structure CoadjointOrbitData (k : Type*) (𝔤 : Type*) [CommRing k]
    [LieRing 𝔤] [LieAlgebra k 𝔤] where
  G : Type*
  [instGroup : Group G]
  Ad : G →* (𝔤 ≃ₗ[k] 𝔤)
  Ad_preserves_bracket : ∀ (g : G) (x y : 𝔤), Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆
  coadjointAction : G → (𝔤 →ₗ[k] k) → (𝔤 →ₗ[k] k)
  coadjoint_formula : ∀ (g : G) (f : 𝔤 →ₗ[k] k) (x : 𝔤),
    coadjointAction g f x = f (Ad g⁻¹ x)

attribute [instance] CoadjointOrbitData.instGroup

variable {k' : Type*} {𝔤' : Type*} [CommRing k'] [LieRing 𝔤'] [LieAlgebra k' 𝔤']

def CoadjointOrbitData.orbit (data : CoadjointOrbitData k' 𝔤') (f : 𝔤' →ₗ[k'] k') :
    Set (𝔤' →ₗ[k'] k') :=
  Set.range (fun g => data.coadjointAction g f)

theorem CoadjointOrbitData.mem_orbit_iff (data : CoadjointOrbitData k' 𝔤')
    (f ξ : 𝔤' →ₗ[k'] k') :
    ξ ∈ data.orbit f ↔ ∃ g : data.G, data.coadjointAction g f = ξ := by
  simp [CoadjointOrbitData.orbit, Set.mem_range]

lemma CoadjointOrbitData.Ad_inv_cancel_left (data : CoadjointOrbitData k' 𝔤')
    (g : data.G) (x : 𝔤') : (data.Ad g⁻¹) ((data.Ad g) x) = x := by
  have h : data.Ad g⁻¹ * data.Ad g = 1 := by
    rw [← data.Ad.map_mul, inv_mul_cancel, data.Ad.map_one]
  calc (data.Ad g⁻¹) ((data.Ad g) x)
      = (data.Ad g⁻¹ * data.Ad g) x := (LinearEquiv.mul_apply _ _ _).symm
    _ = (1 : 𝔤' ≃ₗ[k'] 𝔤') x := by rw [h]
    _ = x := by simp

theorem kirillovKostant_G_invariant (data : CoadjointOrbitData k' 𝔤')
    (g : data.G) (f : 𝔤' →ₗ[k'] k') (y z : 𝔤') :
    data.coadjointAction g f ⁅data.Ad g y, data.Ad g z⁆ = f ⁅y, z⁆ := by
  rw [data.coadjoint_formula, ← data.Ad_preserves_bracket]
  congr 1
  exact data.Ad_inv_cancel_left g ⁅y, z⁆

theorem kirillovKostant_symplectic (data : CoadjointOrbitData k' 𝔤')
    (f : 𝔤' →ₗ[k'] k') :

    (∀ y z : 𝔤', f ⁅y, z⁆ = - f ⁅z, y⁆) ∧


    (∀ x : 𝔤', (∀ y : 𝔤', f ⁅x, y⁆ = 0) ↔ x ∈ coadjointStabilizer k' 𝔤' f) ∧

    (∀ (g : data.G) (y z : 𝔤'),
      data.coadjointAction g f ⁅data.Ad g y, data.Ad g z⁆ = f ⁅y, z⁆) ∧

    (∀ x y z : 𝔤', f ⁅y, ⁅x, z⁆⁆ + f ⁅z, ⁅y, x⁆⁆ + f ⁅x, ⁅z, y⁆⁆ = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro y z
    have := (kirillovKostantForm k' 𝔤' f).skew_symm y z
    simp only [kirillovKostantForm, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact this
  ·
    intro x
    exact kirillovKostant_kernel k' 𝔤' f x
  ·
    intro g y z
    exact kirillovKostant_G_invariant data g f y z
  ·
    intro x y z
    exact kirillovKostant_closed k' 𝔤' f x y z

def nilpotentCone_singularLocus (k : Type*) (𝔤 : Type*)
    [CommRing k] [LieRing 𝔤] [LieAlgebra k 𝔤] [Module.Finite k 𝔤] [Module.Free k 𝔤] :
    Set 𝔤 :=
  {x ∈ nilpotentCone k 𝔤 |
    Module.finrank k (LinearMap.ker (LieAlgebra.ad k 𝔤 x : 𝔤 →ₗ[k] 𝔤)) ≠
      LieAlgebra.rank k 𝔤}

structure NilpotentConeOrbitData (k : Type*) (𝔤 : Type*)
    [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [Module.Finite k 𝔤] [Module.Free k 𝔤] [LieAlgebra.IsSemisimple k 𝔤] where
  dimVariety : Set 𝔤 → ℕ
  dim_nilpCone_eq : dimVariety (nilpotentCone k 𝔤) = Module.finrank k 𝔤 - LieAlgebra.rank k 𝔤
  dim_nilpCone_even : Even (dimVariety (nilpotentCone k 𝔤))
  dim_singLocus_even : Even (dimVariety (nilpotentCone_singularLocus k 𝔤))
  dim_singLocus_lt : dimVariety (nilpotentCone_singularLocus k 𝔤) < dimVariety (nilpotentCone k 𝔤)








theorem even_sub_even_of_lt_ge_two {m n : ℕ} (hm : Even m) (hn : Even n) (hlt : n < m) :
    m - n ≥ 2 := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  omega


structure NilpotentConeCoordRingData (k : Type*) (𝔤 : Type*)
    [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤] where
  SymAlg : Type*
  [symAlgCommRing : CommRing SymAlg]
  [symAlgAlgebra : Algebra k SymAlg]
  eval_𝔤 : SymAlg →ₐ[k] (𝔤 → k)
  vanishingIdeal : Ideal SymAlg
  mem_vanishingIdeal : ∀ f : SymAlg,
    f ∈ vanishingIdeal ↔ ∀ x ∈ nilpotentCone k 𝔤, eval_𝔤 f x = 0
  [symAlg_isNoetherian : IsNoetherianRing SymAlg]
  [vanishingIdeal_isPrime : vanishingIdeal.IsPrime]

attribute [instance] NilpotentConeCoordRingData.symAlgCommRing
  NilpotentConeCoordRingData.symAlgAlgebra
  NilpotentConeCoordRingData.symAlg_isNoetherian
  NilpotentConeCoordRingData.vanishingIdeal_isPrime

abbrev NilpotentConeCoordRingData.coordRing {k : Type*} {𝔤 : Type*}
    [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    (D : NilpotentConeCoordRingData k 𝔤) : Type* :=
  D.SymAlg ⧸ D.vanishingIdeal

theorem nilpotentCone_coordRing_isDomain
    {k : Type*} {𝔤 : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [LieAlgebra.IsSemisimple k 𝔤] [Module.Finite k 𝔤]
    (D : NilpotentConeCoordRingData k 𝔤) : IsDomain D.coordRing :=
  Ideal.Quotient.isDomain D.vanishingIdeal

instance NilpotentConeCoordRingData.instIsDomainCoordRing
    {k : Type*} {𝔤 : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [LieAlgebra.IsSemisimple k 𝔤] [Module.Finite k 𝔤]
    (D : NilpotentConeCoordRingData k 𝔤) : IsDomain D.coordRing :=
  nilpotentCone_coordRing_isDomain D

instance NilpotentConeCoordRingData.instIsNoetherianCoordRing
    {k : Type*} {𝔤 : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    (D : NilpotentConeCoordRingData k 𝔤) : IsNoetherianRing D.coordRing :=
  Ideal.Quotient.isNoetherianRing D.vanishingIdeal

def SatisfiesSerreR1 (R : Type*) [CommRing R] : Prop :=
  ∀ (𝔭 : Ideal R) [𝔭.IsPrime], 𝔭.height ≤ 1 →
    IsRegularLocalRing (Localization.AtPrime 𝔭)

def SatisfiesSerreS2 (R : Type*) [CommRing R] : Prop :=
  ∀ (𝔭 : Ideal R) [𝔭.IsPrime], 𝔭.height ≥ 2 →
    ∃ (a b : Localization.AtPrime 𝔭),
      a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) ∧
      (∀ x : Localization.AtPrime 𝔭, x * a = 0 → x = 0) ∧
      b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) ∧
      (∀ x : Localization.AtPrime 𝔭, x * b ∈ Ideal.span {a} → x ∈ Ideal.span {a})





theorem normalVariety_singular_locus_codim_ge_two
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (𝔭 : Ideal R) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1) :
    IsRegularLocalRing (Localization.AtPrime 𝔭) := by
  set S := Localization.AtPrime 𝔭

  haveI : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors

  have hdim : ringKrullDim S = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 S]
    exact_mod_cast h𝔭

  have hunique : ∀ P : Ideal S, P ≠ ⊥ → P.IsPrime →
      P = IsLocalRing.maximalIdeal S := by
    intro P hP hPprime
    haveI := hPprime
    have hle := IsLocalRing.le_maximalIdeal (R := S) hPprime.ne_top
    by_contra hne
    have hlt : P < IsLocalRing.maximalIdeal S := lt_of_le_of_ne hle hne
    have h_bot_lt_P : (⊥ : Ideal S) < P := bot_lt_iff_ne_bot.mpr hP
    have h1 : (⊥ : Ideal S).primeHeight + 1 ≤ P.primeHeight :=
      Ideal.primeHeight_add_one_le_of_lt h_bot_lt_P
    have h2 : P.primeHeight + 1 ≤ (IsLocalRing.maximalIdeal S).primeHeight :=
      Ideal.primeHeight_add_one_le_of_lt hlt
    have h0 : (⊥ : Ideal S).primeHeight = 0 := by
      rw [Ideal.primeHeight_eq_zero_iff]
      rw [IsDomain.minimalPrimes_eq_singleton_bot]
      exact Set.mem_singleton _
    have hge2 : (IsLocalRing.maximalIdeal S).primeHeight ≥ 2 := by
      calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ P.primeHeight + 1 := by gcongr; rw [← h0]; exact h1
        _ ≤ (IsLocalRing.maximalIdeal S).primeHeight := h2
    have hmaxht : (IsLocalRing.maximalIdeal S).primeHeight = 1 := by
      have := IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim (R := S)
      rw [hdim] at this
      exact_mod_cast this
    rw [hmaxht] at hge2
    exact absurd hge2 (by norm_num)

  have hcond : IsIntegrallyClosed S ∧
      ∀ P : Ideal S, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal S :=
    ⟨inferInstance, hunique⟩
  haveI : IsPrincipalIdealRing S :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain S).out 3 0).mp hcond
  exact IsRegularLocalRing.instOfIsLocalRingOfIsDomainOfIsPrincipalIdealRing _




def IsGradedAlgEquiv {k : Type*} [CommSemiring k]
    {A : Type*} [Semiring A] [Algebra k A]
    {B : Type*} [Semiring B] [Algebra k B]
    (𝒜 : ℕ → Submodule k A) (ℬ : ℕ → Submodule k B)
    (e : A ≃ₐ[k] B) : Prop :=
  ∀ n : ℕ, ∀ a : A, a ∈ 𝒜 n ↔ e a ∈ ℬ n

structure ResolutionData (k : Type*) [Field k] where
  OY : Type*
  [oyCommRing : CommRing OY]
  [oyIsDomain : IsDomain OY]
  [oyAlgebra : Algebra k OY]
  [oyIntegrallyClosed : IsIntegrallyClosed OY]
  [oyNoetherian : IsNoetherianRing OY]
  OX : Type*
  [oxCommRing : CommRing OX]
  [oxIsDomain : IsDomain OX]
  [oxAlgebra : Algebra k OX]
  pStar : OY →+* OX
  hProper : letI : Algebra OY OX := pStar.toAlgebra; Algebra.IsIntegral OY OX
  hFracIso : ∃ (φ : FractionRing OY ≃+* FractionRing OX),
    ∀ r : OY, φ (algebraMap OY (FractionRing OY) r) =
      algebraMap OX (FractionRing OX) (pStar r)

attribute [instance] ResolutionData.oyCommRing ResolutionData.oyIsDomain
  ResolutionData.oyAlgebra ResolutionData.oyIntegrallyClosed
  ResolutionData.oyNoetherian ResolutionData.oxCommRing
  ResolutionData.oxIsDomain ResolutionData.oxAlgebra

noncomputable def ResolutionData.mk' (k : Type*) [Field k]
    (OY : Type*) [CommRing OY] [IsDomain OY] [Algebra k OY]
    [IsIntegrallyClosed OY] [IsNoetherianRing OY]
    (OX : Type*) [CommRing OX] [IsDomain OX] [Algebra k OX]
    (pStar : OY →+* OX)
    (hProper : letI : Algebra OY OX := pStar.toAlgebra; Algebra.IsIntegral OY OX)
    (hFracIso : ∃ (φ : FractionRing OY ≃+* FractionRing OX),
      ∀ r : OY, φ (algebraMap OY (FractionRing OY) r) =
        algebraMap OX (FractionRing OX) (pStar r)) : ResolutionData k where
  OY := OY
  OX := OX
  pStar := pStar
  hProper := hProper
  hFracIso := hFracIso

theorem ResolutionData.pStar_injective {k : Type*} [Field k]
    (R : ResolutionData k) : Function.Injective R.pStar := by
  obtain ⟨φ, hφ⟩ := R.hFracIso
  intro a b hab
  have ha := hφ a
  have hb := hφ b
  rw [hab] at ha
  rw [← hb] at ha
  exact IsFractionRing.injective R.OY (FractionRing R.OY) (φ.injective ha)

theorem resolution_pullback_surjective {k : Type*} [Field k]
    (R : ResolutionData k) : Function.Surjective R.pStar := by
  letI : Algebra R.OY R.OX := R.pStar.toAlgebra
  intro f

  have hf : IsIntegral R.OY f := R.hProper.isIntegral f

  obtain ⟨φ, hφ⟩ := R.hFracIso

  let ψ : R.OX →+* FractionRing R.OY :=
    φ.symm.toRingHom.comp (algebraMap R.OX (FractionRing R.OX))

  have hcomp : (algebraMap R.OY (FractionRing R.OY)).comp (RingHom.id R.OY) =
      ψ.comp (algebraMap R.OY R.OX) := by
    ext r
    simp only [RingHom.comp_apply, RingHom.id_apply, ψ, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [show algebraMap R.OY R.OX r = R.pStar r from rfl, ← hφ r]
    simp [RingEquiv.symm_apply_apply]

  have hf_integral : IsIntegral R.OY (ψ f) :=
    hf.map_of_comp_eq (RingHom.id R.OY) ψ hcomp

  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff).mp hf_integral

  refine ⟨y, ?_⟩
  have h1 : φ (algebraMap R.OY (FractionRing R.OY) y) =
      algebraMap R.OX (FractionRing R.OX) f := by
    rw [hy]
    simp only [ψ, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply,
      RingHom.coe_coe, RingEquiv.apply_symm_apply]
  have h2 : algebraMap R.OX (FractionRing R.OX) (R.pStar y) =
      algebraMap R.OX (FractionRing R.OX) f := by
    rw [← hφ y, h1]
  exact IsFractionRing.injective R.OX (FractionRing R.OX) h2

theorem resolution_pullback_isIso {k : Type*} [Field k]
    (R : ResolutionData k) : Function.Bijective R.pStar :=
  ⟨R.pStar_injective, resolution_pullback_surjective R⟩

lemma graded_map_reflects_mem {k : Type*} [Field k]
    {R : Type*} [CommRing R] [Algebra k R]
    {S : Type*} [CommRing S] [Algebra k S]
    (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule k S) [GradedAlgebra ℬ]
    (f : R →ₐ[k] S)
    (hf_grade : ∀ n, ∀ a ∈ 𝒜 n, f a ∈ ℬ n)
    (hf_inj : Function.Injective f)
    (n : ℕ) (a : R) (ha : f a ∈ ℬ n) : a ∈ 𝒜 n := by

  have naturality : ∀ (m : ℕ) (b : R),
      f (↑((DirectSum.decompose 𝒜 b) m)) = ↑((DirectSum.decompose ℬ (f b)) m) := by
    intro m b
    set 𝒜_sub := fun i => ↥(𝒜 i)

    let φ₁ : DirectSum ℕ 𝒜_sub →+ S :=
      { toFun := fun x => f (↑(x m) : R),
        map_zero' := by simp,
        map_add' := fun x y => by simp [DirectSum.add_apply, map_add] }
    let φ₂ : DirectSum ℕ 𝒜_sub →+ S :=
      { toFun := fun x => ↑((DirectSum.decompose ℬ (f ((DirectSum.decompose 𝒜).symm x))) m),
        map_zero' := by simp,
        map_add' := fun x y => by
          have hsymm := (DirectSum.decomposeAddEquiv 𝒜).symm.map_add x y
          simp only [DirectSum.decomposeAddEquiv_symm_apply] at hsymm
          rw [hsymm, map_add, DirectSum.decompose_add, DirectSum.add_apply]
          simp }
    have h_eq : φ₁ = φ₂ := DirectSum.addHom_ext (fun i y => by
      simp only [φ₁, φ₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, DirectSum.decompose_symm_of]
      by_cases him : i = m
      · subst him
        rw [DirectSum.of_eq_same]
        exact (DirectSum.decompose_of_mem_same ℬ (hf_grade _ (↑y) y.prop)).symm
      · have : (DirectSum.of 𝒜_sub i y) m = 0 :=
          DirectSum.of_eq_of_ne (β := 𝒜_sub) i m y (fun h => him (h.symm))
        rw [this, ZeroMemClass.coe_zero, map_zero]
        exact (DirectSum.decompose_of_mem_ne ℬ (hf_grade i (↑y) y.prop) him).symm)
    have := congr_fun (congr_arg DFunLike.coe h_eq) (DirectSum.decompose 𝒜 b)
    simp only [φ₁, φ₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rw [Equiv.symm_apply_apply] at this
    exact this

  suffices h_zero : ∀ m : ℕ, m ≠ n → (DirectSum.decompose 𝒜 a) m = 0 by
    suffices ha_eq : a = ↑((DirectSum.decompose 𝒜 a) n) by
      rw [ha_eq]; exact SetLike.coe_mem _
    apply (DirectSum.decompose 𝒜).injective
    rw [DirectSum.decompose_coe 𝒜 ((DirectSum.decompose 𝒜 a) n)]
    apply DFinsupp.ext; intro m
    by_cases hm : m = n
    · cases hm; rw [DirectSum.of_eq_same]
    · rw [h_zero m hm, DirectSum.of_eq_of_ne (β := fun i => ↥(𝒜 i)) n m _ hm]
  intro m hm
  have h1 : f (↑((DirectSum.decompose 𝒜 a) m)) = 0 := by
    rw [naturality m a, DirectSum.decompose_of_mem_ne ℬ ha (Ne.symm hm)]
  have h2 : (↑((DirectSum.decompose 𝒜 a) m) : R) = 0 := hf_inj (by rw [h1, map_zero])
  exact Subtype.val_injective h2

theorem springer_pullback_isIso (D : SpringerResolutionData)
    (ON : Type*) [CommRing ON] [IsDomain ON] [Algebra D.k ON]
    [IsIntegrallyClosed ON] [IsNoetherianRing ON]
    (𝒩_grade : ℕ → Submodule D.k ON) [GradedAlgebra 𝒩_grade]
    (OTF : Type*) [CommRing OTF] [IsDomain OTF] [Algebra D.k OTF]
    (TF_grade : ℕ → Submodule D.k OTF) [GradedAlgebra TF_grade]
    (pstar : ON →ₐ[D.k] OTF)
    (hbirational : ∃ (φ : FractionRing ON ≃+* FractionRing OTF),
      ∀ r : ON, φ (algebraMap ON (FractionRing ON) r) =
        algebraMap OTF (FractionRing OTF) (pstar r))
    (hproper : letI : Algebra ON OTF := pstar.toRingHom.toAlgebra;
      Algebra.IsIntegral ON OTF)
    (hpstar_preserves_grade : ∀ n : ℕ, ∀ f : ON, f ∈ 𝒩_grade n → pstar f ∈ TF_grade n) :
    ∃ (e : ON ≃ₐ[D.k] OTF),
      (∀ f : ON, e f = pstar f) ∧ IsGradedAlgEquiv 𝒩_grade TF_grade e := by


  let RD : ResolutionData D.k :=
    { OY := ON
      OX := OTF
      pStar := pstar.toRingHom
      hProper := hproper
      hFracIso := hbirational }


  have hbij : Function.Bijective pstar := resolution_pullback_isIso RD

  refine ⟨AlgEquiv.ofBijective pstar hbij,
    fun f => AlgEquiv.ofBijective_apply pstar hbij f,
    fun n a => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  constructor
  ·
    exact hpstar_preserves_grade n a
  ·


    exact graded_map_reflects_mem 𝒩_grade TF_grade pstar hpstar_preserves_grade hbij.1 n a

end
