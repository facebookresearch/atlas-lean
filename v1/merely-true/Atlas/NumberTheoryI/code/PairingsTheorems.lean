/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Pairings
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Lattice

open Submodule LinearMap Module

noncomputable section

section AuxDefs

variable {K : Type*} [Field K]

def directSumBilinForm {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    (B₁ : V₁ →ₗ[K] V₁ →ₗ[K] K) (B₂ : V₂ →ₗ[K] V₂ →ₗ[K] K) :
    (V₁ × V₂) →ₗ[K] (V₁ × V₂) →ₗ[K] K :=
  LinearMap.mk₂ K
    (fun p q => B₁ p.1 q.1 + B₂ p.2 q.2)
    (by intros; simp [map_add, add_add_add_comm])
    (by intros; simp [map_smul, mul_add])
    (by intros; simp [map_add, add_add_add_comm])
    (by intros; simp [map_smul, mul_add])

end AuxDefs

def Submodule.localize {A : Type*} [CommRing A] {V : Type*} [AddCommGroup V] [Module A V]
    (S : Submonoid A) (M : Submodule A V) : Submodule A V where
  carrier := {v | ∃ s ∈ S, s • v ∈ M}
  add_mem' := by
    rintro a b ⟨s₁, hs₁, hsa⟩ ⟨s₂, hs₂, hsb⟩
    refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm s₁ s₂ a]
    exact M.add_mem (M.smul_mem s₂ hsa) (M.smul_mem s₁ hsb)
  zero_mem' := ⟨1, S.one_mem, by simp [M.zero_mem]⟩
  smul_mem' := by
    rintro c v ⟨s, hs, hsv⟩
    exact ⟨s, hs, by rw [smul_comm]; exact M.smul_mem _ hsv⟩

section Connection

variable
  {A : Type*} [CommRing A] [IsDomain A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

omit [IsDomain A] [IsFractionRing A K] in
theorem dualLattice_eq_dualSubmodule (φ : V →ₗ[K] V →ₗ[K] K) (M : Submodule A V) :
    dualLattice A K V φ M = BilinForm.dualSubmodule φ M := by
  ext v
  constructor
  · intro hv y hy
    exact Submodule.mem_one.mpr (hv y hy)
  · intro hv y hy
    exact Submodule.mem_one.mp (hv y hy)

end Connection

section DualBasis

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {ι : Type*} [DecidableEq ι] [Finite ι]

theorem prop_5_7_existence (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (b : Basis ι K V) :
    ∃ b' : Basis ι K V, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
  ⟨BilinForm.dualBasis B hB b, fun i j => BilinForm.apply_dualBasis_left hB b i j⟩

theorem prop_5_7_uniqueness (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (b : Basis ι K V)
    (b₁ b₂ : Basis ι K V)
    (h₁ : ∀ i j, B (b₁ i) (b j) = if j = i then 1 else 0)
    (h₂ : ∀ i j, B (b₂ i) (b j) = if j = i then 1 else 0) :
    ⇑b₁ = ⇑b₂ := by
  rw [← (BilinForm.dualBasis_eq_iff hB b (⇑b₁)).mpr h₁]
  rw [← (BilinForm.dualBasis_eq_iff hB b (⇑b₂)).mpr h₂]

end DualBasis

section DualBasisGeneral

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
  {ι : Type*} [DecidableEq ι] [Finite ι]

noncomputable def dualBasis_inM_of_perfectPairing
    (B : M →ₗ[A] M →ₗ[A] A) [B.IsPerfPair] (b : Basis ι A M) :
    Basis ι A M :=
  b.dualBasis.map B.toPerfPair.symm

theorem dualBasis_inM_of_perfectPairing_apply
    (B : M →ₗ[A] M →ₗ[A] A) [B.IsPerfPair]
    (b : Basis ι A M) (i j : ι) :
    B (dualBasis_inM_of_perfectPairing B b i) (b j) = if j = i then 1 else 0 := by
  unfold dualBasis_inM_of_perfectPairing
  rw [Basis.map_apply]
  have : B (B.toPerfPair.symm (b.dualBasis i)) (b j) = b.dualBasis i (b j) := by
    rw [← toPerfPair_apply, LinearEquiv.apply_symm_apply]
  rw [this]
  exact b.dualBasis_apply_self i j

theorem prop_5_7_existence_general (B : M →ₗ[A] M →ₗ[A] A) [B.IsPerfPair]
    (b : Basis ι A M) :
    ∃ b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
  ⟨dualBasis_inM_of_perfectPairing B b,
   fun i j => dualBasis_inM_of_perfectPairing_apply B b i j⟩

omit [Finite ι] in
theorem prop_5_7_uniqueness_general (B : M →ₗ[A] M →ₗ[A] A) [B.IsPerfPair]
    (b : Basis ι A M)
    (b₁ b₂ : Basis ι A M)
    (h₁ : ∀ i j, B (b₁ i) (b j) = if j = i then 1 else 0)
    (h₂ : ∀ i j, B (b₂ i) (b j) = if j = i then 1 else 0) :
    ⇑b₁ = ⇑b₂ := by
  funext i
  apply B.toPerfPair.injective
  apply b.ext
  intro j
  simp only [toPerfPair_apply]
  rw [h₁ i j, h₂ i j]

end DualBasisGeneral

section DualLatticeLattice

variable
  {A : Type*} [CommRing A] [IsDomain A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

omit [IsDomain A] [IsFractionRing A K] in
theorem dualSubmodule_antitone (B : V →ₗ[K] V →ₗ[K] K) :
    Antitone (BilinForm.dualSubmodule B : Submodule A V → Submodule A V) := by
  intro N₁ N₂ h x hx y hy
  exact hx y (h hy)

variable {ι : Type*} [DecidableEq ι] [Finite ι]

omit [IsDomain A] [IsFractionRing A K] in
theorem thm_5_12_dualSubmodule_free_lattice (B : V →ₗ[K] V →ₗ[K] K)
    (hB : B.Nondegenerate) (b : Basis ι K V) :
    BilinForm.dualSubmodule B (span A (Set.range b)) =
      span A (Set.range (BilinForm.dualBasis B hB b)) :=
  BilinForm.dualSubmodule_span_of_basis B hB b

omit [IsDomain A] [IsFractionRing A K] in
theorem thm_5_12_fg_key (B : V →ₗ[K] V →ₗ[K] K)
    (hB : B.Nondegenerate) (b : Basis ι K V)
    (M : Submodule A V) (hbM : span A (Set.range b) ≤ M) :
    BilinForm.dualSubmodule B M ≤
      span A (Set.range (BilinForm.dualBasis B hB b)) := by
  rw [← BilinForm.dualSubmodule_span_of_basis B hB b]
  exact dualSubmodule_antitone B hbM

theorem thm_5_12_injective (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (N : Submodule A V) (hN : span K (N : Set V) = ⊤) :
    Function.Injective (BilinForm.dualSubmoduleToDual B N) :=
  BilinForm.dualSubmoduleToDual_injective B hB N hN

end DualLatticeLattice

section DirectSumDualLattice

theorem cor_5_13_directSumBilinForm_nondegenerate
    {K : Type*} [Field K]
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    (B₁ : V₁ →ₗ[K] V₁ →ₗ[K] K) (hB₁ : B₁.Nondegenerate)
    (B₂ : V₂ →ₗ[K] V₂ →ₗ[K] K) (hB₂ : B₂.Nondegenerate) :
    (directSumBilinForm B₁ B₂).Nondegenerate := by
  constructor
  · intro ⟨x₁, x₂⟩ h
    have h1 : x₁ = 0 := by
      apply hB₁.1
      intro y₁
      have := h (y₁, 0)
      simp [directSumBilinForm, LinearMap.mk₂_apply] at this
      exact this
    have h2 : x₂ = 0 := by
      apply hB₂.1
      intro y₂
      have := h (0, y₂)
      simp [directSumBilinForm, LinearMap.mk₂_apply] at this
      exact this
    exact Prod.ext h1 h2
  · intro ⟨y₁, y₂⟩ h
    have h1 : y₁ = 0 := by
      apply hB₁.2
      intro x₁
      have := h (x₁, 0)
      simp [directSumBilinForm, LinearMap.mk₂_apply] at this
      exact this
    have h2 : y₂ = 0 := by
      apply hB₂.2
      intro x₂
      have := h (0, x₂)
      simp [directSumBilinForm, LinearMap.mk₂_apply] at this
      exact this
    exact Prod.ext h1 h2

theorem cor_5_13_direct_sum_dual
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁] [Module A V₁] [IsScalarTower A K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂] [Module A V₂] [IsScalarTower A K V₂]
    (B₁ : V₁ →ₗ[K] V₁ →ₗ[K] K) (B₂ : V₂ →ₗ[K] V₂ →ₗ[K] K)
    (M₁ : Submodule A V₁) (M₂ : Submodule A V₂) :
    BilinForm.dualSubmodule (directSumBilinForm B₁ B₂) (M₁.prod M₂) =
      (BilinForm.dualSubmodule B₁ M₁).prod (BilinForm.dualSubmodule B₂ M₂) := by
  ext ⟨x₁, x₂⟩
  simp only [Submodule.mem_prod, BilinForm.mem_dualSubmodule]
  constructor
  · intro h
    constructor
    · intro m₁ hm₁
      have := h (m₁, 0) (Submodule.mem_prod.mpr ⟨hm₁, M₂.zero_mem⟩)
      simp only [directSumBilinForm, LinearMap.mk₂_apply, map_zero, add_zero] at this
      exact this
    · intro m₂ hm₂
      have := h (0, m₂) (Submodule.mem_prod.mpr ⟨M₁.zero_mem, hm₂⟩)
      simp only [directSumBilinForm, LinearMap.mk₂_apply, map_zero, zero_add] at this
      exact this
  · rintro ⟨h₁, h₂⟩ ⟨m₁, m₂⟩ hm
    simp only [directSumBilinForm, LinearMap.mk₂_apply]
    exact Submodule.add_mem _ (h₁ m₁ (Submodule.mem_prod.mp hm).1) (h₂ m₂ (Submodule.mem_prod.mp hm).2)

theorem cor_5_13
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁] [Module A V₁] [IsScalarTower A K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂] [Module A V₂] [IsScalarTower A K V₂]
    (B₁ : V₁ →ₗ[K] V₁ →ₗ[K] K) (hB₁ : B₁.Nondegenerate)
    (B₂ : V₂ →ₗ[K] V₂ →ₗ[K] K) (hB₂ : B₂.Nondegenerate)
    (M₁ : Submodule A V₁) (M₂ : Submodule A V₂) :
    (directSumBilinForm B₁ B₂).Nondegenerate ∧
    BilinForm.dualSubmodule (directSumBilinForm B₁ B₂) (M₁.prod M₂) =
      (BilinForm.dualSubmodule B₁ M₁).prod (BilinForm.dualSubmodule B₂ M₂) :=
  ⟨cor_5_13_directSumBilinForm_nondegenerate B₁ hB₁ B₂ hB₂,
   cor_5_13_direct_sum_dual B₁ B₂ M₁ M₂⟩

end DirectSumDualLattice

section FreeDualLattice

variable
  {A : Type*} [CommRing A]
  {K : Type*} [Field K] [Algebra A K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {ι : Type*} [DecidableEq ι] [Finite ι]

theorem cor_5_14_dual_basis_property (B : V →ₗ[K] V →ₗ[K] K)
    (hB : B.Nondegenerate) (b : Basis ι K V) (i j : ι) :
    B (BilinForm.dualBasis B hB b i) (b j) = if j = i then 1 else 0 :=
  BilinForm.apply_dualBasis_left hB b i j

theorem cor_5_14_dual_basis_unique (B : V →ₗ[K] V →ₗ[K] K)
    (hB : B.Nondegenerate) (b : Basis ι K V) (v : ι → V)
    (hv : ∀ i j, B (v i) (b j) = if j = i then 1 else 0) :
    v = BilinForm.dualBasis B hB b :=
  ((BilinForm.dualBasis_eq_iff hB b v).mpr hv).symm

theorem cor_5_14_dual_lattice_free (B : V →ₗ[K] V →ₗ[K] K)
    (hB : B.Nondegenerate) (b : Basis ι K V) :
    BilinForm.dualSubmodule B (span A (Set.range b)) =
      span A (Set.range (BilinForm.dualBasis B hB b)) :=
  BilinForm.dualSubmodule_span_of_basis B hB b

end FreeDualLattice

section LocalizationDualLattice

structure IsLocALattice
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (V : Type*) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (S : Submonoid A) (N : Submodule A V) : Prop where
  fg_loc : ∃ T : Finset V, N = (Submodule.span A (T : Set V)).localize S
  span_eq_top : Submodule.span K (N : Set V) = ⊤

def BilinForm.dualSubmoduleLoc
    {A : Type*} [CommRing A]
    {K : Type*} [Field K] [Algebra A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (B : V →ₗ[K] V →ₗ[K] K) (S : Submonoid A) (M : Submodule A V) :
    Submodule A V where
  carrier := {v | ∀ y ∈ M, ∃ s ∈ S, s • (B v y) ∈ (1 : Submodule A K)}
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨s, hs, hs'⟩ := ha y hy
    obtain ⟨t, ht, ht'⟩ := hb y hy
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have key : (s * t) • (B (a + b) y) = t • (s • (B a y)) + s • (t • (B b y)) := by
      simp only [map_add, LinearMap.add_apply]
      rw [smul_add, mul_smul, mul_smul, smul_comm s t]
    rw [key]
    exact add_mem (Submodule.smul_mem _ t hs') (Submodule.smul_mem _ s ht')
  zero_mem' := by
    intro y _
    exact ⟨1, S.one_mem, by simp⟩
  smul_mem' := by
    intro c v hv y hy
    obtain ⟨s, hs, hs'⟩ := hv y hy
    refine ⟨s, hs, ?_⟩
    have key : s • (B (c • v) y) = c • (s • (B v y)) := by
      simp only [Algebra.smul_def, map_smul_of_tower, LinearMap.smul_apply]
      ring
    rw [key]
    exact Submodule.smul_mem _ c hs'

theorem Submodule.le_localize {A : Type*} [CommRing A]
    {V : Type*} [AddCommGroup V] [Module A V]
    (S : Submonoid A) (M : Submodule A V) : M ≤ M.localize S :=
  fun _ hv => ⟨1, S.one_mem, by simpa⟩

theorem isLocALattice_of_localize
    {A : Type*} [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (S : Submonoid A) (M : Submodule A V) (hM : IsALattice A K V M) :
    IsLocALattice A K V S (M.localize S) := by
  obtain ⟨⟨T, hT⟩, hspan⟩ := hM
  exact ⟨⟨T, by rw [hT]⟩, by
    rw [eq_top_iff]; rw [eq_top_iff] at hspan
    exact le_trans hspan (Submodule.span_mono (Submodule.le_localize S M))⟩

theorem dualSubmodule_isALattice
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (M : Submodule A V) (hM : IsALattice A K V M) :
    IsALattice A K V (BilinForm.dualSubmodule B M) := by
  classical
  have hs : ⊤ ≤ span K (M : Set V) := hM.span_eq_top ▸ le_refl _
  obtain ⟨ι, _, _, b, h_sub⟩ : ∃ (ι : Type _) (_ : DecidableEq ι) (_ : Fintype ι)
      (b : Basis ι K V), Set.range b ⊆ (M : Set V) := by
    let b := Basis.ofSpan hs
    have : Finite _ := Finite.finite_basis b
    exact ⟨_, inferInstance, Fintype.ofFinite _, b, Basis.ofSpan_subset hs⟩
  have hle : span A (Set.range b) ≤ M := span_le.mpr h_sub
  have h_le : BilinForm.dualSubmodule B M ≤
      span A (Set.range (BilinForm.dualBasis B hB b)) := by
    rw [← BilinForm.dualSubmodule_span_of_basis B hB b]
    exact dualSubmodule_antitone B hle
  have hN_fg : (span A (Set.range (BilinForm.dualBasis B hB b))).FG :=
    ⟨Set.Finite.toFinset (Set.finite_range _), by rw [Set.Finite.coe_toFinset]⟩
  obtain ⟨s, hs_span⟩ := hM.fg
  constructor

  · haveI := isNoetherian_of_fg_of_noetherian _ hN_fg
    rw [show BilinForm.dualSubmodule B M =
      Submodule.map (span A (Set.range (BilinForm.dualBasis B hB b))).subtype
        (Submodule.comap (span A (Set.range (BilinForm.dualBasis B hB b))).subtype
          (BilinForm.dualSubmodule B M)) from by
      rw [Submodule.map_comap_subtype]; exact (inf_eq_right.mpr h_le).symm]
    exact (IsNoetherian.noetherian _).map _

  · rw [eq_top_iff]
    intro w _
    obtain ⟨⟨d, hd_mem⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors A) (s.image (fun m => B w m))
    have h_mem : d • w ∈ BilinForm.dualSubmodule B M := by
      rw [BilinForm.mem_dualSubmodule]
      intro y hy
      rw [← hs_span] at hy
      refine Submodule.span_induction
        (fun x (hx : x ∈ (s : Set V)) => ?_) ?_ (fun x y _ _ hx hy => ?_)
        (fun a x _ hx => ?_) hy
      · simp only [map_smul_of_tower, smul_apply, Algebra.smul_def]
        obtain ⟨a, ha⟩ := hd (B w x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
        rw [Submodule.mem_one]
        exact ⟨a, by simpa [Algebra.smul_def] using ha⟩
      · simp only [map_zero]; exact zero_mem _
      · simp only [map_add] at *; exact add_mem hx hy
      · rw [map_smul_of_tower]; exact Submodule.smul_mem _ a hx
    have hd_ne : algebraMap A K d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd_mem
    have hw : w = (algebraMap A K d)⁻¹ • (d • w) := by
      rw [smul_comm, ← smul_assoc]
      simp only [Algebra.smul_def, mul_inv_cancel₀ hd_ne, one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h_mem)

theorem thm_5_12_surjective
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (M : Submodule A V) (hM : IsALattice A K V M) :
    Function.Surjective (BilinForm.dualSubmoduleToDual B M) := by
  intro f
  have hs : ⊤ ≤ Submodule.span K (M : Set V) := hM.span_eq_top ▸ le_refl _
  classical
  let b : Basis _ K V := Basis.ofSpan hs
  have hb_mem : ∀ i, (b i : V) ∈ M :=
    fun i => Basis.ofSpan_subset hs ⟨i, rfl⟩
  haveI : Fintype _ := FiniteDimensional.fintypeBasisIndex b
  let g : V →ₗ[K] K := b.constr K (fun i => algebraMap A K (f ⟨b i, hb_mem i⟩))
  have hg_basis : ∀ i, g (b i) = algebraMap A K (f ⟨b i, hb_mem i⟩) :=
    fun i => b.constr_basis (S := K) _ i
  let x : V := (BilinForm.toDual B hB).symm g
  have hBx : ∀ v, (B x) v = g v := by
    intro v
    have : BilinForm.toDual B hB x = g := LinearEquiv.apply_symm_apply _ g
    exact congr_fun (congr_arg DFunLike.coe this) v

  have key : ∀ (m : V) (hm : m ∈ M), g m = algebraMap A K (f ⟨m, hm⟩) := by
    intro m hm
    have hm_eq : m = ∑ i, (b.repr m i) • b i := (b.sum_repr m).symm
    obtain ⟨d, hd_int⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors A) (Finset.univ.image (fun i => b.repr m i))


    have hd_ci : ∀ i, IsLocalization.IsInteger A ((d : A) • b.repr m i) :=
      fun i => hd_int _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    choose a ha using hd_ci


    have hdm_eq : (d : A) • m = ∑ i, a i • b i := by
      conv_lhs => rw [show (d : A) • m = algebraMap A K (d : A) • m from
        (algebraMap_smul K (d : A) m).symm]
      rw [hm_eq, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, ← mul_smul]
      conv_lhs => rw [mul_comm]
      rw [← Algebra.smul_def, ← ha i, algebraMap_smul]

    have hdm_mem : (d : A) • m ∈ M := M.smul_mem (d : A) hm
    have hai_mem : ∀ i, (a i) • b i ∈ M :=
      fun i => M.smul_mem (a i) (hb_mem i)

    have hf_dm : f ⟨(d : A) • m, hdm_mem⟩ = (d : A) * f ⟨m, hm⟩ := by
      rw [show (⟨(d : A) • m, hdm_mem⟩ : ↥M) = (d : A) • ⟨m, hm⟩ from rfl,
          map_smul, smul_eq_mul]

    have hf_sum : f ⟨∑ i, (a i) • b i, M.sum_mem (fun i _ => hai_mem i)⟩ =
        ∑ i, a i * f ⟨b i, hb_mem i⟩ := by
      have h2 : (⟨∑ i, (a i) • b i, M.sum_mem (fun i _ => hai_mem i)⟩ : ↥M) = ∑ i, a i • ⟨b i, hb_mem i⟩ := by

        ext; simp
      rw [h2, map_sum]; congr 1; ext i; rw [map_smul, smul_eq_mul]

    have hf_eq : f ⟨(d : A) • m, hdm_mem⟩ =
        f ⟨∑ i, (a i) • b i, M.sum_mem (fun i _ => hai_mem i)⟩ := by
      congr 1; ext; exact hdm_eq

    have arith : (d : A) * f ⟨m, hm⟩ = ∑ i, a i * f ⟨b i, hb_mem i⟩ := by
      rw [← hf_dm, hf_eq, hf_sum]

    have arith_K : algebraMap A K (d : A) * algebraMap A K (f ⟨m, hm⟩) =
        ∑ i, algebraMap A K (a i) * algebraMap A K (f ⟨b i, hb_mem i⟩) := by
      rw [← map_mul, arith, map_sum]; congr 1; ext i; exact map_mul _ _ _

    have lhs_eq : algebraMap A K (d : A) * g m =
        ∑ i, algebraMap A K (a i) * algebraMap A K (f ⟨b i, hb_mem i⟩) := by

      rw [← smul_eq_mul, ← g.map_smul]


      rw [show algebraMap A K (d : A) • m = (d : A) • m from algebraMap_smul K _ m]
      rw [hdm_eq]


      simp only [map_sum, map_smul_of_tower]
      congr 1; ext i
      rw [hg_basis, Algebra.smul_def]

    have both_eq : algebraMap A K (d : A) * g m =
        algebraMap A K (d : A) * algebraMap A K (f ⟨m, hm⟩) := by
      rw [lhs_eq, arith_K]
    have hd_ne : algebraMap A K (d : A) ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero d.2 (IsFractionRing.injective A K (by simp [h]))
    exact mul_left_cancel₀ hd_ne both_eq
  have hx_mem : x ∈ BilinForm.dualSubmodule B M := by
    intro m hm; rw [hBx m, key m hm]
    exact ⟨f ⟨m, hm⟩, by simp [Algebra.algebraMap_eq_smul_one]⟩
  exact ⟨⟨x, hx_mem⟩, by
    ext ⟨m, hm⟩
    apply IsFractionRing.injective A K
    change algebraMap A K (BilinForm.dualSubmoduleParing B ⟨x, hx_mem⟩ ⟨m, hm⟩) = _
    rw [BilinForm.dualSubmoduleParing_spec, hBx, key m hm]⟩

theorem thm_5_12
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (M : Submodule A V) (hM : IsALattice A K V M) :
    IsALattice A K V (BilinForm.dualSubmodule B M) ∧
    Function.Bijective (BilinForm.dualSubmoduleToDual B M) := by
  refine ⟨dualSubmodule_isALattice B hB M hM, ?_⟩
  exact ⟨thm_5_12_injective B hB M hM.span_eq_top,
         thm_5_12_surjective B hB M hM⟩

def thm_5_12_linearEquiv
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (M : Submodule A V) (hM : IsALattice A K V M) :
    ↥(BilinForm.dualSubmodule B M) ≃ₗ[A] Module.Dual A ↥M :=
  LinearEquiv.ofBijective (BilinForm.dualSubmoduleToDual B M) (thm_5_12 B hB M hM).2

theorem lem_5_15_localization_dual
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (M : Submodule A V) (hM : IsALattice A K V M) (S : Submonoid A) :
    IsLocALattice A K V S (M.localize S) ∧
    IsLocALattice A K V S ((BilinForm.dualSubmodule B M).localize S) ∧
    BilinForm.dualSubmoduleLoc B S (M.localize S) =
      (BilinForm.dualSubmodule B M).localize S := by
  refine ⟨isLocALattice_of_localize S M hM,
         isLocALattice_of_localize S _ (dualSubmodule_isALattice B hB M hM), ?_⟩

  ext v
  constructor
  ·

    intro hv
    obtain ⟨⟨T, hT⟩, _⟩ := hM

    have hT_in_loc : ∀ m ∈ (T : Set V), m ∈ M.localize S :=
      fun m hm => Submodule.le_localize S M (hT ▸ Submodule.subset_span hm)


    have : ∀ m ∈ T, ∃ s ∈ S, s • (B v m) ∈ (1 : Submodule A K) :=
      fun m hm => hv m (hT_in_loc m hm)

    classical
    let s_fun : V → A := fun m => if hm : m ∈ T then (this m hm).choose else 1
    have hs_fun_mem : ∀ m ∈ T, s_fun m ∈ S := by
      intro m hm; simp only [s_fun, dif_pos hm]; exact (this m hm).choose_spec.1
    have hs_fun_prop : ∀ m ∈ T, s_fun m • (B v m) ∈ (1 : Submodule A K) := by
      intro m hm; simp only [s_fun, dif_pos hm]; exact (this m hm).choose_spec.2

    let s_prod := T.prod s_fun
    have hs_prod : s_prod ∈ S := Submonoid.prod_mem S hs_fun_mem
    refine ⟨s_prod, hs_prod, ?_⟩

    intro y hy
    rw [← hT] at hy

    have h_gen : ∀ m ∈ T, s_prod • ((B v) m) ∈ (1 : Submodule A K) := by
      intro m hm
      have hsplit : s_prod = (T.erase m).prod s_fun * s_fun m := by
        simp only [s_prod]; rw [← Finset.prod_erase_mul T s_fun hm]
      rw [hsplit, mul_smul]
      exact Submodule.smul_mem _ _ (hs_fun_prop m hm)

    have : y ∈ Submodule.comap ((B (s_prod • v)).restrictScalars A) (1 : Submodule A K) := by
      apply Submodule.span_le.mpr _ hy
      intro m hm
      show (B (s_prod • v)) m ∈ (1 : Submodule A K)
      have h1 : (B (s_prod • v)) m = s_prod • ((B v) m) := by
        conv_lhs =>
          rw [show s_prod • v = algebraMap A K s_prod • v from (algebraMap_smul K s_prod v).symm]
        simp [LinearMap.smul_apply, Algebra.smul_def]
      rw [h1]; exact h_gen m hm
    exact this

  ·
    intro ⟨s, hs, hsv⟩

    intro y ⟨t, ht, hty⟩


    have h1 : (B (s • v)) (t • y) ∈ (1 : Submodule A K) := hsv (t • y) hty

    refine ⟨s * t, S.mul_mem hs ht, ?_⟩


    convert h1 using 1
    simp only [Algebra.smul_def, map_smul_of_tower, LinearMap.smul_apply, map_mul]
    ring

end LocalizationDualLattice

section DoubleDual

variable
  {A : Type*} [CommRing A]
  {K : Type*} [Field K] [Algebra A K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {ι : Type*} [Finite ι]

theorem prop_5_16_double_dual_free (B : V →ₗ[K] V →ₗ[K] K)
    (hB : B.Nondegenerate) (hB' : BilinForm.IsSymm B) (b : Basis ι K V) :
    BilinForm.dualSubmodule B
      (BilinForm.dualSubmodule B (span A (Set.range b))) =
      span A (Set.range b) :=
  BilinForm.dualSubmodule_dualSubmodule_of_basis B hB hB' b

theorem prop_2_6_lattice_eq_inter_localizations
    {A : Type*} [CommRing A]
    {V : Type*} [AddCommGroup V] [Module A V]
    (M : Submodule A V)
    (v : V) :
    (∀ P : MaximalSpectrum A, ∃ s ∈ P.asIdeal.primeCompl, s • v ∈ M) → v ∈ M := by
  intro h

  let I : Ideal A :=
    { carrier := {a | a • v ∈ M}
      add_mem' := fun {a b} (ha : a • v ∈ M) (hb : b • v ∈ M) => by
        show (a + b) • v ∈ M; rw [add_smul]; exact M.add_mem ha hb
      zero_mem' := by show (0 : A) • v ∈ M; rw [zero_smul]; exact M.zero_mem
      smul_mem' := fun c {a} (ha : a • v ∈ M) => by
        show (c * a) • v ∈ M; rw [mul_smul]; exact M.smul_mem c ha }

  suffices hI : I = ⊤ by
    have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : A) • v ∈ M := h1
    rwa [one_smul] at h2
  by_contra hI
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨s, hs, hsv⟩ := h ⟨P, hP⟩
  exact hs (hIP hsv)

theorem dvr_localize_lattice_free
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (M : Submodule A V) (hM : IsALattice A K V M)
    (P : MaximalSpectrum A) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Basis ι K V),
      M.localize P.asIdeal.primeCompl =
        (Submodule.span A (Set.range b)).localize P.asIdeal.primeCompl := by
  set S := P.asIdeal.primeCompl
  set AP := Localization.AtPrime P.asIdeal with AP_def

  haveI hfin : Module.Finite A ↥M := by rw [Module.Finite.iff_fg]; exact hM.fg
  haveI htf : Module.IsTorsionFree A ↥M := by
    constructor; intro a ha x y hxy; ext
    have h1 : (a : A) • (x : V) = a • (y : V) := congrArg Subtype.val hxy
    have ha' : algebraMap A K a ≠ 0 := by
      intro h; exact ha.ne_zero (IsFractionRing.injective A K (by simp [h]))
    rw [← IsScalarTower.algebraMap_smul K a (x : V),
        ← IsScalarTower.algebraMap_smul K a (y : V)] at h1
    exact smul_right_injective V ha' h1

  obtain ⟨n, bLM⟩ := @Module.basisOfFiniteTypeTorsionFree'
    (Localization.AtPrime P.asIdeal) _ (LocalizedModule S ↥M) _ _ _ _ _ _

  have hS_units : ∀ (s : S), IsUnit ((algebraMap A (Module.End A V)) (s : A)) := by
    intro ⟨s, hs⟩
    rw [Module.algebraMap_end_eq_smul_id]
    have hs' : algebraMap A K s ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero (Ideal.primeCompl_le_nonZeroDivisors P.asIdeal hs)
        (IsFractionRing.injective A K (by simp [h]))
    let inv : V →ₗ[A] V := {
      toFun := fun v => (algebraMap A K s)⁻¹ • v
      map_add' := by intros; simp [smul_add]
      map_smul' := by
        intros a v; simp only [RingHom.id_apply]
        rw [← IsScalarTower.algebraMap_smul K a v, smul_comm,
            IsScalarTower.algebraMap_smul K a]
    }
    refine ⟨⟨s • LinearMap.id, inv, ?_, ?_⟩, rfl⟩
    · ext v; show s • (inv v) = v
      simp only [inv, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← IsScalarTower.algebraMap_smul K s ((algebraMap A K s)⁻¹ • v)]
      simp [smul_smul, mul_inv_cancel₀ hs']
    · ext v; show inv (s • v) = v
      simp only [inv, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← IsScalarTower.algebraMap_smul K s v, smul_smul, inv_mul_cancel₀ hs', one_smul]
  let φ := LocalizedModule.lift S M.subtype hS_units

  have hφ_inj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using LocalizedModule.induction_on with
    | h m s =>
      rw [LocalizedModule.lift_mk] at hx
      set u := (hS_units s).unit
      have h1 : M.subtype m = 0 := by
        have key := congr_arg u.val hx
        simp only [map_zero] at key
        change (u.val ∘ₗ ↑u⁻¹) (M.subtype m) = 0 at key
        have : (u.val ∘ₗ ↑u⁻¹) = LinearMap.id := by
          ext v; show (u.val * u.inv) v = v; simp
        rw [this, LinearMap.id_apply] at key; exact key
      rw [show m = 0 from Subtype.ext h1, LocalizedModule.zero_mk]

  let e : Fin n → V := fun i => φ (bLM i)

  have hli : LinearIndependent K e := by
    rw [← LinearIndependent.iff_fractionRing (R := A) (K := K)]
    have hA_indep : LinearIndependent A (bLM : Fin n → LocalizedModule S ↥M) := by
      apply LinearIndependent.restrict_scalars (K := AP)
      · intro a b h
        exact IsLocalization.injective AP P.asIdeal.primeCompl_le_nonZeroDivisors (by simpa using h)
      · exact bLM.linearIndependent
    exact hA_indep.map' φ (LinearMap.ker_eq_bot.mpr hφ_inj)

  have hspan : Submodule.span K (Set.range e) = ⊤ := by

    rw [eq_top_iff, ← hM.span_eq_top]
    apply Submodule.span_le.mpr


    intro v hv

    set x : LocalizedModule S ↥M := LocalizedModule.mk ⟨v, hv⟩ 1
    have hφx : φ x = v := LocalizedModule.lift_mk_one S M.subtype hS_units ⟨v, hv⟩

    obtain ⟨⟨t, ht⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
      (M := S) (S := AP) (fun i : Fin n => bLM.repr x i)

    have hint' : ∀ i, ∃ a : A, algebraMap A AP a = (t : A) • bLM.repr x i := by
      intro i; exact hint i
    choose a_coeff ha_coeff using hint'

    have ht_ne : algebraMap A K t ≠ 0 := by
      intro hc
      have h0 : t = 0 := IsFractionRing.injective A K (by simp [hc])
      exact ht (h0 ▸ P.asIdeal.zero_mem)

    suffices h_tv : t • v ∈ Submodule.span A (Set.range e) by
      have h_tv_K := Submodule.span_le_restrictScalars A K _ h_tv
      rw [show v = (algebraMap A K t)⁻¹ • (algebraMap A K t • v) from by
        rw [smul_smul, inv_mul_cancel₀ ht_ne, one_smul]]
      rw [← IsScalarTower.algebraMap_smul K t v] at h_tv_K
      exact (Submodule.span K (Set.range e)).smul_mem _ h_tv_K

    have h1 : t • v = φ (t • x) := by rw [map_smul, hφx]
    have h2 : t • x = ∑ i, algebraMap A AP (a_coeff i) • bLM i := by
      conv_lhs => rw [← bLM.sum_repr x]
      rw [Finset.smul_sum]
      congr 1; ext i
      rw [show t • (bLM.repr x) i • bLM i = (t • (bLM.repr x) i) • bLM i from
        (smul_assoc t ((bLM.repr x) i) (bLM i)).symm]
      rw [← ha_coeff i, algebraMap_smul]
    rw [h1, h2, map_sum]
    apply Submodule.sum_mem
    intro i _

    rw [algebraMap_smul, map_smul]
    exact Submodule.smul_mem _ (a_coeff i) (Submodule.subset_span ⟨i, rfl⟩)

  let b := Basis.mk hli hspan.ge


  have h_M_to_span : ∀ w ∈ M, ∃ t ∈ S, t • w ∈ Submodule.span A (Set.range e) := by
    intro w hw
    set xw := LocalizedModule.mk (⟨w, hw⟩ : ↥M) (1 : S)
    have hφw : φ xw = w := LocalizedModule.lift_mk_one S M.subtype hS_units ⟨w, hw⟩
    obtain ⟨⟨tw, htw⟩, hintw⟩ := IsLocalization.exist_integer_multiples_of_finite
      (M := S) (S := AP) (fun i : Fin n => bLM.repr xw i)
    have hintw' : ∀ i, ∃ a : A, algebraMap A AP a = (tw : A) • bLM.repr xw i := by
      intro i; exact hintw i
    choose aw haw using hintw'
    refine ⟨tw, htw, ?_⟩
    rw [show tw • w = φ (tw • xw) by rw [map_smul, hφw]]
    have : tw • xw = ∑ i, algebraMap A AP (aw i) • bLM i := by
      conv_lhs => rw [← bLM.sum_repr xw]
      rw [Finset.smul_sum]; congr 1; ext i
      rw [show tw • (bLM.repr xw) i • bLM i = (tw • (bLM.repr xw) i) • bLM i from
        (smul_assoc tw ((bLM.repr xw) i) (bLM i)).symm]
      rw [← haw i, algebraMap_smul]
    rw [this, map_sum]
    apply Submodule.sum_mem; intro i _
    rw [algebraMap_smul, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have h_e_to_M : ∀ i : Fin n, ∃ u ∈ S, u • e i ∈ M := by
    intro i

    induction hbi : bLM i using LocalizedModule.induction_on with
    | h mi si =>
      refine ⟨si, si.prop, ?_⟩
      show (si : A) • φ (bLM i) ∈ M
      rw [hbi]

      rw [← map_smul φ (si : A) (LocalizedModule.mk mi si)]

      rw [LocalizedModule.smul'_mk]

      have : LocalizedModule.mk ((si : A) • mi) si = LocalizedModule.mk mi (1 : S) :=
        LocalizedModule.mk_cancel si mi
      rw [this]
      rw [LocalizedModule.lift_mk_one]
      exact mi.prop

  refine ⟨Fin n, inferInstance, b, ?_⟩
  ext v
  simp only [Submodule.localize, Submodule.mem_mk]
  constructor
  ·
    rintro ⟨s, hs, hsv⟩
    obtain ⟨t, ht_mem, ht_span⟩ := h_M_to_span (s • v) hsv
    refine ⟨t * s, S.mul_mem ht_mem hs, ?_⟩
    rw [mul_smul]

    convert ht_span using 2
    simp only [b, Basis.coe_mk]
  ·
    rintro ⟨s, hs, hsv⟩

    have hsv' : s • v ∈ Submodule.span A (Set.range e) := by
      convert hsv using 2; simp only [b, Basis.coe_mk]

    choose u_fn hu_fn_mem hu_fn_in_M using h_e_to_M
    set u : A := ∏ i : Fin n, u_fn i
    have hu_mem : u ∈ S := Submonoid.prod_mem S (fun i _ => hu_fn_mem i)
    have hu_ei : ∀ i : Fin n, u • e i ∈ M := by
      intro i
      have : u = (∏ j ∈ (Finset.univ.erase i), u_fn j) * u_fn i := by
        rw [mul_comm]; exact (Finset.mul_prod_erase Finset.univ u_fn (Finset.mem_univ i)).symm
      rw [this, mul_smul]
      exact M.smul_mem _ (hu_fn_in_M i)

    refine ⟨u * s, S.mul_mem hu_mem hs, ?_⟩
    rw [mul_smul]


    apply Submodule.span_induction (p := fun x _ => u • x ∈ M) _ _ _ _ hsv'
    · rintro w ⟨i, rfl⟩; exact hu_ei i
    · simp [M.zero_mem]
    · intro x y _ _ hx hy; rw [smul_add]; exact M.add_mem hx hy
    · intro a x _ hx; rw [smul_comm]; exact M.smul_mem a hx

theorem double_dual_local_dvr_step
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (hB' : BilinForm.IsSymm B)
    (M : Submodule A V) (hM : IsALattice A K V M)
    (P : MaximalSpectrum A)
    (v : V) (hv : v ∈ BilinForm.dualSubmodule B (BilinForm.dualSubmodule B M)) :
    ∃ s ∈ P.asIdeal.primeCompl, s • v ∈ M := by

  set S := P.asIdeal.primeCompl

  obtain ⟨ι, hfin, b, hMloc⟩ := dvr_localize_lattice_free M hM P

  set L := Submodule.span A (Set.range b) with hL_def

  have hL : IsALattice A K V L := by
    constructor
    · haveI : Finite ι := Finite.of_fintype ι
      exact Submodule.fg_span (Set.finite_range b)

    · rw [Submodule.span_span_of_tower]; exact b.span_eq

  have hLstar : IsALattice A K V (BilinForm.dualSubmodule B L) :=
    dualSubmodule_isALattice B hB L hL

  have hMstar : IsALattice A K V (BilinForm.dualSubmodule B M) :=
    dualSubmodule_isALattice B hB M hM

  have h515_M := (lem_5_15_localization_dual B hB M hM S).2.2
  have h515_Mstar := (lem_5_15_localization_dual B hB _ hMstar S).2.2
  have h515_L := (lem_5_15_localization_dual B hB L hL S).2.2
  have h515_Lstar := (lem_5_15_localization_dual B hB _ hLstar S).2.2

  have hfree : BilinForm.dualSubmodule B (BilinForm.dualSubmodule B L) = L := by
    haveI : Finite ι := Finite.of_fintype ι
    exact prop_5_16_double_dual_free B hB hB' b


  have hstar_eq : (BilinForm.dualSubmodule B M).localize S =
      (BilinForm.dualSubmodule B L).localize S := by
    rw [← h515_M, ← h515_L, hMloc]

  have hstarstar_eq : (BilinForm.dualSubmodule B (BilinForm.dualSubmodule B M)).localize S =
      (BilinForm.dualSubmodule B (BilinForm.dualSubmodule B L)).localize S := by
    rw [← h515_Mstar, ← h515_Lstar, hstar_eq]

  have hdd_eq : (BilinForm.dualSubmodule B (BilinForm.dualSubmodule B M)).localize S =
      M.localize S := by
    rw [hstarstar_eq, hfree, ← hMloc]

  have hv_loc : v ∈ (BilinForm.dualSubmodule B (BilinForm.dualSubmodule B M)).localize S :=
    Submodule.le_localize S _ hv

  rw [hdd_eq] at hv_loc
  exact hv_loc

lemma double_dual_sub_original
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (hB' : BilinForm.IsSymm B)
    (M : Submodule A V) (hM : IsALattice A K V M) :
    BilinForm.dualSubmodule B (BilinForm.dualSubmodule B M) ≤ M := by
  intro v hv


  exact prop_2_6_lattice_eq_inter_localizations M v fun P =>

    double_dual_local_dvr_step B hB hB' M hM P v hv

theorem prop_5_16_double_dual_dedekind
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (hB' : BilinForm.IsSymm B)
    (M : Submodule A V) (hM : IsALattice A K V M) :
    dualLattice A K V B (dualLattice A K V B M) = M := by

  rw [dualLattice_eq_dualSubmodule, dualLattice_eq_dualSubmodule]

  apply le_antisymm
  ·
    exact double_dual_sub_original B hB hB' M hM
  ·


    intro v hv w hw
    have h1 := hw v hv
    rw [Submodule.mem_one] at h1 ⊢
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, by rw [hB'.eq w v] at ha; exact ha⟩

end DoubleDual

alias dualBasis_exists := prop_5_7_existence

alias dualBasis_unique := prop_5_7_uniqueness

alias dualSubmoduleToDual_injective := thm_5_12_injective

alias directSumBilinForm_nondegenerate := cor_5_13_directSumBilinForm_nondegenerate

alias localization_dual_comm := lem_5_15_localization_dual
