/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.DifferentDiscriminant

noncomputable section

open Algebra in
lemma discr_smul_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (c : K) (b : Fin (Module.finrank K L) → L) :
    Algebra.discr K (fun i => c • b i) =
      c ^ (2 * Module.finrank K L) * Algebra.discr K b := by
  simp only [Algebra.discr_def]
  have hM : Algebra.traceMatrix K (fun i => c • b i) =
      c ^ 2 • Algebra.traceMatrix K b := by
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.smul_apply, smul_eq_mul]
    rw [smul_mul_smul_comm]
    simp [map_smul, smul_eq_mul, sq]
  rw [hM, Matrix.det_smul]
  simp only [Fintype.card_fin]
  ring

section DiscriminantLocalization


variable (A K : Type*) (L : Type*) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]


variable (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)


variable (SA : Type*) [CommRing SA] [IsDomain SA] [Algebra A SA] [IsLocalization S SA]
variable (SB : Type*) [CommRing SB] [IsDomain SB] [Algebra B SB]
  [IsLocalization (Algebra.algebraMapSubmonoid B S) SB]


variable [Algebra SA SB] [Algebra A SB] [Algebra SA L] [Algebra SA K] [Algebra SB L]
variable [IsScalarTower A SA SB] [IsScalarTower A B SB]
variable [IsScalarTower A SA L] [IsScalarTower A SA K]
variable [IsScalarTower SA SB L] [IsScalarTower SA K L]


variable [IsFractionRing SA K] [IsIntegrallyClosed SA]
variable [IsFractionRing SB L] [IsDedekindDomain SB]
variable [Module.IsTorsionFree SA SB] [Module.IsTorsionFree B SB]
variable [IsIntegralClosure SB SA L]
variable [Nontrivial SB] [NoZeroDivisors SB]
variable [IsScalarTower B SB L]

set_option linter.unusedSectionVars false in
lemma imageOfB_subset_imageOfSB :
    (imageOfB A L B : Set L) ⊆ (imageOfB SA L SB : Set L) := by
  intro x hx
  rw [SetLike.mem_coe, mem_imageOfB] at hx ⊢
  obtain ⟨b, hb⟩ := hx
  exact ⟨algebraMap B SB b, by rw [← hb]; exact (IsScalarTower.algebraMap_apply B SB L _).symm⟩

set_option linter.unusedSectionVars false in
lemma latticeDiscrSet_B_subset_SB :
    latticeDiscrSet A K (imageOfB A L B) ⊆
      latticeDiscrSet SA K (imageOfB SA L SB) := by
  intro d ⟨b, hb, hd⟩
  exact ⟨b, fun i => imageOfB_subset_imageOfSB A L B SA SB (SetLike.mem_coe.mpr (hb i)), hd⟩

include S hS in
set_option linter.unusedSectionVars false in
theorem proposition_12_15 :
    Submodule.span SA (extensionDiscriminant A K L B : Set K) =
      extensionDiscriminant SA K L SB := by
  apply le_antisymm
  ·
    apply Submodule.span_le.mpr
    intro d hd
    rw [extensionDiscriminant, latticeDiscriminant] at hd
    have h1 : d ∈ Submodule.span SA (latticeDiscrSet A K (imageOfB A L B) : Set K) :=
      Submodule.span_le_restrictScalars A SA _ hd
    exact Submodule.span_mono (latticeDiscrSet_B_subset_SB A K L B SA SB) h1
  ·
    rw [extensionDiscriminant, latticeDiscriminant]
    apply Submodule.span_le.mpr
    intro d ⟨e, he, hd⟩
    rw [hd]

    choose sb hsb using fun i => (mem_imageOfB (A := SA) (L := L) (B := SB)).mp (he i)

    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples
        (Algebra.algebraMapSubmonoid B S) Finset.univ sb

    choose bi hbi using fun i => ht i (Finset.mem_univ i)

    obtain ⟨a, ha, hat⟩ := t.prop


    have hL : ∀ i, algebraMap B L (bi i) = algebraMap A L a * e i := by
      intro i

      have h1 := congr_arg (algebraMap SB L) (hbi i)


      rw [← IsScalarTower.algebraMap_apply B SB L] at h1


      simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply B SB L] at h1
      rw [hat.symm, ← IsScalarTower.algebraMap_apply A B L, hsb i] at h1
      exact h1

    have hsmul_mem : ∀ i, algebraMap A K a • e i ∈ imageOfB A L B := by
      intro i
      rw [mem_imageOfB]
      refine ⟨bi i, ?_⟩
      rw [hL i, Algebra.smul_def, IsScalarTower.algebraMap_apply A K L]

    have hdisc_mem : Algebra.discr K (fun i => algebraMap A K a • e i) ∈
        extensionDiscriminant A K L B :=
      discr_mem_extensionDiscriminant A K L B hsmul_mem

    have hdisc_eq : Algebra.discr K (fun i => algebraMap A K a • e i) =
        (algebraMap A K a) ^ (2 * Module.finrank K L) * Algebra.discr K e :=
      discr_smul_eq (algebraMap A K a) e

    have ha_unit : IsUnit (algebraMap A SA a) :=
      IsLocalization.map_units SA ⟨a, ha⟩

    have ha_ne : algebraMap A K a ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective A K)]
      exact nonZeroDivisors.ne_zero (hS ha)

    have hdisc_inv : Algebra.discr K e =
        ((algebraMap A K a) ^ (2 * Module.finrank K L))⁻¹ *
          Algebra.discr K (fun i => algebraMap A K a • e i) := by
      rw [hdisc_eq]
      rw [inv_mul_cancel_left₀ (pow_ne_zero _ ha_ne)]

    obtain ⟨u, hu⟩ := ha_unit
    set n' := 2 * Module.finrank K L with hn'

    have hmap_inv : algebraMap SA K ↑u⁻¹ = (algebraMap SA K ↑u)⁻¹ :=
      eq_inv_of_mul_eq_one_right
        (by rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
    have hinv_eq : ((algebraMap A K a) ^ n')⁻¹ =
        algebraMap SA K (↑u⁻¹ ^ n') := by
      rw [map_pow, hmap_inv, ← inv_pow, IsScalarTower.algebraMap_apply A SA K, hu]

    rw [hdisc_inv, hinv_eq, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (SetLike.mem_coe.mpr hdisc_mem))

end DiscriminantLocalization

end
