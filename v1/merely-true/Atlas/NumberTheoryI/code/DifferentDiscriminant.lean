/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Atlas.NumberTheoryI.code.EtaleAlgebrasProps
import Atlas.NumberTheoryI.code.IdealNorms

noncomputable section

open Algebra Submodule FractionalIdeal
open scoped Matrix

universe u

section TraceDualBModule

variable {A K : Type*} {L : Type u} {B : Type*}
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

theorem traceDual_smul_mem (I : Submodule B L) (b : B) (x : L)
    (hx : x ∈ Submodule.traceDual A K I) :
    b • x ∈ Submodule.traceDual A K I := by
  rw [Submodule.mem_traceDual] at hx ⊢
  intro m hm

  rw [traceForm_apply, smul_mul_assoc, mul_comm, ← smul_mul_assoc, mul_comm]

  exact hx _ (I.smul_mem b hm)

end TraceDualBModule

section TraceDualFractionalIdeal

variable (A K : Type*) {L : Type u} {B : Type*}
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain B]

theorem traceDual_ne_zero
    {I : FractionalIdeal (nonZeroDivisors B) L} (hI : I ≠ 0) :
    FractionalIdeal.dual A K I ≠ 0 :=
  FractionalIdeal.dual_ne_zero A K hI

theorem mem_traceDual_iff
    {I : FractionalIdeal (nonZeroDivisors B) L} (hI : I ≠ 0) {x : L} :
    x ∈ FractionalIdeal.dual A K I ↔
      ∀ m ∈ I, traceForm K L x m ∈ (algebraMap A K).range :=
  FractionalIdeal.mem_dual hI

end TraceDualFractionalIdeal

section TraceDualOfB

variable (A K : Type*) {L : Type u} {B : Type*}
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain B]

def traceDualB : FractionalIdeal (nonZeroDivisors B) L :=
  FractionalIdeal.dual A K 1

lemma traceDual_restrictScalars_eq_coe_dual :
    (Submodule.traceDual A K (1 : Submodule B L)).restrictScalars A =
    (↑(FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) :
      Submodule B L).restrictScalars A := by
  congr 1
  exact (FractionalIdeal.coe_dual_one A K L B).symm

theorem mem_traceDualB {x : L} :
    x ∈ traceDualB A K (L := L) (B := B) ↔
      ∀ b ∈ (1 : FractionalIdeal (nonZeroDivisors B) L),
        traceForm K L x b ∈ (algebraMap A K).range := by
  exact FractionalIdeal.mem_dual
    (show (1 : FractionalIdeal (nonZeroDivisors B) L) ≠ 0 from one_ne_zero)

theorem one_le_traceDualB :
    (1 : FractionalIdeal (nonZeroDivisors B) L) ≤ traceDualB A K := by
  have := FractionalIdeal.inv_le_dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)
  rwa [inv_one] at this

theorem traceDualB_inv_le_one :
    (traceDualB A K (L := L) (B := B))⁻¹ ≤ 1 :=
  FractionalIdeal.dual_inv_le A K 1

end TraceDualOfB

section DifferentIdeal

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain B] [Module.IsTorsionFree A B]

abbrev different : Ideal B := differentIdeal A B

theorem different_eq_traceDual_inv :
    (↑(differentIdeal A B) : FractionalIdeal (nonZeroDivisors B) L) =
      (FractionalIdeal.dual A K 1)⁻¹ :=
  coeIdeal_differentIdeal A K L B

theorem different_inv_eq_traceDual :
    (↑(differentIdeal A B) : FractionalIdeal (nonZeroDivisors B) L)⁻¹ =
      FractionalIdeal.dual A K 1 := by
  rw [different_eq_traceDual_inv A K L B, inv_inv]

end DifferentIdeal

section DifferentLocalization


variable (A K : Type*) (L : Type u) (B : Type*)
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
variable [IsScalarTower B SB L]
variable [IsScalarTower A SA L] [IsScalarTower A SA K]
variable [IsScalarTower SA SB L] [IsScalarTower SA K L]


variable [IsFractionRing SA K] [IsIntegrallyClosed SA]
variable [IsFractionRing SB L] [IsDedekindDomain SB]
variable [Module.IsTorsionFree SA SB] [Module.IsTorsionFree B SB]
variable [IsIntegralClosure SB SA L]
variable [Nontrivial SB] [NoZeroDivisors SB]

include hS K L in
theorem localization_dual_comm_axiom :
    (FractionalIdeal.extendedHomₐ L SB)
      (FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) =
      FractionalIdeal.dual SA K (1 : FractionalIdeal (nonZeroDivisors SB) L) := by

  have hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (algebraMap B SB)
    (FaithfulSMul.algebraMap_injective B SB)
  have h_map_id : IsLocalization.map L (algebraMap B SB) hf = RingHom.id L := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors B)
    ext b
    simp only [RingHom.comp_apply, IsLocalization.map_eq, RingHom.id_apply]
    rw [IsScalarTower.algebraMap_apply B SB L]
  have h_map_eq : ∀ x : L, IsLocalization.map L (algebraMap B SB) hf x = x :=
    fun x => congr_fun (congr_arg DFunLike.coe h_map_id) x

  have hone_B : (1 : FractionalIdeal (nonZeroDivisors B) L) ≠ 0 := one_ne_zero
  have hone_SB : (1 : FractionalIdeal (nonZeroDivisors SB) L) ≠ 0 := one_ne_zero


  have dual_B_le_dual_SB : ∀ y : L,
      y ∈ FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L) →
      y ∈ FractionalIdeal.dual SA K (1 : FractionalIdeal (nonZeroDivisors SB) L) := by
    intro y hy
    rw [FractionalIdeal.mem_dual hone_SB]
    intro m hm
    rw [FractionalIdeal.mem_dual hone_B] at hy
    rw [FractionalIdeal.mem_one_iff] at hm
    obtain ⟨m_sb, rfl⟩ := hm

    obtain ⟨⟨b_val, ⟨sb, hsb⟩⟩, hbs⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid B S) m_sb
    simp only at hbs
    change sb ∈ S.map (algebraMap A B) at hsb
    rw [Submonoid.mem_map] at hsb
    obtain ⟨a, ha, rfl⟩ := hsb


    have hbs_L : algebraMap SB L m_sb * algebraMap A L a = algebraMap B L b_val := by
      have h := congr_arg (algebraMap SB L) hbs
      simp only [map_mul] at h
      rw [← IsScalarTower.algebraMap_apply B SB L,
          ← IsScalarTower.algebraMap_apply B SB L] at h
      rwa [← IsScalarTower.algebraMap_apply A B L] at h

    have ha_nzd : a ∈ nonZeroDivisors A := hS ha
    have ha_K_ne : (algebraMap A K) a ≠ 0 :=
      map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective A K) ha_nzd
    have ha_L_ne : algebraMap A L a ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A K L]
      simp [ha_K_ne]

    have hb_mem : algebraMap B L b_val ∈ (1 : FractionalIdeal (nonZeroDivisors B) L) := by
      rw [FractionalIdeal.mem_one_iff]; exact ⟨b_val, rfl⟩
    obtain ⟨c, hc⟩ := hy (algebraMap B L b_val) hb_mem

    have h_msb_eq : algebraMap SB L m_sb = algebraMap B L b_val * (algebraMap A L a)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ ha_L_ne, hbs_L]


    rw [Algebra.traceForm_apply, h_msb_eq]

    rw [show (algebraMap A L a)⁻¹ = algebraMap K L ((algebraMap A K a)⁻¹) from by
      rw [IsScalarTower.algebraMap_apply A K L, map_inv₀]]
    rw [show y * (algebraMap B L b_val * algebraMap K L ((algebraMap A K a)⁻¹)) =
        algebraMap K L ((algebraMap A K a)⁻¹) * (y * algebraMap B L b_val) from by ring,
      ← Algebra.smul_def]
    rw [(Algebra.trace K L).map_smul, smul_eq_mul]
    rw [show (trace K L) (y * (algebraMap B L) b_val) = ((traceForm K L) y) ((algebraMap B L) b_val)
      from (Algebra.traceForm_apply K y _).symm, ← hc]

    refine ⟨IsLocalization.mk' SA c ⟨a, ha⟩, ?_⟩
    have h1 := IsLocalization.mk'_spec SA c ⟨a, ha⟩
    have h2 := congr_arg (algebraMap SA K) h1
    simp only [map_mul] at h2
    rw [← IsScalarTower.algebraMap_apply A SA K, ← IsScalarTower.algebraMap_apply A SA K] at h2
    rw [← h2, mul_comm]
    exact (mul_inv_cancel_right₀ ha_K_ne _).symm

  apply le_antisymm
  ·
    intro x hx
    rw [FractionalIdeal.extendedHomₐ] at hx
    simp only [FractionalIdeal.extendedHom_apply] at hx
    have hx_sub : x ∈ (↑(FractionalIdeal.extended L hf
      (FractionalIdeal.dual A K 1)) : Submodule SB L) := hx
    rw [FractionalIdeal.coe_extended_eq_span] at hx_sub
    have h_image_eq : ∀ (s : Set L), IsLocalization.map L (algebraMap B SB) hf '' s = s := by
      intro s; ext y; simp only [Set.mem_image, h_map_eq]
      exact ⟨fun ⟨a, ha, he⟩ => he ▸ ha, fun hy => ⟨y, hy, rfl⟩⟩
    rw [h_image_eq] at hx_sub


    exact Submodule.span_le.mpr (fun y hy => dual_B_le_dual_SB y hy) hx_sub
  ·
    intro x hx

    show x ∈ (↑((FractionalIdeal.extendedHomₐ L SB)
      (FractionalIdeal.dual A K 1)) : Submodule SB L)
    rw [show (↑((FractionalIdeal.extendedHomₐ L SB)
      (FractionalIdeal.dual A K 1)) : Submodule SB L) =
      Submodule.span SB (↑(FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) : Set L) from by
        rw [FractionalIdeal.extendedHomₐ]
        simp only [FractionalIdeal.extendedHom_apply]
        rw [FractionalIdeal.coe_extended_eq_span]
        congr 1
        ext y; simp only [Set.mem_image, h_map_eq]
        exact ⟨fun ⟨a, ha, he⟩ => he ▸ ha, fun hy => ⟨y, hy, rfl⟩⟩]

    classical


    rw [FractionalIdeal.mem_dual hone_SB] at hx

    haveI : IsNoetherianRing A := inferInstance
    haveI : Module.Finite A B := IsIntegralClosure.finite A K L B

    obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := A) (M := B)

    have hb_in_SB : ∀ b : B, algebraMap B L b ∈
        (1 : FractionalIdeal (nonZeroDivisors SB) L) := by
      intro b
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨algebraMap B SB b, by rw [IsScalarTower.algebraMap_apply B SB L]⟩
    have h_tr_SA : ∀ b : B, (Algebra.traceForm K L x) (algebraMap B L b) ∈ (algebraMap SA K).range :=
      fun b => hx _ (hb_in_SB b)

    choose sa_fun hsa_fun using fun b : B => (h_tr_SA b)
    choose surj_fun hsurj_fun using fun b : B => IsLocalization.surj S (sa_fun b)

    let s_fun : B → A := fun b => ((surj_fun b).2 : A)
    let s_prod : A := T.prod s_fun
    have hs_prod : s_prod ∈ S := Submonoid.prod_mem _ (fun b _ => (surj_fun b).2.2)
    have hs_prod_nzd : s_prod ∈ nonZeroDivisors A := hS hs_prod
    have hs_prod_K_ne : (algebraMap A K) s_prod ≠ 0 :=
      map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective A K) hs_prod_nzd
    have hs_prod_L_ne : algebraMap A L s_prod ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A K L]; simp [hs_prod_K_ne]

    have h_prod_trace_gen : ∀ b ∈ T,
        algebraMap A K s_prod * (Algebra.traceForm K L x) (algebraMap B L b) ∈
          (algebraMap A K).range := by
      intro b hb
      rw [← hsa_fun b]
      have hsurj := hsurj_fun b
      have hsurj_K : algebraMap SA K (sa_fun b) * algebraMap A K ((surj_fun b).2 : A) =
          algebraMap A K (surj_fun b).1 := by
        have := congr_arg (algebraMap SA K) hsurj
        simp only [map_mul] at this
        rwa [← IsScalarTower.algebraMap_apply A SA K, ← IsScalarTower.algebraMap_apply A SA K] at this
      have h_split : s_prod = s_fun b * (T.erase b).prod s_fun := by
        exact (Finset.mul_prod_erase T s_fun hb).symm
      rw [h_split, map_mul, mul_assoc]
      rw [show (algebraMap A K) (s_fun b) *
          ((algebraMap A K) ((T.erase b).prod s_fun) * (algebraMap SA K) (sa_fun b)) =
          (algebraMap A K) ((T.erase b).prod s_fun) *
          ((algebraMap SA K) (sa_fun b) * (algebraMap A K) ((surj_fun b).2 : A)) from by ring,
        hsurj_K]
      exact ⟨(T.erase b).prod s_fun * (surj_fun b).1, map_mul _ _ _⟩

    have h_prod_trace_all : ∀ b : B,
        algebraMap A K s_prod * (Algebra.traceForm K L x) (algebraMap B L b) ∈
          (algebraMap A K).range := by
      intro b
      have hb_span : b ∈ Submodule.span A (↑T : Set B) := by rw [hT]; exact Submodule.mem_top
      induction hb_span using Submodule.span_induction with
      | mem b hb => exact h_prod_trace_gen b hb
      | zero => simp only [map_zero, mul_zero]; exact ⟨0, map_zero _⟩
      | add b1 b2 _ _ ih1 ih2 =>
        simp only [map_add, mul_add]
        obtain ⟨c1, hc1⟩ := ih1; obtain ⟨c2, hc2⟩ := ih2
        exact ⟨c1 + c2, by rw [map_add, hc1, hc2]⟩
      | smul a' b _ ih =>
        obtain ⟨c_val, hc_val⟩ := ih
        have h_trace_smul : (Algebra.traceForm K L x) (algebraMap B L (a' • b)) =
            algebraMap A K a' * (Algebra.traceForm K L x) (algebraMap B L b) := by
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A B L,
            IsScalarTower.algebraMap_apply A K L]
          simp only [Algebra.traceForm_apply]
          rw [show x * ((algebraMap K L) ((algebraMap A K) a') * (algebraMap B L) b) =
              (algebraMap K L) ((algebraMap A K) a') * (x * (algebraMap B L) b) from by ring,
            ← Algebra.smul_def, (Algebra.trace K L).map_smul, smul_eq_mul]
        rw [h_trace_smul, show (algebraMap A K) s_prod *
            ((algebraMap A K) a' * ((traceForm K L) x) ((algebraMap B L) b)) =
            (algebraMap A K) a' * ((algebraMap A K) s_prod * ((traceForm K L) x) ((algebraMap B L) b))
            from by ring, ← hc_val]
        exact ⟨a' * c_val, by rw [map_mul]⟩


    have h_scaled_dual : algebraMap K L (algebraMap A K s_prod) * x ∈
        FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L) := by
      rw [FractionalIdeal.mem_dual hone_B]
      intro m hm
      rw [FractionalIdeal.mem_one_iff] at hm
      obtain ⟨m_b, rfl⟩ := hm
      rw [Algebra.traceForm_apply, mul_assoc, ← Algebra.smul_def, (Algebra.trace K L).map_smul,
        smul_eq_mul, ← Algebra.traceForm_apply]
      exact h_prod_trace_all m_b

    let y := algebraMap K L (algebraMap A K s_prod) * x
    have hy_dual : y ∈ FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L) :=
      h_scaled_dual
    have hx_eq : x = algebraMap K L ((algebraMap A K s_prod)⁻¹) * y := by
      simp only [map_inv₀, y]
      rw [← mul_assoc, inv_mul_cancel₀, one_mul]
      rw [map_ne_zero_iff _ (algebraMap K L).injective]; exact hs_prod_K_ne
    rw [hx_eq]

    have hy_gen : y ∈ (↑(FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) : Set L) :=
      hy_dual


    have h_ab_s_in_submonoid : algebraMap A B s_prod ∈ Algebra.algebraMapSubmonoid B S :=
      ⟨s_prod, hs_prod, rfl⟩
    have h_sb_unit : IsUnit (algebraMap B SB (algebraMap A B s_prod)) :=
      IsLocalization.map_units SB ⟨algebraMap A B s_prod, h_ab_s_in_submonoid⟩

    let sb_inv := (h_sb_unit.unit⁻¹ : SBˣ).val
    have h_sb_inv_spec : algebraMap SB L sb_inv * algebraMap A L s_prod = 1 := by
      have := h_sb_unit.val_inv_mul
      have h1 := congr_arg (algebraMap SB L) this
      simp only [map_mul, map_one] at h1
      rw [← IsScalarTower.algebraMap_apply B SB L,
          ← IsScalarTower.algebraMap_apply A B L] at h1
      exact h1
    have h_inv_eq : algebraMap K L ((algebraMap A K s_prod)⁻¹) = algebraMap SB L sb_inv := by
      have h_prod_L : algebraMap A L s_prod = algebraMap K L (algebraMap A K s_prod) := by
        rw [IsScalarTower.algebraMap_apply A K L]
      rw [map_inv₀, ← h_prod_L]
      rw [eq_comm, inv_eq_of_mul_eq_one_left]
      exact h_sb_inv_spec
    rw [h_inv_eq]


    have h_smul : algebraMap SB L sb_inv * y = sb_inv • y := by
      rw [Algebra.smul_def]
    rw [h_smul]
    exact Submodule.smul_mem _ sb_inv (Submodule.subset_span hy_gen)

include hS K L in
theorem differentIdeal_localization :
    Ideal.map (algebraMap B SB) (differentIdeal A B) = differentIdeal SA SB := by

  have localization_dual_comm :
      (FractionalIdeal.extendedHomₐ L SB)
        (FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) =
        FractionalIdeal.dual SA K (1 : FractionalIdeal (nonZeroDivisors SB) L) :=
    localization_dual_comm_axiom A K L B S hS SA SB

  rw [← FractionalIdeal.coeIdeal_inj (K := L)]

  rw [← FractionalIdeal.extendedHomₐ_coeIdeal_eq_map (K := L) L SB (differentIdeal A B)]

  rw [coeIdeal_differentIdeal A K L B]

  rw [map_inv₀]

  rw [localization_dual_comm]

  exact (coeIdeal_differentIdeal SA K L SB).symm

end DifferentLocalization

section DifferentCompletion

open TensorProduct


variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]


variable (Khat : Type*) [Field Khat]
variable (Lhat : Type u) [Field Lhat]
variable (Ahat : Type*) [CommRing Ahat] [IsDomain Ahat]
variable (Bhat : Type*) [CommRing Bhat] [IsDomain Bhat]


variable [Algebra A Ahat] [Algebra B Bhat]
variable [Algebra Ahat Khat] [Algebra Bhat Lhat]
variable [Algebra Ahat Bhat] [Algebra A Bhat]
variable [Algebra Khat Lhat] [Algebra Ahat Lhat]
variable [Algebra B Lhat]


variable [IsScalarTower A Ahat Bhat] [IsScalarTower A B Bhat]
variable [IsScalarTower Ahat Khat Lhat] [IsScalarTower Ahat Bhat Lhat]
variable [IsScalarTower B Bhat Lhat]


variable [IsFractionRing Ahat Khat] [IsIntegrallyClosed Ahat]
variable [IsFractionRing Bhat Lhat]
variable [FiniteDimensional Khat Lhat]
variable [Algebra.IsSeparable Khat Lhat]
variable [IsIntegralClosure Bhat Ahat Lhat]
variable [IsDedekindDomain Bhat]
variable [Module.IsTorsionFree Ahat Bhat] [Module.IsTorsionFree B Bhat]
variable [Nontrivial Bhat] [NoZeroDivisors Bhat]

theorem trace_completion_compat
    (A : Type*) (K : Type*) (L : Type u) (B : Type*)
    [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
    [FiniteDimensional K L] [IsIntegralClosure B A L]
    [Algebra.IsSeparable K L]
    [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    (Khat : Type*) [Field Khat]
    (Lhat : Type u) [Field Lhat]
    (Ahat : Type*) [CommRing Ahat] [IsDomain Ahat]
    (Bhat : Type*) [CommRing Bhat] [IsDomain Bhat]
    [Algebra A Ahat] [Algebra B Bhat]
    [Algebra Ahat Khat] [Algebra Bhat Lhat]
    [Algebra Ahat Bhat] [Algebra A Bhat]
    [Algebra Khat Lhat] [Algebra Ahat Lhat] [Algebra B Lhat]
    [Algebra K Khat] [Algebra L Lhat] [Algebra A Khat] [Algebra K Lhat]
    [IsScalarTower A Ahat Bhat] [IsScalarTower A B Bhat]
    [IsScalarTower Ahat Khat Lhat] [IsScalarTower Ahat Bhat Lhat]
    [IsScalarTower B Bhat Lhat]
    [IsScalarTower A K Khat] [IsScalarTower K Khat Lhat]
    [IsScalarTower K L Lhat]
    [IsFractionRing Ahat Khat] [IsFractionRing Bhat Lhat]
    [FiniteDimensional Khat Lhat] [Algebra.IsSeparable Khat Lhat]
    [IsIntegralClosure Bhat Ahat Lhat] [IsDedekindDomain Bhat]
    [Module.IsTorsionFree Ahat Bhat] [Module.IsTorsionFree B Bhat]
    [Nontrivial Bhat] [NoZeroDivisors Bhat]
    (e : Lhat ≃ₐ[Khat] (Khat ⊗[K] L))
    (he : ∀ y : L, e (algebraMap L Lhat y) = (1 : Khat) ⊗ₜ[K] y)
    (x : L) :
    algebraMap K Khat (Algebra.trace K L x) = Algebra.trace Khat Lhat (algebraMap L Lhat x) := by
  have h1 : Algebra.trace Khat Lhat (algebraMap L Lhat x) =
    Algebra.trace Khat (Khat ⊗[K] L) (e (algebraMap L Lhat x)) :=
    (Algebra.trace_eq_of_algEquiv e (algebraMap L Lhat x)).symm
  rw [h1, he x]
  have h2 : (Algebra.trace Khat (Khat ⊗[K] L)) ((1 : Khat) ⊗ₜ[K] x) =
    (LinearMap.trace Khat (Khat ⊗[K] L))
      ((Algebra.lmul Khat (Khat ⊗[K] L)) ((1 : Khat) ⊗ₜ[K] x)) := by
    rw [Algebra.trace_apply]
  rw [h2, ← Algebra.baseChange_lmul (A := Khat) x,
      LinearMap.trace_baseChange (Algebra.lmul K L x) Khat,
      ← Algebra.trace_apply K]




variable [Algebra K Khat] [Algebra L Lhat] [Algebra A Khat] [Algebra K Lhat]
variable [IsScalarTower A K Khat] [IsScalarTower K Khat Lhat]
variable [IsScalarTower K L Lhat] [IsScalarTower B L Lhat]
variable [Algebra.IsIntegral B Bhat]



end DifferentCompletion

section Discriminant

variable {n : ℕ} (R : Type*) {S : Type*}
  [CommRing R] [CommRing S] [Algebra R S]

def disc (x : Fin n → S) : R := Algebra.discr R x

theorem disc_eq_det_traceMatrix (x : Fin n → S) :
    disc R x = (Algebra.traceMatrix R x).det :=
  Algebra.discr_def R x

theorem disc_traceMatrix_entry (x : Fin n → S) (i j : Fin n) :
    Algebra.traceMatrix R x i j = Algebra.trace R S (x i * x j) := by
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]

end Discriminant

section DiscriminantEmbeddings

variable (K : Type*) {L : Type*} (E : Type*) [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra K E] [Module.Finite K L] [IsAlgClosed E]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem discr_eq_det_embeddingsMatrix_sq
    (b : ι → L) [Algebra.IsSeparable K L] (e : ι ≃ (L →ₐ[K] E)) :
    algebraMap K E (Algebra.discr K b) =
      (Algebra.embeddingsMatrixReindex K E b e).det ^ 2 :=
  Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two K E b e

theorem discr_powerBasis_eq_prod
    (pb : PowerBasis K L) (e : Fin pb.dim ≃ (L →ₐ[K] E)) [Algebra.IsSeparable K L] :
    algebraMap K E (Algebra.discr K pb.basis) =
      ∏ i : Fin pb.dim, ∏ j ∈ Finset.Ioi i, (e j pb.gen - e i pb.gen) ^ 2 :=
  Algebra.discr_powerBasis_eq_prod K E pb e

end DiscriminantEmbeddings

section PolynomialDiscriminant

variable {R : Type*} [CommRing R]

open Polynomial in
def polyDiscr (f : R[X]) : R := f.discr

open Polynomial in
theorem polyDiscr_eq_discr (f : R[X]) : polyDiscr f = f.discr := rfl

open Polynomial in
theorem polyDiscr_resultant {f : R[X]} (hf : 0 < f.degree) :
    f.resultant f.derivative f.natDegree (f.natDegree - 1) =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff * polyDiscr f :=
  Polynomial.resultant_deriv hf

end PolynomialDiscriminant

section LatticeDiscriminant

variable (A K : Type*) {L : Type u}
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L]
  [FiniteDimensional K L]

def latticeDiscrSet (M : Submodule A L) : Set K :=
  { d : K | ∃ b : Fin (Module.finrank K L) → L,
      (∀ i, b i ∈ M) ∧ d = Algebra.discr K b }

def latticeDiscriminant (M : Submodule A L) : Submodule A K :=
  Submodule.span A (latticeDiscrSet A K M)

set_option linter.unusedSectionVars false in
theorem latticeDiscriminant_eq_span (M : Submodule A L) :
    latticeDiscriminant A K M = Submodule.span A (latticeDiscrSet A K M) :=
  rfl

set_option linter.unusedSectionVars false in
theorem discr_mem_latticeDiscriminant
    {M : Submodule A L}
    {b : Fin (Module.finrank K L) → L} (hb : ∀ i, b i ∈ M) :
    Algebra.discr K b ∈ latticeDiscriminant A K M :=
  Submodule.subset_span ⟨b, hb, rfl⟩

set_option linter.unusedSectionVars false in
theorem latticeDiscriminant_mono {M N : Submodule A L} (h : M ≤ N) :
    latticeDiscriminant A K M ≤ latticeDiscriminant A K N := by
  apply Submodule.span_mono
  intro d ⟨b, hb, hd⟩
  exact ⟨b, fun i => h (hb i), hd⟩

end LatticeDiscriminant

section FreeLatticeDiscriminant

variable (A K : Type*) {L : Type u}
  [CommRing A] [IsDomain A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L]
  [FiniteDimensional K L]

set_option linter.unusedSectionVars false in
theorem discr_change_of_basis (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (x : Fin (Module.finrank K L) → L) :
    Algebra.discr K x = (bK.toMatrix x).det ^ 2 * Algebra.discr K bK := by
  conv_lhs => rw [show x = (⇑bK) ᵥ* ((bK.toMatrix x).map (algebraMap K L))
    from (bK.toMatrix_map_vecMul x).symm]
  exact Algebra.discr_of_matrix_vecMul (⇑bK) (bK.toMatrix x)

omit [IsDomain A] in
theorem discr_mem_span_of_basis
    (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (M : Submodule A L)
    (hM : ∀ x : L, x ∈ M → x ∈ Submodule.span A (Set.range (⇑bK)))
    (x : Fin (Module.finrank K L) → L) (hx : ∀ i, x i ∈ M) :
    Algebra.discr K x ∈ Submodule.span A {Algebra.discr K (⇑bK)} := by
  classical
  have hcob := discr_change_of_basis K bK x
  have hentries : ∀ i j, bK.toMatrix x i j ∈ (algebraMap A K).range := by
    intro i j
    simp only [Module.Basis.toMatrix_apply]
    have hxj : x j ∈ Submodule.span A (Set.range (⇑bK)) := hM (x j) (hx j)
    rw [Submodule.mem_span_range_iff_exists_fun] at hxj
    obtain ⟨c, hc⟩ := hxj
    rw [show x j = ∑ k, algebraMap A K (c k) • bK k from by
      rw [← hc]; congr 1; ext k
      rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply A K L],
      Module.Basis.repr_sum_self]
    exact ⟨c i, rfl⟩
  set PA : Matrix _ _ A := Matrix.of (fun i j => (hentries i j).choose)
  have hPA : bK.toMatrix x = PA.map (algebraMap A K) := by
    ext i j; simp only [Matrix.map_apply]
    exact (hentries i j).choose_spec.symm
  rw [hcob, hPA, show (PA.map (algebraMap A K)).det = algebraMap A K PA.det from
    (RingHom.map_det (algebraMap A K) PA).symm,
    show (algebraMap A K PA.det) ^ 2 = algebraMap A K (PA.det ^ 2) from (map_pow _ _ _).symm,
    ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

omit [IsDomain A] in
theorem latticeDiscriminant_principal
    (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (M : Submodule A L)
    (hM_le : ∀ x : L, x ∈ M → x ∈ Submodule.span A (Set.range (⇑bK)))
    (hM_ge : ∀ i, bK i ∈ M) :
    latticeDiscriminant A K M = Submodule.span A {Algebra.discr K (⇑bK)} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro d ⟨b, hb, hd⟩
    rw [hd]
    exact discr_mem_span_of_basis A K bK M hM_le b hb
  · apply Submodule.span_le.mpr
    intro d hd
    rw [Set.mem_singleton_iff.mp hd]
    exact Submodule.subset_span ⟨⇑bK, hM_ge, rfl⟩

omit [IsDomain A] [IsScalarTower A K L] in
theorem latticeDiscriminant_ne_bot [Algebra.IsSeparable K L]
    (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (M : Submodule A L) (hM_ge : ∀ i, bK i ∈ M) :
    latticeDiscriminant A K M ≠ ⊥ := by
  intro h
  have hd : Algebra.discr K (⇑bK) ∈ latticeDiscriminant A K M :=
    Submodule.subset_span ⟨⇑bK, hM_ge, rfl⟩
  rw [h] at hd
  simp only [Submodule.mem_bot] at hd
  exact Algebra.discr_not_zero_of_basis K bK hd

omit [IsDomain A] in
theorem latticeDiscriminant_eq_imp_eq [Algebra.IsSeparable K L]
    (hAK : Function.Injective (algebraMap A K))
    (M M' : Submodule A L) (hle : M' ≤ M)
    (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (hM_le : ∀ x : L, x ∈ M → x ∈ Submodule.span A (Set.range (⇑bK)))
    (hM_ge : ∀ i, bK i ∈ M)
    (bK' : Module.Basis (Fin (Module.finrank K L)) K L)
    (hM'_le : ∀ x : L, x ∈ M' → x ∈ Submodule.span A (Set.range (⇑bK')))
    (hM'_ge : ∀ i, bK' i ∈ M')
    (hD : latticeDiscriminant A K M' = latticeDiscriminant A K M) :
    M' = M := by
  classical

  have hbK'_in_span : ∀ i, bK' i ∈ Submodule.span A (Set.range (⇑bK)) :=
    fun i => hM_le _ (hle (hM'_ge i))
  have hentries : ∀ i j, bK.toMatrix (⇑bK') i j ∈ (algebraMap A K).range := by
    intro i j
    simp only [Module.Basis.toMatrix_apply]
    have hxj := hbK'_in_span j
    rw [Submodule.mem_span_range_iff_exists_fun] at hxj
    obtain ⟨c, hc⟩ := hxj
    rw [show bK' j = ∑ k, algebraMap A K (c k) • bK k from by
      rw [← hc]; congr 1; ext k
      rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply A K L],
      Module.Basis.repr_sum_self]
    exact ⟨c i, rfl⟩
  set PA : Matrix _ _ A := Matrix.of (fun i j => (hentries i j).choose)
  have hPA : bK.toMatrix (⇑bK') = PA.map (algebraMap A K) := by
    ext i j; simp only [Matrix.map_apply]
    exact (hentries i j).choose_spec.symm

  have hdiscr : Algebra.discr K (⇑bK') =
      (algebraMap A K PA.det) ^ 2 * Algebra.discr K bK := by
    conv_lhs => rw [show (⇑bK' : Fin _ → L) =
      (⇑bK) ᵥ* ((bK.toMatrix (⇑bK')).map (algebraMap K L))
      from (bK.toMatrix_map_vecMul (⇑bK')).symm]
    rw [hPA]
    rw [Algebra.discr_of_matrix_vecMul (⇑bK) (PA.map (algebraMap A K))]
    congr 1; congr 1
    exact (RingHom.map_det (algebraMap A K) PA).symm

  have hD_eq : latticeDiscriminant A K M = Submodule.span A {Algebra.discr K (⇑bK)} :=
    latticeDiscriminant_principal A K bK M hM_le hM_ge
  have hD'_eq : latticeDiscriminant A K M' = Submodule.span A {Algebra.discr K (⇑bK')} :=
    latticeDiscriminant_principal A K bK' M' hM'_le hM'_ge

  have hbK_in : Algebra.discr K (⇑bK) ∈ Submodule.span A {Algebra.discr K (⇑bK')} := by
    rw [← hD'_eq, hD, hD_eq]
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [Submodule.mem_span_singleton] at hbK_in
  obtain ⟨c, hc⟩ := hbK_in


  have hdiscr_ne : Algebra.discr K (⇑bK) ≠ 0 := Algebra.discr_not_zero_of_basis K bK

  have hunit_K : algebraMap A K c * (algebraMap A K PA.det) ^ 2 = 1 := by
    have h1 : Algebra.discr K (⇑bK) =
        algebraMap A K c * ((algebraMap A K PA.det) ^ 2 * Algebra.discr K bK) := by
      rw [← hdiscr, ← hc, Algebra.smul_def]
    have h2 : algebraMap A K c * (algebraMap A K PA.det) ^ 2 * Algebra.discr K bK =
        1 * Algebra.discr K bK := by
      rw [mul_assoc, ← h1, one_mul]
    exact mul_right_cancel₀ hdiscr_ne h2

  have hunit_A : c * PA.det ^ 2 = 1 := by
    apply hAK
    rw [map_mul, map_pow, map_one]
    exact hunit_K

  have hdetPA_unit : IsUnit PA.det := by
    rw [isUnit_iff_exists_inv]
    refine ⟨c * PA.det, ?_⟩
    have : PA.det * (c * PA.det) = c * PA.det ^ 2 := by ring
    rw [this, hunit_A]

  have hbK_recover : ∀ i, bK i ∈ Submodule.span A (Set.range (⇑bK')) := by

    have hbK'_eq : (⇑bK' : Fin _ → L) =
        (⇑bK) ᵥ* (PA.map (algebraMap A L)) := by
      ext i
      have := bK.toMatrix_map_vecMul (⇑bK')
      rw [hPA] at this
      rw [show (PA.map (algebraMap A K)).map (algebraMap K L) = PA.map (algebraMap A L) from by
        ext i j; simp only [Matrix.map_apply, ← IsScalarTower.algebraMap_apply A K L]] at this
      exact congr_fun this.symm i

    have hbK_eq : (⇑bK : Fin _ → L) =
        (⇑bK') ᵥ* (PA⁻¹.map (algebraMap A L)) := by
      rw [hbK'_eq, Matrix.vecMul_vecMul]
      have : PA.map (algebraMap A L) * (PA⁻¹).map (algebraMap A L) = 1 := by
        rw [show PA.map (algebraMap A L) = (algebraMap A L).mapMatrix PA from rfl,
            show (PA⁻¹).map (algebraMap A L) = (algebraMap A L).mapMatrix PA⁻¹ from rfl,
            ← map_mul, Matrix.mul_nonsing_inv PA hdetPA_unit, map_one]
      rw [this, Matrix.vecMul_one]

    intro i
    rw [hbK_eq]
    show (bK' ⬝ᵥ fun j => (algebraMap A L) (PA⁻¹ j i)) ∈ _
    rw [dotProduct]
    apply Submodule.sum_mem
    intro j _
    rw [mul_comm (bK' j) _, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

  have hM_le_M' : M ≤ M' := by
    intro x hx
    have hx_span := hM_le x hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx_span
    obtain ⟨c_x, hcx⟩ := hx_span
    rw [← hcx]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    have := hbK_recover j
    rw [Submodule.mem_span_range_iff_exists_fun] at this
    obtain ⟨c_bK, hcbK⟩ := this
    rw [← hcbK]
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (hM'_ge k)
  exact le_antisymm hle hM_le_M'

end FreeLatticeDiscriminant

section LatticeDiscriminantFractional

variable (A K : Type*) {L : Type u}
  [CommRing A] [IsDomain A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L]
  [IsFractionRing A K]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

omit [IsDomain A] [Algebra.IsSeparable K L] in
theorem latticeDiscriminant_isFractional
    (M : Submodule A L)
    (bN : Module.Basis (Fin (Module.finrank K L)) K L)
    (hMN : ∀ x : L, x ∈ M → x ∈ Submodule.span A (Set.range (⇑bN))) :
    IsFractional (nonZeroDivisors A) (latticeDiscriminant A K M) := by

  have hle : latticeDiscriminant A K M ≤
      (↑(FractionalIdeal.spanSingleton (nonZeroDivisors A)
        (Algebra.discr K (⇑bN))) : Submodule A K) := by
    rw [FractionalIdeal.coe_spanSingleton]
    apply Submodule.span_le.mpr
    intro d ⟨b, hb, hd⟩
    rw [hd]
    exact discr_mem_span_of_basis A K bN M hMN b hb
  exact FractionalIdeal.isFractional_of_le hle

omit [IsDomain A] [IsFractionRing A K] [IsScalarTower A K L] in
theorem latticeDiscriminant_ne_bot_of_basis
    (M : Submodule A L)
    (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (hM_ge : ∀ i, bK i ∈ M) :
    latticeDiscriminant A K M ≠ ⊥ :=
  latticeDiscriminant_ne_bot A K bK M hM_ge

omit [IsDomain A] in
theorem latticeDiscriminant_isFractional_and_ne_bot
    (M : Submodule A L)
    (bK : Module.Basis (Fin (Module.finrank K L)) K L)
    (hM_ge : ∀ i, bK i ∈ M)
    (bN : Module.Basis (Fin (Module.finrank K L)) K L)
    (hMN : ∀ x : L, x ∈ M → x ∈ Submodule.span A (Set.range (⇑bN))) :
    IsFractional (nonZeroDivisors A) (latticeDiscriminant A K M) ∧
    latticeDiscriminant A K M ≠ ⊥ :=
  ⟨latticeDiscriminant_isFractional A K M bN hMN,
   latticeDiscriminant_ne_bot_of_basis A K M bK hM_ge⟩

end LatticeDiscriminantFractional

section MonogenicDifferent


variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B]

variable (α : B)

include K L in
set_option linter.unusedSectionVars false in
theorem differentIdeal_eq_span_derivative
    (hα_gen : Algebra.adjoin A {α} = ⊤)
    (hα_field : @Algebra.adjoin K L _ _ _ {(algebraMap B L) α} = ⊤) :
    differentIdeal A B =
      Ideal.span {Polynomial.aeval α (Polynomial.derivative (minpoly A α))} := by
  have hcond := conductor_mul_differentIdeal A K L α hα_field
  have htop : conductor A α = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    rw [mem_conductor_iff]
    intro b
    rw [one_mul]
    exact hα_gen ▸ Algebra.mem_top
  rw [htop, Ideal.top_mul] at hcond
  exact hcond

include K L in
set_option linter.unusedSectionVars false in
theorem differentIdeal_eq_span_derivative_powerBasis
    (pb : PowerBasis A B)
    (hpb_field : @Algebra.adjoin K L _ _ _ {(algebraMap B L) pb.gen} = ⊤) :
    differentIdeal A B =
      Ideal.span {Polynomial.aeval pb.gen
        (Polynomial.derivative (minpoly A pb.gen))} := by
  have hcond := conductor_mul_differentIdeal A K L pb.gen hpb_field
  have htop : conductor A pb.gen = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    rw [mem_conductor_iff]
    intro b
    rw [one_mul]
    exact pb.adjoin_gen_eq_top ▸ Algebra.mem_top
  rw [htop, Ideal.top_mul] at hcond
  exact hcond

end MonogenicDifferent

section ElementDifferent

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

open Classical in
def elementDifferent (α : L) : L :=
  if IntermediateField.adjoin K {α} = ⊤
  then Polynomial.aeval α (Polynomial.derivative (minpoly K α))
  else 0

theorem elementDifferent_of_adjoin_eq_top {α : L}
    (h : IntermediateField.adjoin K {α} = ⊤) :
    elementDifferent K α =
      Polynomial.aeval α (Polynomial.derivative (minpoly K α)) := by
  classical
  simp [elementDifferent, h]

theorem elementDifferent_of_adjoin_ne_top {α : L}
    (h : IntermediateField.adjoin K {α} ≠ ⊤) :
    elementDifferent K α = 0 := by
  classical
  simp [elementDifferent, h]

theorem elementDifferent_of_powerBasis (pb : PowerBasis K L) :
    elementDifferent K pb.gen =
      Polynomial.aeval pb.gen (Polynomial.derivative (minpoly K pb.gen)) := by
  exact elementDifferent_of_adjoin_eq_top K
    (IntermediateField.adjoin_eq_top_of_algebra K {pb.gen} pb.adjoin_gen_eq_top)

end ElementDifferent

section ElementDifferentB

variable (A : Type*) (K : Type*) {L : Type u} (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

def elementDifferentB (α : B) : B := by
  classical
  exact if Algebra.adjoin K {algebraMap B L α} = ⊤
    then Polynomial.aeval α (Polynomial.derivative (minpoly A α))
    else 0

omit [Algebra A K] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] in
theorem elementDifferentB_of_adjoin_eq_top {α : B}
    (h : Algebra.adjoin K {algebraMap B L α} = ⊤) :
    elementDifferentB A K (L := L) B α =
      Polynomial.aeval α (Polynomial.derivative (minpoly A α)) := by
  classical
  simp [elementDifferentB, h]

omit [Algebra A K] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] in
theorem elementDifferentB_of_adjoin_ne_top {α : B}
    (h : Algebra.adjoin K {algebraMap B L α} ≠ ⊤) :
    elementDifferentB A K (L := L) B α = 0 := by
  classical
  simp [elementDifferentB, h]

end ElementDifferentB

section DifferentGeneratedByElements

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain B] [Module.IsTorsionFree A B]

omit [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B] in
lemma span_elementDifferentB_le_differentIdeal :
    Ideal.span (Set.range (elementDifferentB A K (L := L) B)) ≤ differentIdeal A B := by
  rw [Ideal.span_le]
  rintro _ ⟨b, rfl⟩
  simp only [elementDifferentB]
  split_ifs with h
  · exact aeval_derivative_mem_differentIdeal A K L b h
  · exact (differentIdeal A B).zero_mem


omit [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B] in
lemma conductor_mul_differentIdeal_le_span (x : B)
    (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) :
    conductor A x * differentIdeal A B ≤
      Ideal.span (Set.range (elementDifferentB A K (L := L) B)) := by
  rw [conductor_mul_differentIdeal A K L x hx]
  apply Ideal.span_mono
  intro b hb
  rw [Set.mem_singleton_iff] at hb
  rw [hb]
  exact ⟨x, by classical simp [elementDifferentB, hx]⟩



end DifferentGeneratedByElements

section DifferentValuationBounds

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A : Type*) (B : Type*)
  [CommRing A] [IsDomain A] [IsDedekindDomain A]
  [CommRing B] [IsDomain B] [IsDedekindDomain B]
  [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

open IsDedekindDomain

def idealValuation (𝔮 : HeightOneSpectrum B) (I : Ideal B) : ℕ :=
  multiplicity 𝔮.asIdeal I

def ramificationIndex (𝔮 : HeightOneSpectrum B) : ℕ :=
  Ideal.ramificationIdx (𝔮.asIdeal.comap (algebraMap A B)) 𝔮.asIdeal

def IsTamelyRamified (𝔮 : HeightOneSpectrum B) : Prop :=
  ¬ (ringChar (B ⧸ 𝔮.asIdeal) ∣ ramificationIndex A B 𝔮)

def valuationOfRamIdx (𝔮 : HeightOneSpectrum B) : ℕ :=
  idealValuation B 𝔮 (Ideal.span {(ramificationIndex A B 𝔮 : B)})

theorem different_valuation_lower_bound
    (𝔮 : HeightOneSpectrum B)
    (hsep : Algebra.IsSeparable
      (A ⧸ (𝔮.asIdeal.comap (algebraMap A B)))
      (B ⧸ 𝔮.asIdeal)) :
    ramificationIndex A B 𝔮 - 1 ≤ idealValuation B 𝔮 (differentIdeal A B) := by
  unfold ramificationIndex idealValuation
  set p := 𝔮.asIdeal.comap (algebraMap A B) with hp_def
  set e := Ideal.ramificationIdx p 𝔮.asIdeal with he_def
  by_cases hp0 : p = ⊥
  · rw [show e = 0 from by rw [he_def, hp0, Ideal.ramificationIdx_bot]]
    exact Nat.zero_le _
  haveI : p.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔮.asIdeal
  have hpe : 𝔮.asIdeal ^ e ∣ Ideal.map (algebraMap A B) p :=
    Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx
  have hdvd : 𝔮.asIdeal ^ (e - 1) ∣ differentIdeal A B :=
    pow_sub_one_dvd_differentIdeal A 𝔮.asIdeal e hp0 hpe
  have hdiff_ne_bot : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  exact (FiniteMultiplicity.of_prime_left 𝔮.prime hdiff_ne_bot).le_multiplicity_of_pow_dvd hdvd




end DifferentValuationBounds

section FiniteRamification


variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]

open IsDedekindDomain

include K L in
set_option linter.unusedSectionVars false in
theorem different_ne_bot_of_AKLB : differentIdeal A B ≠ ⊥ := by
  intro h
  have h1 := coeIdeal_differentIdeal A K L B
  rw [h] at h1
  simp at h1
  exact FractionalIdeal.dual_ne_zero A K
    (show (1 : FractionalIdeal (nonZeroDivisors B) L) ≠ 0 from one_ne_zero) h1.symm

include K L in
set_option linter.unusedSectionVars false in
theorem finite_ramified_primes :
    Set.Finite {𝔮 : HeightOneSpectrum B | 𝔮.asIdeal ∣ differentIdeal A B} :=
  Ideal.finite_factors (different_ne_bot_of_AKLB A K L B)

include K L in
set_option linter.unusedSectionVars false in
theorem finite_ramified_primes_of_base :
    Set.Finite ((fun 𝔮 : HeightOneSpectrum B => 𝔮.asIdeal.comap (algebraMap A B)) ''
      {𝔮 : HeightOneSpectrum B | 𝔮.asIdeal ∣ differentIdeal A B}) :=
  (finite_ramified_primes A K L B).image _

end FiniteRamification

section ExtensionDiscriminant

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [FiniteDimensional K L]

def imageOfB : Submodule A L :=
  Subalgebra.toSubmodule (IsScalarTower.toAlgHom A B L).range

theorem mem_imageOfB {x : L} :
    x ∈ imageOfB A L B ↔ ∃ b : B, algebraMap B L b = x := by
  simp only [imageOfB, Subalgebra.mem_toSubmodule, AlgHom.mem_range,
    IsScalarTower.coe_toAlgHom']

instance imageOfB_finite [Module.Finite A B] : Module.Finite A ↥(imageOfB A L B) := by
  have : Module.Finite A ((IsScalarTower.toAlgHom A B L).toLinearMap.range) :=
    Module.Finite.range (IsScalarTower.toAlgHom A B L).toLinearMap
  convert this

def extensionDiscriminant : Submodule A K :=
  latticeDiscriminant A K (imageOfB A L B)

omit [IsScalarTower A K L] [FiniteDimensional K L] in
theorem extensionDiscriminant_eq :
    extensionDiscriminant A K L B = latticeDiscriminant A K (imageOfB A L B) :=
  rfl

theorem discr_mem_extensionDiscriminant
    {b : Fin (Module.finrank K L) → L} (hb : ∀ i, b i ∈ imageOfB A L B) :
    Algebra.discr K b ∈ extensionDiscriminant A K L B :=
  discr_mem_latticeDiscriminant A K hb

end ExtensionDiscriminant

section DiscriminantCompletion


variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain A] [IsDedekindDomain B]


variable (Ahat : Type*) (Khat : Type*)
  [CommRing Ahat] [IsDomain Ahat] [Field Khat]
  [Algebra Ahat Khat] [Algebra A Ahat] [Algebra A Khat] [Algebra K Khat]
  [IsScalarTower A Ahat Khat] [IsScalarTower A K Khat]
  [IsFractionRing Ahat Khat] [IsDedekindDomain Ahat]


variable (𝔔 : Type*) [Fintype 𝔔] [DecidableEq 𝔔]


variable (Bhat : 𝔔 → Type*) (Lhat : 𝔔 → Type u)
variable [∀ 𝔮, CommRing (Bhat 𝔮)] [∀ 𝔮, IsDomain (Bhat 𝔮)] [∀ 𝔮, Field (Lhat 𝔮)]
variable [∀ 𝔮, Algebra (Bhat 𝔮) (Lhat 𝔮)] [∀ 𝔮, IsFractionRing (Bhat 𝔮) (Lhat 𝔮)]
variable [∀ 𝔮, Algebra Ahat (Bhat 𝔮)] [∀ 𝔮, Algebra Ahat (Lhat 𝔮)]
variable [∀ 𝔮, Algebra Khat (Lhat 𝔮)]
variable [∀ 𝔮, IsScalarTower Ahat Khat (Lhat 𝔮)]
variable [∀ 𝔮, IsScalarTower Ahat (Bhat 𝔮) (Lhat 𝔮)]
variable [∀ 𝔮, FiniteDimensional Khat (Lhat 𝔮)]


variable [∀ 𝔮, Algebra K (Lhat 𝔮)] [∀ 𝔮, Algebra L (Lhat 𝔮)]
variable [∀ 𝔮, IsScalarTower K L (Lhat 𝔮)] [∀ 𝔮, IsScalarTower K Khat (Lhat 𝔮)]



def discriminantBaseChange : Submodule Ahat Khat :=
  Submodule.span Ahat (algebraMap K Khat '' (extensionDiscriminant A K L B : Set K))







end DiscriminantCompletion

section DiscriminantNormDifferent


variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain A] [IsDedekindDomain B]

  [Module.Finite A B] [Module.IsTorsionFree A B]

theorem extensionDiscriminant_isIntegral :
    ∃ D : Ideal A, extensionDiscriminant A K L B = IsLocalization.coeSubmodule K D := by


  set S := latticeDiscrSet A K (imageOfB A L B) with hS_def

  have hS_range : S ⊆ Set.range (algebraMap A K) := by
    intro d ⟨b, hb, hd⟩
    subst hd
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    apply Algebra.discr_isIntegral K
    intro i
    have hi := hb i
    rw [mem_imageOfB] at hi
    obtain ⟨y, hy⟩ := hi
    rw [← hy]

    exact (IsIntegralClosure.isIntegral A L y).map (IsScalarTower.toAlgHom A B L)

  have hext : extensionDiscriminant A K L B = Submodule.span A S := rfl

  refine ⟨Ideal.span ((algebraMap A K) ⁻¹' S), ?_⟩
  rw [IsLocalization.coeSubmodule_span, hext]
  congr 1
  exact (Set.image_preimage_eq_of_subset hS_range).symm





theorem discr_ideal_ne_zero
    (D : Ideal A)
    (hD : extensionDiscriminant A K L B = IsLocalization.coeSubmodule K D) :
    (↑D : FractionalIdeal (nonZeroDivisors A) K) ≠ 0 := by
  rw [FractionalIdeal.coeIdeal_ne_zero]
  intro hD_bot
  rw [hD_bot, IsLocalization.coeSubmodule_bot] at hD


  classical

  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A K L B
  have hspan_range : Submodule.span K (Set.range (algebraMap B L)) = ⊤ := by
    rw [_root_.eq_top_iff]; intro x _
    obtain ⟨⟨b, s⟩, hbs⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) x
    obtain ⟨a, ha, has⟩ := s.prop
    have h1 : (algebraMap B L) (algebraMap A B a) = (algebraMap K L) (algebraMap A K a) := by
      rw [← IsScalarTower.algebraMap_apply A B L, ← IsScalarTower.algebraMap_apply A K L]
    have hkey : x * algebraMap K L (algebraMap A K a) = algebraMap B L b := by
      have h := hbs; dsimp at h; rw [← has] at h; rwa [h1] at h
    have ha_ne : algebraMap A K a ≠ 0 :=
      map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective A K) ha
    rw [show x = (algebraMap A K a)⁻¹ • algebraMap B L b from by
      have hne : (algebraMap K L) ((algebraMap A K) a) ≠ 0 := by
        rw [ne_eq, map_eq_zero]; exact ha_ne
      rw [Algebra.smul_def, map_inv₀, eq_comm, inv_mul_eq_div, div_eq_iff hne]
      exact hkey.symm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

  obtain ⟨t, ht_sub, ht_span, ht_li⟩ := exists_linearIndependent K (Set.range (algebraMap B L))
  rw [hspan_range] at ht_span
  haveI : Fintype t := ht_li.setFinite.fintype
  have hcard : Fintype.card t = Module.finrank K L := by
    apply le_antisymm
    · exact ht_li.fintype_card_le_finrank
    · exact finrank_le_of_span_eq_top (by rwa [Subtype.range_val])
  obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hcard
  set v := Subtype.val ∘ e.symm
  have hv_li : LinearIndependent K v := ht_li.comp e.symm e.symm.injective

  have hv_imageOfB : ∀ i, v i ∈ imageOfB A L B := by
    intro i
    rw [mem_imageOfB]
    exact ht_sub (e.symm i).prop

  have hmem : Algebra.discr K v ∈ extensionDiscriminant A K L B :=
    discr_mem_extensionDiscriminant A K L B hv_imageOfB

  haveI : Nonempty (Fin (Module.finrank K L)) := ⟨⟨0, Module.finrank_pos⟩⟩
  have hfin_card : Fintype.card (Fin (Module.finrank K L)) = Module.finrank K L :=
    Fintype.card_fin _
  have hdiscr_ne : Algebra.discr K v ≠ 0 := by
    have h := Algebra.discr_not_zero_of_basis K
      (basisOfLinearIndependentOfCardEqFinrank hv_li hfin_card)
    rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at h

  rw [hD] at hmem
  exact hdiscr_ne ((Submodule.mem_bot K).mp hmem)









end DiscriminantNormDifferent

section EtaleDiscriminant

open Module EtaleAlgebra

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable (K : Type*) {R : Type*} [Field K] [CommRing R] [Algebra K R]

theorem discr_ne_zero_iff_traceForm_nondegenerate (b : Basis ι K R) :
    Algebra.discr K b ≠ 0 ↔ (Algebra.traceForm K R).Nondegenerate := by
  rw [Algebra.discr_def, Algebra.traceMatrix_of_basis]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).symm

theorem discr_ne_zero_iff_isFiniteEtale (b : Basis ι K R)
    (thm_5_20 : IsFiniteEtaleAlgebra K R ↔ (Algebra.traceForm K R).Nondegenerate) :
    Algebra.discr K b ≠ 0 ↔ IsFiniteEtaleAlgebra K R := by
  rw [discr_ne_zero_iff_traceForm_nondegenerate K b, thm_5_20]

theorem discr_ne_zero_of_isFiniteEtale (b : Basis ι K R)
    (thm_5_20 : IsFiniteEtaleAlgebra K R ↔ (Algebra.traceForm K R).Nondegenerate)
    (hR : IsFiniteEtaleAlgebra K R) :
    Algebra.discr K b ≠ 0 :=
  (discr_ne_zero_iff_isFiniteEtale K b thm_5_20).mpr hR

theorem isFiniteEtale_of_discr_ne_zero (b : Basis ι K R)
    (thm_5_20 : IsFiniteEtaleAlgebra K R ↔ (Algebra.traceForm K R).Nondegenerate)
    (h : Algebra.discr K b ≠ 0) : IsFiniteEtaleAlgebra K R :=
  (discr_ne_zero_iff_isFiniteEtale K b thm_5_20).mp h

end EtaleDiscriminant

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

open IsDedekindDomain

theorem not_dvd_differentIdeal_iff_unramified
    {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (𝔮 : HeightOneSpectrum B) :
    ¬(𝔮.asIdeal ∣ differentIdeal A B) ↔ Algebra.IsUnramifiedAt A 𝔮.asIdeal :=
  not_dvd_differentIdeal_iff

theorem dvd_differentIdeal_iff_ramified
    {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (𝔮 : HeightOneSpectrum B) :
    (𝔮.asIdeal ∣ differentIdeal A B) ↔ ¬ Algebra.IsUnramifiedAt A 𝔮.asIdeal :=
  dvd_differentIdeal_iff

section RamificationDiscriminant


variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]



end RamificationDiscriminant

section OrderDiscriminant

def subalgebraConductor {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (𝒪 : Subalgebra A B) : Ideal B where
  carrier := {a | ∀ b : B, a * b ∈ 𝒪}
  zero_mem' b := by simp
  add_mem' ha hb c := by simpa [add_mul] using 𝒪.add_mem (ha c) (hb c)
  smul_mem' c a ha b := by simpa [mul_left_comm, mul_assoc] using ha (c * b)

theorem mem_subalgebraConductor_iff {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {𝒪 : Subalgebra A B} {a : B} :
    a ∈ subalgebraConductor 𝒪 ↔ ∀ b : B, a * b ∈ 𝒪 :=
  Iff.rfl

theorem subalgebraConductor_le {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (𝒪 : Subalgebra A B) :
    (subalgebraConductor 𝒪 : Set B) ⊆ (𝒪 : Set B) :=
  fun a ha => by simpa [mul_one] using ha 1

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.Finite A B] [Module.IsTorsionFree A B]

def imageOfSubalgebra (𝒪 : Subalgebra A B) : Submodule A L :=
  Submodule.map (IsScalarTower.toAlgHom A B L).toLinearMap 𝒪.toSubmodule

def orderDiscriminant (𝒪 : Subalgebra A B) : Submodule A K :=
  latticeDiscriminant A K (imageOfSubalgebra A L B 𝒪)


end OrderDiscriminant

end
