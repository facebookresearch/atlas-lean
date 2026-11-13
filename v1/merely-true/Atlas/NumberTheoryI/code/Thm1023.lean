/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.LocalExtensions
import Atlas.NumberTheoryI.code.ResidueFieldFunctor
import Atlas.NumberTheoryI.code.UnramBridge
import Mathlib.RingTheory.Invariant.Basic

noncomputable section

open Ideal Polynomial
open scoped Pointwise

section UnramifiedTotallyRamifiedDecomposition

variable
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
















theorem thm_10_23_part_iii_galois
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    [IsGalois K L] :
    IsGalois K (maximalUnramifiedSubextension A K L) := by
  rw [isGalois_iff]
  constructor
  · exact IntermediateField.isSeparable_tower_bot K (maximalUnramifiedSubextension A K L)
  · rw [IntermediateField.normal_iff_forall_map_eq']
    exact maximalUnramifiedSubextension_map_eq A K L

theorem thm_10_23_galLK_eq_decomp
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    [IsGalois K L]
    [MulSemiringAction (L ≃ₐ[K] L) B] :
    MulAction.stabilizer (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal B) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro σ
  rw [MulAction.mem_stabilizer_iff]
  have : (σ • IsLocalRing.maximalIdeal B).IsMaximal := by
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_equiv _
  exact IsLocalRing.eq_maximalIdeal this

theorem smul_algebraMap_eq_galois
    {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra B L] [IsFractionRing B L]
    [MulSemiringAction (L ≃ₐ[K] L) B]
    [SMulDistribClass (L ≃ₐ[K] L) B L]
    (σ : L ≃ₐ[K] L) (b : B) :
    algebraMap B L (σ • b) = σ (algebraMap B L b) :=
  algebraMap.smul' σ b L

theorem dvr_card_inertia_subgroupOf_eq
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    [IsGalois K L]
    [MulSemiringAction (L ≃ₐ[K] L) B]
    [SMulDistribClass (L ≃ₐ[K] L) B L]
    [SMulCommClass (L ≃ₐ[K] L) A B]
    [Algebra.IsInvariant A B (L ≃ₐ[K] L)]
    (E : IntermediateField K L)
    [FiniteDimensional K E]
    (hunram : Algebra.FormallyUnramified A (integralClosure A E)) :
    Nat.card
      (((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)).subgroupOf E.fixingSubgroup) =
    Nat.card ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)) := by
  suffices h : (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L) ≤ E.fixingSubgroup by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx

  set C := integralClosure A ↥E
  let ι_L : ↥C →ₐ[A] L := (E.val.restrictScalars A).comp C.val
  letI : Algebra ↥C L := ι_L.toAlgebra
  haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom ι_L
  haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
  let ι : ↥C →ₐ[A] B := IsIntegralClosure.lift A B L

  let σ_B := MulSemiringAction.toAlgHom A B σ

  have hKrull : ⨅ i, (IsLocalRing.maximalIdeal B) ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'
  have hext : σ_B.comp ι = ι := by
    apply Algebra.FormallyUnramified.ext_of_iInf (IsLocalRing.maximalIdeal B) hKrull
    intro y
    rw [Ideal.Quotient.eq]
    simp only [AlgHom.coe_comp, Function.comp_apply]
    exact hσ (ι y)

  have hfix_B : ∀ y : ↥C, σ • (ι y) = ι y := by
    intro y
    have := AlgHom.congr_fun hext y
    simp only [AlgHom.coe_comp, Function.comp_apply] at this
    exact this

  have hι_comm : ∀ y : ↥C, algebraMap B L (ι y) = ι_L y :=
    fun y => IsIntegralClosure.algebraMap_lift A B L y
  have hfix_L : ∀ y : ↥C, σ (ι_L y) = ι_L y := by
    intro y
    rw [← hι_comm, ← smul_algebraMap_eq_galois, hfix_B]

  haveI : IsFractionRing ↥C ↥E :=
    integralClosure.isFractionRing_of_finite_extension K ↥E
  set x' : ↥E := ⟨x, hx⟩
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors C) x'

  set aL := algebraMap ↥E L (algebraMap C ↥E a)
  set bL := algebraMap ↥E L (algebraMap C ↥E b)

  have haL : aL = ι_L a := rfl
  have hbL : bL = ι_L b := rfl
  have hab_L : x * bL = aL := by
    change (x' : L) * bL = aL
    have := congr_arg (algebraMap ↥E L) hab
    simp only [map_mul] at this
    convert this using 1
  have hσ_hab : σ x * bL = aL := by
    calc σ x * bL = σ x * σ bL := by rw [hbL, hfix_L b]
      _ = σ (x * bL) := by rw [map_mul]
      _ = σ aL := by rw [hab_L]
      _ = aL := by rw [haL, hfix_L a]
  have hb_ne : bL ≠ 0 := by
    intro h0
    have hbE_zero : algebraMap C ↥E b = 0 :=
      (FaithfulSMul.algebraMap_injective ↥E L) h0
    exact (nonZeroDivisors.coe_ne_zero ⟨b, hb⟩) ((IsFractionRing.injective C ↥E) hbE_zero)
  exact mul_right_cancel₀ hb_ne (hσ_hab.trans hab_L.symm)

theorem cor_7_14_inertia_le_fixingSubgroup_of_unramified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    [IsGalois K L]
    [MulSemiringAction (L ≃ₐ[K] L) B]
    [SMulDistribClass (L ≃ₐ[K] L) B L]
    [SMulCommClass (L ≃ₐ[K] L) A B]
    [Algebra.IsInvariant A B (L ≃ₐ[K] L)]

    (E : IntermediateField K L)
    (hfin : FiniteDimensional K E)
    (hunram : Algebra.FormallyUnramified A (integralClosure A E)) :
    (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L) ≤ E.fixingSubgroup := by
  haveI := hfin

  have hcard := dvr_card_inertia_subgroupOf_eq A K B L E hunram

  set H := (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)
  set K' := E.fixingSubgroup
  intro x hx
  let f : (H.subgroupOf K') → H := fun ⟨⟨g, _⟩, hg⟩ => ⟨g, Subgroup.mem_subgroupOf.mp hg⟩
  have hf_inj : Function.Injective f := by
    intro ⟨⟨g₁, _⟩, _⟩ ⟨⟨g₂, _⟩, _⟩ heq
    simp only [f, Subtype.mk.injEq] at heq
    exact Subtype.ext (Subtype.ext heq)
  have hf_bij := hf_inj.bijective_of_nat_card_le (hcard ▸ le_refl _)
  obtain ⟨⟨⟨g, hg_K⟩, hg_H⟩, hg_eq⟩ := hf_bij.2 ⟨x, hx⟩
  simp only [f, Subtype.mk.injEq] at hg_eq
  rw [← hg_eq]; exact hg_K






theorem formallyUnramified_le_fixedField_inertia
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    [IsGalois K L]
    [MulSemiringAction (L ≃ₐ[K] L) B]
    [SMulDistribClass (L ≃ₐ[K] L) B L]

    [SMulCommClass (L ≃ₐ[K] L) A B]
    [Algebra.IsInvariant A B (L ≃ₐ[K] L)]

    (E : IntermediateField K L)
    (hE : IsFiniteUnramifiedSubext A K L E) :
    E ≤ IntermediateField.fixedField ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)) := by

  obtain ⟨hfin, hunram⟩ := hE

  have hle := cor_7_14_inertia_le_fixingSubgroup_of_unramified A K B L E hfin hunram

  exact (IntermediateField.le_iff_le
    ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)) E).mpr hle






end UnramifiedTotallyRamifiedDecomposition

end
