/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Frobenius
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Galois.Basic

open Ideal
open scoped Pointwise

abbrev IsLeftGModule (G : Type*) (M : Type*) [Group G] [AddCommGroup M]
    [DistribMulAction G M] : Prop := True

theorem left_gmodule_smul_add (G M : Type*) [Group G] [AddCommGroup M]
    [DistribMulAction G M] (σ : G) (a b : M) : σ • (a + b) = σ • a + σ • b :=
  smul_add σ a b

section GaloisActionOnIdeals

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

theorem galois_action_fractional_ideal (σ : G) (I : Ideal B) (x : B) :
    x ∈ σ • I ↔ σ⁻¹ • x ∈ I :=
  Ideal.mem_pointwise_smul_iff_inv_smul_mem

theorem galois_action_mul_compat (σ : G) (I J : Ideal B) :
    σ • (I * J) = σ • I * σ • J :=
  MulSemiringAction.smul_mul σ I J

@[reducible]
def galois_gmodule_fractional_ideals :
    MulSemiringAction G (Ideal B) :=
  inferInstance

theorem galois_action_preserves_prime (σ : G) (I : Ideal B) [I.IsPrime] :
    (σ • I).IsPrime :=
  IsPrime.smul σ

theorem galois_smul_ideal_mem_iff (σ : G) (I : Ideal B) (x : B) :
    x ∈ σ • I ↔ σ⁻¹ • x ∈ I :=
  Ideal.mem_pointwise_smul_iff_inv_smul_mem

@[deprecated galois_smul_ideal_mem_iff (since := "2025-05-04")]
theorem theorem_7_2_sigma_preserves_fractional_ideal (σ : G) (I : Ideal B) (x : B) :
    x ∈ σ • I ↔ σ⁻¹ • x ∈ I :=
  galois_smul_ideal_mem_iff G σ I x

theorem galois_smul_ideal_mul (σ : G) (I J : Ideal B) :
    σ • (I * J) = σ • I * σ • J :=
  MulSemiringAction.smul_mul σ I J

@[deprecated galois_smul_ideal_mul (since := "2025-05-04")]
theorem theorem_7_2_gmodule_structure (σ : G) (I J : Ideal B) :
    σ • (I * J) = σ • I * σ • J :=
  galois_smul_ideal_mul G σ I J

theorem galois_smul_isPrime (σ : G) (I : Ideal B) [I.IsPrime] :
    (σ • I).IsPrime :=
  IsPrime.smul σ

@[deprecated galois_smul_isPrime (since := "2025-05-04")]
theorem theorem_7_2_gset_on_primes (σ : G) (I : Ideal B) [I.IsPrime] :
    (σ • I).IsPrime :=
  galois_smul_isPrime G σ I

theorem galois_smul_ideal_add (σ : G) (I J : Ideal B) :
    σ • (I + J) = σ • I + σ • J :=
  DistribMulAction.smul_add σ I J

@[deprecated galois_smul_ideal_add (since := "2025-05-04")]
theorem theorem_7_2_gmodule_add_compat (σ : G) (I J : Ideal B) :
    σ • (I + J) = σ • I + σ • J :=
  galois_smul_ideal_add G σ I J

end GaloisActionOnIdeals

section GaloisActionTransitivity

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {p : Ideal A}
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

theorem galois_action_on_ideals_isPretransitive :
    MulAction.IsPretransitive G (primesOver p B) :=
  isPretransitive_of_isGaloisGroup p G

end GaloisActionTransitivity

section TransitiveActionOnPrimes

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (p : Ideal A)
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

theorem galois_transitive_on_primes_above
    (P Q : Ideal B) [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] :
    ∃ σ : G, σ • P = Q :=
  exists_smul_eq_of_isGaloisGroup p P Q G

end TransitiveActionOnPrimes

section ConstantRamificationInertia

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (p : Ideal A)
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

include G in
theorem ramificationIdx_constant_of_isGaloisGroup
    (P Q : Ideal B) [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] :
    p.ramificationIdx P = p.ramificationIdx Q :=
  ramificationIdx_eq_of_isGaloisGroup p P Q G

include G in
theorem inertiaDeg_constant_of_isGaloisGroup
    (P Q : Ideal B) [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] :
    p.inertiaDeg P = p.inertiaDeg Q :=
  inertiaDeg_eq_of_isGaloisGroup p P Q G

end ConstantRamificationInertia

section EFGFormula

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {p : Ideal A} [p.IsMaximal]
  (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

theorem efg_eq_degree (hp : p ≠ ⊥) :
    (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Nat.card G :=
  ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G

end EFGFormula

section DecompositionGroupDef

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [MulSemiringAction G B]

abbrev decompositionGroup (Q : Ideal B) : Subgroup G :=
  MulAction.stabilizer G Q

theorem mem_decompositionGroup_iff (Q : Ideal B) (σ : G) :
    σ ∈ decompositionGroup G Q ↔ σ • Q = Q :=
  MulAction.mem_stabilizer_iff

end DecompositionGroupDef

section DecompositionGroupProperties

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {p : Ideal A}
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

omit [Finite G] in
theorem decompositionGroup_conjugate
    (P : Ideal B) (σ : G) :
    decompositionGroup G (σ • P) =
      (decompositionGroup G P).map (MulAut.conj σ).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj σ P

theorem card_decompositionGroup_eq_ef
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.IsTorsionFree A B]
    (hp : p ≠ ⊥) (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    Nat.card (decompositionGroup G P) = ramificationIdxIn p B * inertiaDegIn p B :=
  Ideal.card_stabilizer_eq p hp P

theorem index_decompositionGroup_eq_g
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [p.IsMaximal]
    (hp : p ≠ ⊥) (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    (decompositionGroup G P).index = (primesOver p B).ncard := by
  have hef : Nat.card (MulAction.stabilizer G P) = ramificationIdxIn p B * inertiaDegIn p B :=
    Ideal.card_stabilizer_eq p hp P
  have hefg : (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Nat.card G :=
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G
  have hcard : Nat.card (MulAction.stabilizer G P) * (MulAction.stabilizer G P).index = Nat.card G :=
    Subgroup.card_mul_index _
  rw [hef] at hcard
  have hef_pos : 0 < ramificationIdxIn p B * inertiaDegIn p B := by
    rw [← hef]; exact Nat.card_pos (α := ↥(MulAction.stabilizer G P))
  exact Nat.eq_of_mul_eq_mul_right hef_pos (by linarith)

end DecompositionGroupProperties

section ResidueFieldSurjection

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {p : Ideal A}
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G]

noncomputable def residueField_surjection
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    MulAction.stabilizer G Q ⧸ (Q.inertia G).subgroupOf (MulAction.stabilizer G Q) ≃*
      ((B ⧸ Q) ≃ₐ[A ⧸ p] (B ⧸ Q)) :=
  Ideal.Quotient.stabilizerQuotientInertiaEquiv G p Q

attribute [local instance] Ideal.Quotient.field

omit [SMulCommClass G A B] in
include G in
theorem residueField_normal
    (Q : Ideal B) [Q.LiesOver p] [p.IsMaximal] [Q.IsMaximal] :
    Normal (A ⧸ p) (B ⧸ Q) :=
  Ideal.Quotient.normal G p Q

end ResidueFieldSurjection

section InertiaGroupDef

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

abbrev inertiaGroup (Q : Ideal B) : Subgroup G :=
  Q.inertia G

theorem inertiaGroup_le_decompositionGroup (Q : Ideal B) :
    inertiaGroup G Q ≤ decompositionGroup G Q :=
  Ideal.inertia_le_stabilizer Q

end InertiaGroupDef

section InertiaDecompositionExactSequence

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {p : Ideal A}
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

attribute [local instance] Ideal.Quotient.field

noncomputable def decompositionQuotientInertiaEquiv
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    MulAction.stabilizer G Q ⧸ (Q.inertia G).subgroupOf (MulAction.stabilizer G Q) ≃*
      ((B ⧸ Q) ≃ₐ[A ⧸ p] (B ⧸ Q)) :=
  Ideal.Quotient.stabilizerQuotientInertiaEquiv G p Q

@[deprecated decompositionQuotientInertiaEquiv (since := "2025-05-04")]
noncomputable def exact_sequence_inertia_decomposition
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    MulAction.stabilizer G Q ⧸ (Q.inertia G).subgroupOf (MulAction.stabilizer G Q) ≃*
      ((B ⧸ Q) ≃ₐ[A ⧸ p] (B ⧸ Q)) :=
  decompositionQuotientInertiaEquiv G Q

theorem card_inertiaGroup_eq_e_mul_insepDegree
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [p.IsMaximal]
    (hp : p ≠ ⊥) (P : Ideal B) [P.LiesOver p] [P.IsMaximal] :
    Nat.card (inertiaGroup G P) =
      ramificationIdxIn p B * Field.finInsepDegree (A ⧸ p) (B ⧸ P) := by

  have h_exact := Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P
  have h_index : ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).index =
      Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) :=
    Nat.card_congr h_exact.toEquiv
  have h_lagrange := ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).card_mul_index
  rw [h_index, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv] at h_lagrange

  haveI : Normal (A ⧸ p) (B ⧸ P) := Ideal.Quotient.normal G p P
  have h_aut_sep : Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) =
      Field.finSepDegree (A ⧸ p) (B ⧸ P) :=
    Nat.card_congr (Normal.algHomEquivAut (A ⧸ p) (AlgebraicClosure (B ⧸ P)) (B ⧸ P)).symm
  rw [h_aut_sep] at h_lagrange

  have h_gef := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G
  have h_orbit := Algebra.IsInvariant.orbit_eq_primesOver A B G p P
  have h_gD : (primesOver p B).ncard * Nat.card (MulAction.stabilizer G P) = Nat.card G := by
    rw [← h_orbit]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hg_pos : 0 < (primesOver p B).ncard := by
    by_contra hg; simp only [not_lt, Nat.le_zero] at hg
    rw [hg, zero_mul] at h_gef; linarith [Nat.card_pos (α := G)]
  have h_D_eq : Nat.card (MulAction.stabilizer G P) =
      ramificationIdxIn p B * inertiaDegIn p B :=
    Nat.eq_of_mul_eq_mul_left hg_pos (h_gD.trans h_gef.symm)

  rw [h_D_eq, inertiaDegIn_eq_inertiaDeg p P G, inertiaDeg_algebraMap,
    ← Field.finSepDegree_mul_finInsepDegree (A ⧸ p) (B ⧸ P)] at h_lagrange


  have h_rw : ramificationIdxIn p B * (Field.finSepDegree (A ⧸ p) (B ⧸ P) *
      Field.finInsepDegree (A ⧸ p) (B ⧸ P)) =
    (ramificationIdxIn p B * Field.finInsepDegree (A ⧸ p) (B ⧸ P)) *
      Field.finSepDegree (A ⧸ p) (B ⧸ P) := by ring
  rw [h_rw] at h_lagrange
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne _)) h_lagrange

theorem card_inertiaGroup_eq_e
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.IsTorsionFree A B]
    (hp : p ≠ ⊥) (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    Nat.card (inertiaGroup G P) = ramificationIdxIn p B :=
  Ideal.card_inertia_eq_ramificationIdxIn p hp P

end InertiaDecompositionExactSequence

section FieldTower

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing A] [CommRing B] [Algebra A B] {p : Ideal A}
  (P : Ideal B) [P.LiesOver p]
  [FiniteDimensional K L] [MulSemiringAction (L ≃ₐ[K] L) B]
  [IsGaloisGroup (L ≃ₐ[K] L) A B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Ring.HasFiniteQuotients A] [P.IsMaximal]

theorem finrank_over_inertiaField_eq_ramificationIdx
    (E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E]
    (hp : p ≠ ⊥) :
    Module.finrank E L = ramificationIdxIn p B :=
  IsInertiaField.rank_left A K L P E hp

theorem finrank_inertiaField_over_decompositionField_eq_inertiaDeg
    (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]
    (E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E]
    [IsGalois K L] [Algebra K D] [Algebra K E] [Algebra D E]
    [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower K D L]
    (hp : p ≠ ⊥) :
    Module.finrank D E = inertiaDegIn p B :=
  IsInertiaField.rank_decompositionField A K L P D E hp

theorem finrank_decompositionField_eq_ncard_primesOver
    (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]
    [IsGalois K L] [Algebra K D] [IsScalarTower K D L]
    (hp : p ≠ ⊥) :
    Module.finrank K D = (primesOver p B).ncard :=
  IsDecompositionField.rank_right A K L P D hp

theorem finrank_over_decompositionField_eq_ef
    (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]
    (hp : p ≠ ⊥) :
    Module.finrank D L = ramificationIdxIn p B * inertiaDegIn p B :=
  IsDecompositionField.rank_left A K L P D hp

end FieldTower

section IntermediateExtensionGroups

variable {B : Type*} [Ring B]
  (G : Type*) [Group G] [MulSemiringAction G B]

theorem stabilizer_subgroupOf_and_inertia_subgroupOf (Q : Ideal B) (H : Subgroup G) :
    (MulAction.stabilizer G Q).subgroupOf H = MulAction.stabilizer H Q ∧
    (Q.inertia G).subgroupOf H = Q.inertia H :=
  ⟨by ext ⟨h, hH⟩; simp [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf],
   AddSubgroup.subgroupOf_inertia Q.toAddSubgroup H⟩

theorem decompositionGroup_subgroupOf (Q : Ideal B)
    (H : Subgroup G) :
    (MulAction.stabilizer G Q).subgroupOf H =
      MulAction.stabilizer H Q :=
  (stabilizer_subgroupOf_and_inertia_subgroupOf G Q H).1

theorem inertiaGroup_subgroupOf (Q : Ideal B)
    (H : Subgroup G) :
    (Q.inertia G).subgroupOf H = Q.inertia H :=
  (stabilizer_subgroupOf_and_inertia_subgroupOf G Q H).2

end IntermediateExtensionGroups

section UnramifiedSplitCharacterization

variable (K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing B] [Algebra B L] [MulSemiringAction (L ≃ₐ[K] L) B]

omit [Algebra B L] in
theorem inertiaField_is_fixedField_of_inertiaGroup
    (P : Ideal B)
    [IsGalois K L] :
    IsInertiaField K L P
      (FixedPoints.intermediateField (P.inertia (L ≃ₐ[K] L)) : IntermediateField K L) :=
  inferInstance

omit [Algebra B L] in
theorem decompositionField_is_fixedField_of_decompositionGroup
    (P : Ideal B)
    [IsGalois K L] :
    IsDecompositionField K L P
      (FixedPoints.intermediateField (MulAction.stabilizer (L ≃ₐ[K] L) P) :
        IntermediateField K L) :=
  inferInstance

lemma Subgroup.le_of_card_subgroupOf_eq' {G : Type*} [Group G] {H K : Subgroup G}
    [Finite H]
    (h : Nat.card (H.subgroupOf K) = Nat.card H) :
    H ≤ K := by
  intro x hx
  let f : (H.subgroupOf K) → H := fun ⟨⟨g, _⟩, hg⟩ => ⟨g, Subgroup.mem_subgroupOf.mp hg⟩
  have hf_inj : Function.Injective f := by
    intro ⟨⟨g₁, _⟩, _⟩ ⟨⟨g₂, _⟩, _⟩ heq
    simp only [f, Subtype.mk.injEq] at heq
    exact Subtype.ext (Subtype.ext heq)
  have hf_bij := hf_inj.bijective_of_nat_card_le (h ▸ le_refl _)
  obtain ⟨⟨⟨g, hg_K⟩, hg_H⟩, hg_eq⟩ := hf_bij.2 ⟨x, hx⟩
  simp only [f, Subtype.mk.injEq] at hg_eq
  rw [← hg_eq]; exact hg_K

theorem card_inertia_tower_formula
    {K L : Type*} {B : Type*} [Field K] [Field L] [Algebra K L]
    [CommRing B] [MulSemiringAction (L ≃ₐ[K] L) B]
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]

    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (hp : p ≠ ⊥) (hP_E : P_E ≠ ⊥) :
    Ideal.ramificationIdx p P_E *
      Nat.card (P.inertia (↥E.fixingSubgroup)) =
    Nat.card (P.inertia (L ≃ₐ[K] L)) := by

  have h_full := Ideal.card_inertia_eq_ramificationIdxIn (G := (L ≃ₐ[K] L)) p hp P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P (L ≃ₐ[K] L)] at h_full

  have h_sub := Ideal.card_inertia_eq_ramificationIdxIn (G := ↥E.fixingSubgroup) P_E hP_E P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P_E P ↥E.fixingSubgroup] at h_sub

  have h_tower := Ideal.ramificationIdx_algebra_tower' p P_E P

  rw [h_full, h_sub, h_tower]

theorem ramificationIdx_mul_card_inertia_subgroupOf
    {K L : Type*} {B : Type*} [Field K] [Field L] [Algebra K L]
    [CommRing B] [MulSemiringAction (L ≃ₐ[K] L) B]
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]

    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (hp : p ≠ ⊥) (hP_E : P_E ≠ ⊥) :
    Ideal.ramificationIdx p P_E *
      Nat.card ((P.inertia (L ≃ₐ[K] L)).subgroupOf E.fixingSubgroup) =
    Nat.card (P.inertia (L ≃ₐ[K] L)) := by

  rw [show (P.inertia (L ≃ₐ[K] L)).subgroupOf E.fixingSubgroup =
    P.inertia E.fixingSubgroup from
    AddSubgroup.subgroupOf_inertia P.toAddSubgroup E.fixingSubgroup]

  exact card_inertia_tower_formula P p E C_E P_E hp hP_E

omit [Algebra B L] in

theorem ramificationIdx_eq_one_iff_inertia_le_fixingSubgroup
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]

    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (hp : p ≠ ⊥) (hP_E : P_E ≠ ⊥) :
    Ideal.ramificationIdx p P_E = 1 ↔
      P.inertia (L ≃ₐ[K] L) ≤ E.fixingSubgroup := by
  have htower := ramificationIdx_mul_card_inertia_subgroupOf P p E C_E P_E hp hP_E
  constructor
  ·
    intro he
    rw [he, one_mul] at htower
    exact Subgroup.le_of_card_subgroupOf_eq' htower
  ·
    intro hle
    have hcard_eq : Nat.card ((P.inertia (L ≃ₐ[K] L)).subgroupOf E.fixingSubgroup) =
        Nat.card (P.inertia (L ≃ₐ[K] L)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hcard_eq] at htower
    exact mul_right_cancel₀ (Nat.pos_iff_ne_zero.mp Nat.card_pos)
      (htower.trans (one_mul _).symm)

omit [Algebra B L] in
theorem e_eq_one_iff_le_inertiaField
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]

    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (hp : p ≠ ⊥) (hP_E : P_E ≠ ⊥) :
    Ideal.ramificationIdx p P_E = 1 ↔
      E ≤ IntermediateField.fixedField (P.inertia (L ≃ₐ[K] L)) := by
  rw [ramificationIdx_eq_one_iff_inertia_le_fixingSubgroup K L P p E C_E P_E hp hP_E]
  exact (IntermediateField.le_iff_le (P.inertia (L ≃ₐ[K] L)) E).symm

omit [Algebra B L] in
set_option maxHeartbeats 400000 in
theorem ef_mul_card_stabilizer_subgroupOf
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]

    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (hp : p ≠ ⊥) (hP_E : P_E ≠ ⊥) :
    (Ideal.ramificationIdx p P_E * Ideal.inertiaDeg p P_E) *
      Nat.card ((@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
        Ideal.pointwiseMulSemiringAction.toMulAction P).subgroupOf E.fixingSubgroup) =
    Nat.card (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
        Ideal.pointwiseMulSemiringAction.toMulAction P) := by

  rw [show (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
      Ideal.pointwiseMulSemiringAction.toMulAction P).subgroupOf E.fixingSubgroup =
      @MulAction.stabilizer (↥E.fixingSubgroup) (Ideal B) _
        Ideal.pointwiseMulSemiringAction.toMulAction P from by
    ext ⟨h, hH⟩
    simp only [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    rfl]

  have h_full := Ideal.card_stabilizer_eq (G := (L ≃ₐ[K] L)) p hp P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P (L ≃ₐ[K] L),
      Ideal.inertiaDegIn_eq_inertiaDeg p P (L ≃ₐ[K] L)] at h_full

  have h_sub := Ideal.card_stabilizer_eq (G := ↥E.fixingSubgroup) P_E hP_E P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P_E P ↥E.fixingSubgroup,
      Ideal.inertiaDegIn_eq_inertiaDeg P_E P ↥E.fixingSubgroup] at h_sub

  have h_e_tower := Ideal.ramificationIdx_algebra_tower' p P_E P
  have h_f_tower := Ideal.inertiaDeg_algebra_tower p P_E P

  rw [h_full, h_sub, h_e_tower, h_f_tower]
  ring

omit [Algebra B L] in
theorem ef_eq_one_iff_stabilizer_le_fixingSubgroup
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]

    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (hp : p ≠ ⊥) (hP_E : P_E ≠ ⊥) :
    (Ideal.ramificationIdx p P_E = 1 ∧ Ideal.inertiaDeg p P_E = 1) ↔
      (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
        Ideal.pointwiseMulSemiringAction.toMulAction P) ≤ E.fixingSubgroup := by
  have htower := ef_mul_card_stabilizer_subgroupOf K L P p E C_E P_E hp hP_E
  constructor
  ·
    intro ⟨he, hf⟩
    rw [he, hf, mul_one, one_mul] at htower
    exact Subgroup.le_of_card_subgroupOf_eq' htower
  ·
    intro hle
    have hcard_eq : Nat.card ((@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
          Ideal.pointwiseMulSemiringAction.toMulAction P).subgroupOf E.fixingSubgroup) =
        Nat.card (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
          Ideal.pointwiseMulSemiringAction.toMulAction P) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hcard_eq] at htower
    have hef : Ideal.ramificationIdx p P_E * Ideal.inertiaDeg p P_E = 1 :=
      mul_right_cancel₀ (Nat.pos_iff_ne_zero.mp Nat.card_pos)
        (htower.trans (one_mul _).symm)
    exact mul_eq_one.mp hef

omit [Algebra B L] in
theorem ef_eq_one_iff_le_decompositionField
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]

    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (hp : p ≠ ⊥) (hP_E : P_E ≠ ⊥) :
    (Ideal.ramificationIdx p P_E = 1 ∧ Ideal.inertiaDeg p P_E = 1) ↔
      E ≤ IntermediateField.fixedField
        (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
          Ideal.pointwiseMulSemiringAction.toMulAction P) := by
  rw [IntermediateField.le_iff_le]
  exact ef_eq_one_iff_stabilizer_le_fixingSubgroup K L P p E C_E P_E hp hP_E

omit [Algebra B L] in
theorem e_ef_eq_one_iff_le_inertiaField_decompositionField
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [Algebra.IsSeparable (C_E ⧸ P_E) (B ⧸ P)]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (hp : p ≠ ⊥) (hP_E : P_E ≠ ⊥) :
    (Ideal.ramificationIdx p P_E = 1 ↔
      E ≤ IntermediateField.fixedField (P.inertia (L ≃ₐ[K] L))) ∧
    ((Ideal.ramificationIdx p P_E = 1 ∧ Ideal.inertiaDeg p P_E = 1) ↔
      E ≤ IntermediateField.fixedField
        (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
          Ideal.pointwiseMulSemiringAction.toMulAction P)) :=
  ⟨e_eq_one_iff_le_inertiaField K L P p E C_E P_E hp hP_E,
   ef_eq_one_iff_le_decompositionField K L P p E C_E P_E hp hP_E⟩

end UnramifiedSplitCharacterization

section InertiaDecompositionNormality

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]

omit [Finite G] in
theorem inertiaGroup_normal_in_decompositionGroup [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] (Q : Ideal B) [Q.IsPrime] :
    ((Q.inertia G).subgroupOf (MulAction.stabilizer G Q)).Normal :=
  inferInstance

end InertiaDecompositionNormality

section GaloisInertiaDecompositionFields

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [IsGalois K L] [FiniteDimensional K L]

omit [FiniteDimensional K L] in
theorem isGalois_inertiaField_normalClosure
    {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B L]
    [MulSemiringAction (L ≃ₐ[K] L) B]
    (P : Ideal B) :
    IsGalois K (IntermediateField.fixedField
      (Subgroup.normalClosure (↑(P.inertia (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)))) := by
  haveI : (Subgroup.normalClosure (↑(P.inertia (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L))).Normal :=
    Subgroup.normalClosure_normal
  exact IsGalois.of_fixedField_normal_subgroup _

omit [FiniteDimensional K L] in
theorem isGalois_decompositionField_normalClosure
    {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B L]
    [MulSemiringAction (L ≃ₐ[K] L) B]
    (P : Ideal B) :
    IsGalois K (IntermediateField.fixedField
      (Subgroup.normalClosure
        (↑(MulAction.stabilizer (L ≃ₐ[K] L) P) : Set (L ≃ₐ[K] L)))) := by
  haveI : (Subgroup.normalClosure
    (↑(MulAction.stabilizer (L ≃ₐ[K] L) P) : Set (L ≃ₐ[K] L))).Normal :=
    Subgroup.normalClosure_normal
  exact IsGalois.of_fixedField_normal_subgroup _

lemma normalClosure_le_iff_forall_conj {G : Type*} [Group G] (H N : Subgroup G) :
    Subgroup.normalClosure (↑H : Set G) ≤ N ↔
      ∀ g : G, H.map (MulAut.conj g).toMonoidHom ≤ N := by
  simp only [Subgroup.normalClosure, Subgroup.closure_le]
  constructor
  · intro hle g x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨h, hh, rfl⟩ := hx
    apply hle
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨h, hh, isConj_iff.mpr ⟨g, rfl⟩⟩
  · intro hall x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hconj⟩ := hx
    rw [isConj_iff] at hconj
    obtain ⟨g, rfl⟩ := hconj
    exact hall g (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)

lemma normalClosure_stabilizer_le_iff {G : Type*} [Group G] {α : Type*} [MulAction G α]
    (a : α) (N : Subgroup G) :
    Subgroup.normalClosure (↑(MulAction.stabilizer G a) : Set G) ≤ N ↔
      ∀ g : G, MulAction.stabilizer G (g • a) ≤ N := by
  rw [normalClosure_le_iff_forall_conj]
  simp_rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]

open Pointwise in
lemma Ideal.IsMaximal.smul {G : Type*} [Group G] {B : Type*} [CommRing B]
    [MulSemiringAction G B] {P : Ideal B} (hP : P.IsMaximal) (g : G) : (g • P).IsMaximal := by
  rw [Ideal.pointwise_smul_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ (MulSemiringAction.toRingAut G B g).symm.surjective

open Pointwise in
lemma inertia_smul_eq_inertia_map_conj
    {G B : Type*} [Group G] [CommRing B] [MulSemiringAction G B]
    (P : Ideal B) (σ : G) :
    (σ • P).inertia G = (P.inertia G).map (MulAut.conj σ).toMonoidHom := by
  ext g
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hg
    refine ⟨σ⁻¹ * g * σ, ?_, by group⟩
    intro x
    have h1 := hg (σ • x)
    have key : g • (σ • x) - σ • x = σ • ((σ⁻¹ * g * σ) • x - x) := by
      simp [mul_smul, smul_sub]
    rw [key] at h1
    change σ • _ ∈ (σ • P : Ideal B) at h1
    rwa [Ideal.smul_mem_pointwise_smul_iff] at h1
  · rintro ⟨h, hh, rfl⟩
    intro x
    have h1 := hh (σ⁻¹ • x)
    have key : (σ * h * σ⁻¹) • x - x = σ • (h • (σ⁻¹ • x) - σ⁻¹ • x) := by
      simp [mul_smul, smul_sub]
    rw [key]
    change σ • _ ∈ (σ • P : Ideal B)
    rwa [Ideal.smul_mem_pointwise_smul_iff]

open Pointwise in
lemma normalClosure_inertia_le_iff
    {G B : Type*} [Group G] [CommRing B] [MulSemiringAction G B]
    (P : Ideal B) (N : Subgroup G) :
    Subgroup.normalClosure (↑(P.inertia G) : Set G) ≤ N ↔
      ∀ σ : G, (σ • P).inertia G ≤ N := by
  rw [normalClosure_le_iff_forall_conj]
  simp_rw [inertia_smul_eq_inertia_map_conj]

theorem unramified_all_primes_iff_le_inertiaField_normalClosure
    {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B L]
    [MulSemiringAction (L ≃ₐ[K] L) B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    [Algebra.IsIntegral A B] [SMulCommClass (L ≃ₐ[K] L) A B]
    (P : Ideal B) [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal] [P.LiesOver p]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E]
    [Algebra A C_E] [Algebra C_E B] [IsScalarTower A C_E B]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]

    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (hp : p ≠ ⊥)

    (h_sep_A : ∀ (P' : Ideal B) [P'.IsMaximal] [P'.LiesOver p],
        Algebra.IsSeparable (A ⧸ p) (B ⧸ P'))
    (h_sep_C : ∀ (Q' : Ideal C_E) (P' : Ideal B) [Q'.IsMaximal] [P'.IsMaximal]
        [Q'.LiesOver p] [P'.LiesOver Q'],
        Algebra.IsSeparable (C_E ⧸ Q') (B ⧸ P'))

    (h_exists_smul : ∀ (Q' : Ideal C_E) [Q'.IsMaximal] [Q'.LiesOver p],
        ∃ σ : L ≃ₐ[K] L, (σ • P).LiesOver Q')

    (hQ_ne_bot : ∀ (Q' : Ideal C_E) [Q'.IsMaximal] [Q'.LiesOver p], Q' ≠ ⊥) :
    (∀ (Q : Ideal C_E) [Q.IsMaximal] [Q.LiesOver p],
      Ideal.ramificationIdx p Q = 1) ↔

      E ≤ IntermediateField.fixedField
        (Subgroup.normalClosure (↑(P.inertia (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L))) := by
  rw [IntermediateField.le_iff_le]
  rw [normalClosure_inertia_le_iff]
  constructor
  ·
    intro hall σ
    haveI : (σ • P).IsMaximal := Ideal.IsMaximal.smul ‹P.IsMaximal› σ
    haveI : (σ • P).LiesOver p := Ideal.LiesOver.smul σ
    haveI : Algebra.IsIntegral C_E B := Algebra.IsIntegral.tower_top (R := A)
    set Q_σ := Ideal.comap (algebraMap C_E B) (σ • P)
    haveI : Q_σ.IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (σ • P)
    haveI : Q_σ.LiesOver p := Ideal.under_liesOver_of_liesOver C_E (σ • P) p
    haveI : (σ • P).LiesOver Q_σ := ⟨rfl⟩
    haveI : Algebra.IsSeparable (A ⧸ p) (B ⧸ (σ • P)) := h_sep_A (σ • P)
    haveI : Algebra.IsSeparable (C_E ⧸ Q_σ) (B ⧸ (σ • P)) := h_sep_C Q_σ (σ • P)
    have hQ_ne := hQ_ne_bot Q_σ
    have hQ := hall Q_σ
    rw [e_eq_one_iff_le_inertiaField K L (σ • P) p E C_E Q_σ hp hQ_ne] at hQ
    exact (IntermediateField.le_iff_le ((σ • P).inertia (L ≃ₐ[K] L)) E).mp hQ
  ·
    intro hall Q _ _

    obtain ⟨σ, hσ_over⟩ := h_exists_smul Q
    haveI : (σ • P).IsMaximal := Ideal.IsMaximal.smul ‹P.IsMaximal› σ
    haveI : (σ • P).LiesOver p := Ideal.LiesOver.smul σ
    haveI : (σ • P).LiesOver Q := hσ_over
    haveI : Algebra.IsSeparable (A ⧸ p) (B ⧸ (σ • P)) := h_sep_A (σ • P)
    haveI : Algebra.IsSeparable (C_E ⧸ Q) (B ⧸ (σ • P)) := h_sep_C Q (σ • P)
    have hQ_ne := hQ_ne_bot Q

    rw [e_eq_one_iff_le_inertiaField K L (σ • P) p E C_E Q hp hQ_ne]

    apply (IntermediateField.le_iff_le ((σ • P).inertia (L ≃ₐ[K] L)) E).mpr

    exact hall σ

theorem splitsCompletely_all_primes_iff_le_decompositionField_normalClosure
    {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B L]
    [MulSemiringAction (L ≃ₐ[K] L) B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    [Algebra.IsIntegral A B] [SMulCommClass (L ≃ₐ[K] L) A B]
    (P : Ideal B) [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal] [P.LiesOver p]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E]
    [Algebra A C_E] [Algebra C_E B] [IsScalarTower A C_E B]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]

    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (hp : p ≠ ⊥)

    (h_sep_A : ∀ (P' : Ideal B) [P'.IsMaximal] [P'.LiesOver p],
        Algebra.IsSeparable (A ⧸ p) (B ⧸ P'))
    (h_sep_C : ∀ (Q' : Ideal C_E) (P' : Ideal B) [Q'.IsMaximal] [P'.IsMaximal]
        [Q'.LiesOver p] [P'.LiesOver Q'],
        Algebra.IsSeparable (C_E ⧸ Q') (B ⧸ P'))

    (h_exists_smul : ∀ (Q' : Ideal C_E) [Q'.IsMaximal] [Q'.LiesOver p],
        ∃ σ : L ≃ₐ[K] L, (σ • P).LiesOver Q')

    (hQ_ne_bot : ∀ (Q' : Ideal C_E) [Q'.IsMaximal] [Q'.LiesOver p], Q' ≠ ⊥) :
    (∀ (Q : Ideal C_E) [Q.IsMaximal] [Q.LiesOver p],
      Ideal.ramificationIdx p Q = 1 ∧ Ideal.inertiaDeg p Q = 1) ↔
      E ≤ IntermediateField.fixedField
        (Subgroup.normalClosure
          (↑(MulAction.stabilizer (L ≃ₐ[K] L) P) : Set (L ≃ₐ[K] L))) := by
  rw [IntermediateField.le_iff_le]
  rw [normalClosure_stabilizer_le_iff]
  constructor
  ·
    intro hall σ
    haveI : (σ • P).IsMaximal := Ideal.IsMaximal.smul ‹P.IsMaximal› σ
    haveI : (σ • P).LiesOver p := Ideal.LiesOver.smul σ
    haveI : Algebra.IsIntegral C_E B := Algebra.IsIntegral.tower_top (R := A)
    set Q_σ := Ideal.comap (algebraMap C_E B) (σ • P)
    haveI : Q_σ.IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (σ • P)
    haveI : Q_σ.LiesOver p := Ideal.under_liesOver_of_liesOver C_E (σ • P) p
    haveI : (σ • P).LiesOver Q_σ := ⟨rfl⟩
    haveI : Algebra.IsSeparable (A ⧸ p) (B ⧸ (σ • P)) := h_sep_A (σ • P)
    haveI : Algebra.IsSeparable (C_E ⧸ Q_σ) (B ⧸ (σ • P)) := h_sep_C Q_σ (σ • P)
    have hQ_ne := hQ_ne_bot Q_σ
    have hQ := hall Q_σ
    exact (ef_eq_one_iff_stabilizer_le_fixingSubgroup K L (σ • P) p E C_E Q_σ hp hQ_ne).mp hQ
  ·
    intro hall Q _ _
    obtain ⟨σ, hσ_over⟩ := h_exists_smul Q
    haveI : (σ • P).IsMaximal := Ideal.IsMaximal.smul ‹P.IsMaximal› σ
    haveI : (σ • P).LiesOver p := Ideal.LiesOver.smul σ
    haveI : (σ • P).LiesOver Q := hσ_over
    haveI : Algebra.IsSeparable (A ⧸ p) (B ⧸ (σ • P)) := h_sep_A (σ • P)
    haveI : Algebra.IsSeparable (C_E ⧸ Q) (B ⧸ (σ • P)) := h_sep_C Q (σ • P)
    have hQ_ne := hQ_ne_bot Q

    rw [show (Ideal.ramificationIdx p Q = 1 ∧ Ideal.inertiaDeg p Q = 1) ↔
        MulAction.stabilizer (L ≃ₐ[K] L) (σ • P) ≤ E.fixingSubgroup from
      ef_eq_one_iff_stabilizer_le_fixingSubgroup K L (σ • P) p E C_E Q hp hQ_ne]

    exact hall σ

end GaloisInertiaDecompositionFields

section FrobeniusElement

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

def IsFrobeniusElement (σ : G) (Q : Ideal B) (q : ℕ) : Prop :=
  ∀ x : B, (σ • x - x ^ q) ∈ Q

lemma isFrobeniusElement_one (Q : Ideal B) :
    IsFrobeniusElement G 1 Q 1 := by
  intro x; simp [one_smul, pow_one, sub_self, Q.zero_mem]

noncomputable def frobeniusElement (Q : Ideal B) (q : ℕ)
    (hexists : ∃! σ : G, IsFrobeniusElement G σ Q q) : G :=
  hexists.choose



end FrobeniusElement

section FrobeniusExistsUnique

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Finite G] [Algebra.IsInvariant A B G]

omit [Finite G] [Algebra.IsInvariant A B G] in
lemma isFrobeniusElement_eq_isArithFrobAt (σ : G) (Q : Ideal B) :
    IsFrobeniusElement G σ Q (Nat.card (A ⧸ Q.under A)) ↔ IsArithFrobAt A σ Q :=
  Iff.rfl

theorem frobenius_existsUnique_of_inertia_eq_bot
    (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)]
    (hunr : Q.inertia G = ⊥) :
    ∃! σ : G, IsFrobeniusElement G σ Q (Nat.card (A ⧸ Q.under A)) := by

  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant A G Q
  refine ⟨σ, hσ, fun σ' hσ' => ?_⟩

  have hmem : σ' * σ⁻¹ ∈ Q.inertia G := IsArithFrobAt.mul_inv_mem_inertia hσ' hσ

  rw [hunr, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

end FrobeniusExistsUnique

section FrobeniusConjugacy

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

lemma isFrobeniusElement_conj {σ τ : G} {Q : Ideal B} {q : ℕ}
    (hσ : IsFrobeniusElement G σ Q q) :
    IsFrobeniusElement G (τ * σ * τ⁻¹) (τ • Q) q := by
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, smul_pow']
  have heq : τ⁻¹ • (τ * σ * τ⁻¹) • x = σ • (τ⁻¹ • x) := by
    simp only [smul_smul]; congr 1; group
  rw [heq]
  exact hσ (τ⁻¹ • x)


end FrobeniusConjugacy

section FrobeniusClassDef

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]



end FrobeniusClassDef

section ArtinSymbolDef

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]


end ArtinSymbolDef

section SplittingCriterion

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]



end SplittingCriterion

section UnramifiedFrobeniusDataDef

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]


end UnramifiedFrobeniusDataDef

section SplitsCompletelyCriterion

open Ideal

variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  {p : Ideal A} [p.IsMaximal]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

theorem decompositionGroup_trivial_iff_splitsCompletely
    (hp : p ≠ ⊥) (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    MulAction.stabilizer G P = ⊥ ↔
      (primesOver p B).ncard = Nat.card G := by

  have hef : Nat.card (MulAction.stabilizer G P) = ramificationIdxIn p B * inertiaDegIn p B :=
    Ideal.card_stabilizer_eq p hp P
  have hefg : (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Nat.card G :=
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G
  rw [← Subgroup.card_eq_one]
  constructor
  ·
    intro h
    rw [hef] at h
    rw [h, mul_one] at hefg
    exact hefg
  ·
    intro h
    rw [hef]
    rw [← h] at hefg
    have hg_pos : (primesOver p B).ncard ≠ 0 := by
      rw [h]; exact Nat.card_pos.ne'
    have : (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) =
        (primesOver p B).ncard * 1 := by rw [mul_one]; exact hefg
    exact mul_left_cancel₀ hg_pos this



end SplitsCompletelyCriterion

section FrobeniusTower

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

lemma Ideal.pow_sub_pow_mem {R : Type*} [CommRing R] (I : Ideal R) {a b : R} (n : ℕ)
    (h : a - b ∈ I) : a ^ n - b ^ n ∈ I := by
  have hq : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b := Ideal.Quotient.eq.mpr h
  exact Ideal.Quotient.eq.mp (by simp only [map_pow, hq])

lemma isFrobeniusElement_pow {σ : G} {Q : Ideal B} {q : ℕ}
    (hσ : IsFrobeniusElement G σ Q q) (f : ℕ) :
    IsFrobeniusElement G (σ ^ f) Q (q ^ f) := by
  induction f with
  | zero => intro x; simp [pow_zero, one_smul, sub_self, Q.zero_mem]
  | succ n ih =>
    intro x
    rw [pow_succ, mul_smul]
    have h1 := ih (σ • x)
    have h2 : (σ • x) ^ (q ^ n) - (x ^ q) ^ (q ^ n) ∈ Q :=
      Ideal.pow_sub_pow_mem Q (q ^ n) (hσ x)
    have htele : σ ^ n • σ • x - x ^ q ^ (n + 1) =
        (σ ^ n • σ • x - (σ • x) ^ q ^ n) + ((σ • x) ^ q ^ n - (x ^ q) ^ q ^ n) := by ring
    rw [htele]
    exact Q.add_mem h1 h2


end FrobeniusTower

section FrobeniusRestriction

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

theorem isFrobeniusElement_restriction
    {C : Type*} [CommRing C]
    (H : Type*) [Group H] [MulSemiringAction H C]
    (ι : C →+* B) (ρ : G →* H)
    (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
    {σ : G} {Q : Ideal B} {q : ℕ}
    (hσ : IsFrobeniusElement G σ Q q) :
    IsFrobeniusElement H (ρ σ) (Q.comap ι) q := by
  intro c
  rw [Ideal.mem_comap]
  have : ι (ρ σ • c - c ^ q) = σ • ι c - (ι c) ^ q := by
    rw [map_sub, map_pow, hcompat]
  rw [this]
  exact hσ (ι c)


end FrobeniusRestriction

section FrobeniusInertiaHelpers

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

lemma isFrobeniusElement_mul_inv_mem_inertia
    {σ σ' : G} {Q : Ideal B} {n : ℕ}
    (h1 : IsFrobeniusElement G σ Q n)
    (h2 : IsFrobeniusElement G σ' Q n) :
    σ * σ'⁻¹ ∈ Q.inertia G := by
  intro x
  simpa [mul_smul] using Q.sub_mem (h1 (σ'⁻¹ • x)) (h2 (σ'⁻¹ • x))

lemma frobenius_existsUnique_of_exists_of_inertia_eq_bot
    {Q : Ideal B} {n : ℕ} {σ : G}
    (hσ : IsFrobeniusElement G σ Q n)
    (hunr : Q.inertia G = ⊥) :
    ∃! τ : G, IsFrobeniusElement G τ Q n := by
  refine ⟨σ, hσ, fun σ' hσ' => ?_⟩
  have hmem : σ' * σ⁻¹ ∈ Q.inertia G :=
    isFrobeniusElement_mul_inv_mem_inertia G hσ' hσ
  rw [hunr, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

end FrobeniusInertiaHelpers

section FrobeniusTowerAndRestriction

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]



end FrobeniusTowerAndRestriction

section ArtinMapDef

variable {A : Type*} [CommRing A]
  (G : Type*) [CommGroup G]

noncomputable def artinMap
    {S : Set (Ideal A)}
    (artinSymbolPrime : {𝔭 : Ideal A // 𝔭.IsPrime ∧ 𝔭 ∉ S} → G) :
    FreeAbelianGroup {𝔭 : Ideal A // 𝔭.IsPrime ∧ 𝔭 ∉ S} →+ Additive G :=
  FreeAbelianGroup.lift (fun 𝔭 => Additive.ofMul (artinSymbolPrime 𝔭))

lemma artinMap_of {S : Set (Ideal A)}
    (artinSymbolPrime : {𝔭 : Ideal A // 𝔭.IsPrime ∧ 𝔭 ∉ S} → G)
    (𝔭 : {𝔭 : Ideal A // 𝔭.IsPrime ∧ 𝔭 ∉ S}) :
    artinMap G artinSymbolPrime (FreeAbelianGroup.of 𝔭) =
      Additive.ofMul (artinSymbolPrime 𝔭) := by
  simp [artinMap, FreeAbelianGroup.lift_apply_of]

end ArtinMapDef
