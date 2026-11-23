/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.TypeTags.Basic
import Atlas.NumberTheoryI.code.GroupCounts

noncomputable section

namespace KroneckerWeberLocal2

class IsCyclicExtension (F : Type*) (E : Type*) [Field F] [Field E]
    [Algebra F E] : Prop where
  isGalois : IsGalois F E
  isCyclic : IsCyclic (E ≃ₐ[F] E)

def LiesInCyclotomicExtension (F : Type*) (K : Type*) [Field F] [Field K]
    [Algebra F K] : Prop :=
  ∃ (m : ℕ+), Nonempty (K →ₐ[F] CyclotomicField (m : ℕ) F)

lemma index_map_mulEquiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') (H : Subgroup G) :
    (H.map φ.toMonoidHom).index = H.index := by
  apply Subgroup.index_map_eq
  · exact φ.surjective
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x = 1 := φ.injective (hx.trans (map_one φ).symm)
    rw [this]; exact H.one_mem

lemma index_subgroups_card_eq_of_mulEquiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') (n : ℕ) :
    Nat.card {H : Subgroup G // H.index = n} =
      Nat.card {H : Subgroup G' // H.index = n} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ.mapSubgroup.toEquiv ?_
  intro H
  constructor
  · intro h
    change (φ.mapSubgroup H).index = n
    rw [show (φ.mapSubgroup H) = H.map φ.toMonoidHom from rfl]
    rw [index_map_mulEquiv]; exact h
  · intro h
    have : (φ.mapSubgroup H).index = n := h
    rw [show (φ.mapSubgroup H) = H.map φ.toMonoidHom from rfl] at this
    rw [index_map_mulEquiv] at this; exact this

def galoisCorrespondenceIndex (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (n : ℕ) :
    {H : Subgroup (K ≃ₐ[F] K) // H.index = n} ≃
    {L : IntermediateField F K // Module.finrank F L = n} where
  toFun := fun ⟨H, hH⟩ => ⟨IntermediateField.fixedField H, by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
        @IntermediateField.fixingSubgroup_fixedField F _ K _ _ H _]
    exact hH⟩
  invFun := fun ⟨L, hL⟩ => ⟨L.fixingSubgroup, by
    rwa [← IntermediateField.finrank_eq_fixingSubgroup_index]⟩
  left_inv := fun ⟨H, _⟩ => by
    simp only [Subtype.mk.injEq]
    exact @IntermediateField.fixingSubgroup_fixedField F _ K _ _ H _
  right_inv := fun ⟨L, _⟩ => by
    simp only [Subtype.mk.injEq]
    exact IsGalois.fixedField_fixingSubgroup L










theorem cyclic_normal_index_subgroups_card_eq_of_mulEquiv
    {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') (n : ℕ) :
    Nat.card {H : Subgroup G // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G ⧸ H)} =
    Nat.card {H : Subgroup G' // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G' ⧸ H)} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ.mapSubgroup.toEquiv ?_
  intro H
  constructor
  · rintro ⟨h_idx, h_norm, h_cyc⟩
    have h_norm' : (φ.mapSubgroup H).Normal := by
      change (H.map φ.toMonoidHom).Normal
      exact Subgroup.Normal.map h_norm φ.toMonoidHom φ.surjective
    refine ⟨?_, h_norm', ?_⟩
    · change (H.map (φ : G →* G')).index = n
      rw [Subgroup.index_map_equiv H φ]; exact h_idx
    · haveI : (H.map φ.toMonoidHom).Normal :=
        Subgroup.Normal.map h_norm φ.toMonoidHom φ.surjective
      haveI := h_norm
      exact (QuotientGroup.congr H (H.map φ.toMonoidHom) φ rfl).isCyclic.mp h_cyc
  · rintro ⟨h_idx, h_norm, h_cyc⟩
    have h_norm' : (φ.mapSubgroup H).Normal := h_norm
    haveI : (φ.mapSubgroup.toEquiv H).Normal := h_norm
    haveI : (H.map (φ : G →* G')).Normal := ‹_›
    have h_normH : H.Normal := by
      have heq : H = (H.map (φ : G →* G')).comap (φ : G →* G') := by
        ext x; constructor
        · intro hx; exact ⟨x, hx, rfl⟩
        · rintro ⟨y, hy, he⟩; exact φ.injective he ▸ hy
      rw [heq]; exact Subgroup.Normal.comap ‹(H.map (φ : G →* G')).Normal› _
    refine ⟨?_, h_normH, ?_⟩
    · change (H.map (φ : G →* G')).index = n at h_idx
      rw [Subgroup.index_map_equiv H φ] at h_idx; exact h_idx
    · haveI := h_normH
      haveI : (H.map φ.toMonoidHom).Normal := ‹(H.map (φ : G →* G')).Normal›
      exact (QuotientGroup.congr H (H.map φ.toMonoidHom) φ rfl).isCyclic.mpr h_cyc




theorem galois_quotient_extension.{u₁, u₂, u₃}
    (F : Type u₁) (L : Type u₂) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (Q : Type u₃) [Group Q] [Fintype Q]
    (φ : (L ≃ₐ[F] L) →* Q) (hφ : Function.Surjective φ) :
    ∃ (E : Type u₂) (_ : Field E) (_ : Algebra F E)
      (_ : FiniteDimensional F E) (_ : IsGalois F E),
      Nonempty ((E ≃ₐ[F] E) ≃* Q) := by
  let H := φ.ker
  let E := IntermediateField.fixedField H
  haveI : Subgroup.Normal H := φ.normal_ker
  haveI : IsGalois F E := IsGalois.of_fixedField_normal_subgroup H
  have iso1 : (L ≃ₐ[F] L) ⧸ H ≃* (↥E ≃ₐ[F] ↥E) := IsGalois.normalAutEquivQuotient H
  have iso2 : (L ≃ₐ[F] L) ⧸ H ≃* Q := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  exact ⟨↥E, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨iso1.symm.trans iso2⟩⟩



lemma surjective_toMultiplicative {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (f : A →+ B) (hf : Function.Surjective f) :
    Function.Surjective (AddMonoidHom.toMultiplicative f) := by
  intro b
  obtain ⟨a, ha⟩ := hf (Multiplicative.toAdd b)
  exact ⟨Multiplicative.ofAdd a, by simp [AddMonoidHom.toMultiplicative, ha]⟩

lemma addMonoidHom_prodMap_surjective {M N M' N' : Type*}
    [AddZeroClass M] [AddZeroClass N] [AddZeroClass M'] [AddZeroClass N']
    (f : M →+ M') (g : N →+ N')
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (AddMonoidHom.prodMap f g) := by
  intro ⟨m', n'⟩
  obtain ⟨m, hm⟩ := hf m'
  obtain ⟨n, hn⟩ := hg n'
  exact ⟨(m, n), Prod.ext (by simp [hm]) (by simp [hn])⟩




end KroneckerWeberLocal2

end
