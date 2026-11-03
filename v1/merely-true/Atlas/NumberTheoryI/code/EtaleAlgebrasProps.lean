/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped Classical

namespace EtaleAlgebra

lemma pi_single_mul {ι : Type*} [DecidableEq ι] {F : ι → Type*}
    [∀ i, CommMonoidWithZero (F i)] (i : ι) (a : F i) (f : ∀ j, F j) :
    Pi.single i a * f = Pi.single i (a * f i) := by
  ext j; simp only [Pi.mul_apply]
  by_cases h : j = i
  · subst h; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

lemma pi_field_not_domain_of_two {ι : Type*} {F : ι → Type*}
    [∀ i, Field (F i)] [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) :
    ¬ NoZeroDivisors (∀ k, F k) := by
  intro h
  have h1 : Pi.single i (1 : F i) ≠ (0 : ∀ k, F k) := by
    intro heq; have := congr_fun heq i; simp [Pi.single_eq_same] at this
  have h2 : Pi.single j (1 : F j) ≠ (0 : ∀ k, F k) := by
    intro heq; have := congr_fun heq j; simp [Pi.single_eq_same] at this
  have h3 : Pi.single i (1 : F i) * Pi.single j (1 : F j) = (0 : ∀ k, F k) := by
    ext k; simp only [Pi.mul_apply, Pi.zero_apply]
    by_cases hki : k = i
    · subst hki; simp [Pi.single_eq_same, Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hki]
  exact (h.eq_zero_or_eq_zero_of_mul_eq_zero h3).elim h1 h2

noncomputable def piSingletonAlgEquiv {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
    (j : ι) (hsing : ∀ i : ι, i = j) :
    (∀ i, F i) ≃ₐ[K] F j where
  toFun f := f j
  invFun x i := hsing i ▸ x
  left_inv f := by ext i; have hi := hsing i; subst hi; simp
  right_inv x := by simp
  map_mul' f g := by simp
  map_add' f g := by simp
  commutes' r := by simp [Pi.algebraMap_apply]

structure IsEtaleAlgebra (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K L] :
    Prop where
  exists_decomp : ∃ (ι : Type) (_ : Fintype ι) (F : ι → Type)
    (_ : ∀ i, Field (F i)) (_ : ∀ i, Algebra K (F i))
    (_ : ∀ i, Algebra.IsSeparable K (F i)),
    Nonempty (L ≃ₐ[K] ∀ i, F i)

def IsFiniteEtaleAlgebra (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K L] :
    Prop :=
  IsEtaleAlgebra K L ∧ Module.Finite K L

section SurjectionsFromProductsOfFields

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]

noncomputable def piRestr (S : Finset ι) :
    (∀ i, F i) →ₐ[K] ∀ i : S, F i where
  toFun f i := f i
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := by ext; simp [Pi.algebraMap_apply]

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma piRestr_apply (S : Finset ι) (f : ∀ i, F i) (j : S) :
    piRestr (K := K) S f j = f j := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma piRestr_surjective (S : Finset ι) :
    Function.Surjective (piRestr (K := K) (F := F) S) := by
  intro f; use fun i => if h : i ∈ S then f ⟨i, h⟩ else 0
  ext ⟨i, hi⟩; dsimp [piRestr]; rw [dif_pos hi]

omit [Fintype ι] [DecidableEq ι] in
lemma mem_ker_piRestr (S : Finset ι) (f : ∀ i, F i) :
    f ∈ RingHom.ker (piRestr (K := K) (F := F) S) ↔ ∀ i ∈ S, f i = 0 := by
  constructor
  · intro hf i hi; exact congr_fun hf ⟨i, hi⟩
  · intro hf; ext ⟨i, hi⟩; exact hf i hi

theorem ker_phi_eq_ker_piRestr {B : Type*} [CommRing B] [Algebra K B]
    (φ : (∀ i, F i) →ₐ[K] B) :
    let T := Finset.univ.filter (fun i => ∃ f ∈ RingHom.ker φ, f i ≠ 0)
    RingHom.ker φ = RingHom.ker (piRestr (K := K) (F := F) (Finset.univ \ T)) := by
  intro T; ext f; rw [mem_ker_piRestr]; constructor
  · intro hf i hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, T,
      Finset.mem_filter, not_exists] at hi
    push Not at hi; exact hi f hf
  · intro hf
    suffices h : ∀ i ∉ T, f i = 0 by
      have decomp : f = ∑ j ∈ T, Pi.single j (1 : F j) * f := by
        conv_lhs => rw [← Finset.univ_sum_single f]
        simp_rw [show ∀ i, Pi.single i (f i) = Pi.single i (1 : F i) * f from
          fun i => by rw [pi_single_mul, one_mul]]
        symm; apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hj; rw [pi_single_mul, one_mul, h j hj, Pi.single_zero]
      rw [decomp]; apply Ideal.sum_mem; intro j hj
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨g, hg, hgi⟩ := hj
      have ej_mem : Pi.single j (1 : F j) ∈ RingHom.ker φ := by
        have : Pi.single j (g j)⁻¹ * g ∈ RingHom.ker φ := Ideal.mul_mem_left _ _ hg
        rwa [pi_single_mul, inv_mul_cancel₀ hgi] at this
      exact Ideal.mul_mem_right _ _ ej_mem
    exact fun i hi => hf i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)

noncomputable def algEquivOfSurjSameKer {R A B C : Type*}
    [CommSemiring R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    (f : A →ₐ[R] B) (g : A →ₐ[R] C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : RingHom.ker f = RingHom.ker g) : B ≃ₐ[R] C :=
  (Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans
    ((Ideal.quotientEquivAlgOfEq R hker).trans (Ideal.quotientKerAlgEquivOfSurjective hg))

theorem surj_algHom_pi_fields_isSubproduct {B : Type*} [CommRing B] [Algebra K B]
    (φ : (∀ i, F i) →ₐ[K] B) (hφ : Function.Surjective φ) :
    ∃ S : Finset ι, Nonempty (B ≃ₐ[K] ∀ i : S, F i) := by
  let T := Finset.univ.filter (fun i => ∃ f ∈ RingHom.ker φ, f i ≠ 0)
  exact ⟨Finset.univ \ T,
    ⟨algEquivOfSurjSameKer φ (piRestr (Finset.univ \ T)) hφ
      (piRestr_surjective _) (ker_phi_eq_ker_piRestr φ)⟩⟩

end SurjectionsFromProductsOfFields

section DecompositionUniqueness

variable {K : Type*} [Field K]

theorem algEquiv_field_of_pi_field {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
    {E : Type*} [Field E] [Algebra K E]
    (e : E ≃ₐ[K] ∀ i, F i) :
    ∃ j : ι, Nonempty (E ≃ₐ[K] F j) := by
  have hne : Nonempty ι := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    exact one_ne_zero (e.injective (funext (IsEmpty.elim hemp)))
  have hnd : NoZeroDivisors (∀ i, F i) := by
    constructor; intro a b hab; by_contra hc; push Not at hc
    obtain ⟨ha0, hb0⟩ := hc
    have hea : e.symm a ≠ 0 := fun h => ha0 (e.symm.injective (by simp [h]))
    have heb : e.symm b ≠ 0 := fun h => hb0 (e.symm.injective (by simp [h]))
    have : e.symm a * e.symm b ≠ 0 := by
      intro h; exact absurd (mul_eq_zero.mp h) (by push Not; exact ⟨hea, heb⟩)
    rw [show e.symm a * e.symm b = e.symm (a * b) from by simp, hab, map_zero] at this
    exact this rfl
  have hsing : ∀ i j : ι, i = j := by
    intro i j; by_contra hij; exact pi_field_not_domain_of_two hij hnd
  obtain ⟨j⟩ := hne
  exact ⟨j, ⟨e.trans (piSingletonAlgEquiv j (hsing · j))⟩⟩

theorem surjection_to_field_factors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
    {E : Type*} [Field E] [Algebra K E]
    (φ : (∀ i, F i) →ₐ[K] E) (hφ : Function.Surjective φ) :
    ∃ j : ι, Nonempty (E ≃ₐ[K] F j) := by
  obtain ⟨S, ⟨e⟩⟩ := surj_algHom_pi_fields_isSubproduct φ hφ
  obtain ⟨⟨j, _⟩, ⟨iso⟩⟩ := algEquiv_field_of_pi_field e
  exact ⟨j, ⟨iso⟩⟩

theorem etale_decomposition_unique
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
    {G : κ → Type*} [∀ j, Field (G j)] [∀ j, Algebra K (G j)]
    (e : (∀ i, F i) ≃ₐ[K] ∀ j, G j) :
    (∀ i, ∃ j, Nonempty (F i ≃ₐ[K] G j)) ∧
    (∀ j, ∃ i, Nonempty (G j ≃ₐ[K] F i)) := by
  constructor
  · intro i
    have hsurj : Function.Surjective ((Pi.evalAlgHom K F i).comp e.symm.toAlgHom) := by
      intro x
      obtain ⟨y, hy⟩ := e.symm.surjective (Pi.single i x)
      exact ⟨y, by simp [hy, Pi.evalAlgHom_apply, Pi.single_eq_same]⟩
    exact surjection_to_field_factors _ hsurj
  · intro j
    have hsurj : Function.Surjective ((Pi.evalAlgHom K G j).comp e.toAlgHom) := by
      intro x
      obtain ⟨y, hy⟩ := e.surjective (Pi.single j x)
      exact ⟨y, by simp [hy, Pi.evalAlgHom_apply, Pi.single_eq_same]⟩
    exact surjection_to_field_factors _ hsurj

end DecompositionUniqueness

section BaseChange

abbrev baseChange (A : Type*) [CommRing A]
    (M : Type*) [AddCommGroup M] [Module A M]
    (B : Type*) [CommRing B] [Algebra A B] : Type _ :=
  TensorProduct A B M

instance baseChange.instModule (A : Type*) [CommRing A]
    (M : Type*) [AddCommGroup M] [Module A M]
    (B : Type*) [CommRing B] [Algebra A B] :
    Module B (baseChange A M B) := inferInstance

instance baseChange.instAlgebra (A : Type*) [CommRing A]
    (M : Type*) [CommRing M] [Algebra A M]
    (B : Type*) [CommRing B] [Algebra A B] :
    Algebra B (TensorProduct A B M) := inferInstance

end BaseChange

end EtaleAlgebra
