/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Jacobson.Ring

set_option maxHeartbeats 800000

noncomputable section

open Ideal

section Nakayama

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Determinant form of Nakayama's lemma (Lem 4, Lec 3): if `I · M = M` for a
finitely generated module `M`, there exists `a` with `a - 1 ∈ I` annihilating `M`. -/
theorem nakayama_determinant_form [Module.Finite R M] (I : Ideal R)
    (hIM : I • (⊤ : Submodule R M) = ⊤) :
    ∃ a : R, a - 1 ∈ I ∧ ∀ m : M, a • m = 0 := by
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    I ⊤ Module.Finite.fg_top (ge_of_eq hIM)
  exact ⟨r, hr1, fun m => hr2 m Submodule.mem_top⟩

/-- Identity-element form of Nakayama: under the same hypotheses, there is some
`a ∈ I` acting as the identity on `M`. -/
theorem nakayama_exists_identity_element [Module.Finite R M] (I : Ideal R)
    (hIM : I • (⊤ : Submodule R M) = ⊤) :
    ∃ a ∈ I, ∀ m : M, a • m = m := by
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul
    I ⊤ Module.Finite.fg_top (ge_of_eq hIM)
  exact ⟨r, hr1, fun m => hr2 m Submodule.mem_top⟩

/-- Nakayama: if `I` is contained in the Jacobson radical and `M` is nontrivial,
then `I · M ≠ M`. -/
theorem nakayama_ne_top_of_le_jacobson [Nontrivial M] [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ jacobson ⊥) :
    I • (⊤ : Submodule R M) ≠ ⊤ :=
  Ne.symm (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (le_trans hI (jacobson_mono bot_le)))

/-- Contrapositive form: if `I · M = M` with `I` in the Jacobson radical, then
`M` is the zero module. -/
theorem nakayama_subsingleton_of_le_jacobson [Module.Finite R M]
    (I : Ideal R) (hIM : I • (⊤ : Submodule R M) = ⊤)
    (hIjac : I ≤ jacobson ⊥) : Subsingleton M := by
  have h := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤
    Module.Finite.fg_top (ge_of_eq hIM) hIjac
  have : ∀ x : M, x = 0 := fun x =>
    (Submodule.mem_bot R).mp (h ▸ Submodule.mem_top)
  exact ⟨fun a b => by rw [this a, this b]⟩

end Nakayama

section FiniteMorphisms

/-- A finite faithful algebra has surjective `Spec` (going-up applied to integral). -/
theorem finite_morphism_spec_surjective
    (B A : Type*) [CommRing B] [CommRing A] [Algebra B A]
    [Module.Finite B A] [FaithfulSMul B A] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap B A)) := by
  have hInt : (algebraMap B A).IsIntegral := fun x => IsIntegral.of_finite B x
  exact hInt.comap_surjective (FaithfulSMul.algebraMap_injective B A)

/-- Ring-hom version: an injective finite ring homomorphism is surjective on
prime spectra. -/
theorem finite_morphism_spec_surjective_of_ringHom {B A : Type*} [CommRing B] [CommRing A]
    (f : B →+* A) (hfin : f.Finite) (hinj : Function.Injective f) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  algebraize [f]
  have : Module.Finite B A := hfin
  have hInt : f.IsIntegral := fun x => IsIntegral.of_finite B x
  exact hInt.comap_surjective hinj

end FiniteMorphisms

section Nullstellensatz

/-- Essential form of the Nullstellensatz: a field which is a finitely generated
algebra over another field is algebraic over it. -/
theorem essential_nullstellensatz
    (k A : Type*) [Field k] [Field A] [Algebra k A]
    [Algebra.FiniteType k A] : Algebra.IsAlgebraic k A := by
  have : Module.Finite k A := finite_of_finite_type_of_isJacobsonRing k A
  exact Algebra.IsAlgebraic.of_finite k A

/-- A field that is finitely generated as a `k`-algebra is in fact a finite
`k`-module. -/
theorem finite_of_finiteType_field
    (k A : Type*) [Field k] [Field A] [Algebra k A]
    [Algebra.FiniteType k A] : Module.Finite k A :=
  finite_of_finite_type_of_isJacobsonRing k A

end Nullstellensatz
