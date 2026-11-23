/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.LocalExtensions
import Atlas.NumberTheoryI.code.ResidueFieldFunctor
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section

open Ideal Polynomial IsLocalRing

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 80000 in
theorem isFiniteUnramifiedSubext_integralClosure_isUnramifiedDVR
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    (E : IntermediateField K L)
    (hE : IsFiniteUnramifiedSubext A K L E)


    [IsDomain (integralClosure A ↥E)]
    [IsDiscreteValuationRing (integralClosure A ↥E)]
    [IsLocalHom (algebraMap A (integralClosure A ↥E))]
    [Module.Finite A (integralClosure A ↥E)] :
    IsUnramifiedDVRExtension A (integralClosure A ↥E) := by
  obtain ⟨_, hunr⟩ := hE

  letI : Algebra.FormallyUnramified A (integralClosure A ↥E) := hunr
  haveI : NoZeroSMulDivisors A (integralClosure A ↥E) := by
    haveI : NoZeroSMulDivisors A ↥E := by
      constructor
      intro a b hab
      rw [Algebra.smul_def] at hab
      rcases mul_eq_zero.mp hab with h | h
      · left
        have : Function.Injective (algebraMap A ↥E) := by
          rw [IsScalarTower.algebraMap_eq A K ↥E]
          exact (algebraMap K ↥E).injective.comp (IsFractionRing.injective A K)
        exact this (by rw [h, map_zero])
      · right
        exact h
    exact Function.Injective.noZeroSMulDivisors
      (integralClosure A ↥E).val Subtype.val_injective rfl (fun _ _ => rfl)
  haveI : Module.Free A (integralClosure A ↥E) := Module.free_of_finite_type_torsion_free'
  haveI : Algebra.EssFiniteType A (integralClosure A ↥E) :=
    Algebra.EssFiniteType.of_finiteType A (integralClosure A ↥E)

  exact {
    residue_separable := inferInstance
    degree_eq := by
      set B := integralClosure A ↥E
      have hmapmax := Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := B)
      letI : Algebra (ResidueField A)
          (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) :=
        Ideal.Quotient.algebraQuotientMapQuotient
      have e : (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) ≃ₐ[ResidueField A]
          ResidueField B :=
        AlgEquiv.ofRingEquiv (f := Ideal.quotEquivOfEq hmapmax) (fun x => by
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
          rfl)
      rw [← IsLocalRing.finrank_quotient_map (R := A) (S := B)]
      exact e.toLinearEquiv.finrank_eq }

end
