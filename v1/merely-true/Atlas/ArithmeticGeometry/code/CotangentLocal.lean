/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Derivation.Basic

open IsLocalRing

namespace CotangentDual

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {k : Type*} [Field k] [Algebra k R] [Algebra R k]
variable [IsScalarTower k R k]

omit [IsLocalRing R] in
lemma algebraMap_comp_section (c : k) : algebraMap R k (algebraMap k R c) = c := by
  have := IsScalarTower.algebraMap_apply k R k c
  rw [Algebra.algebraMap_self_apply] at this; exact this.symm

omit [Algebra k R] [IsScalarTower k R k] in
lemma mem_maximalIdeal_map_zero
    (hφ : Function.Surjective (algebraMap R k)) (x : maximalIdeal R) :
    algebraMap R k x.val = 0 := by
  rw [← RingHom.mem_ker, IsLocalRing.ker_eq_maximalIdeal (algebraMap R k) hφ]; exact x.2

noncomputable def projMaxIdeal
    (hφ : Function.Surjective (algebraMap R k)) (r : R) : maximalIdeal R :=
  ⟨r - algebraMap k R (algebraMap R k r), by
    rw [← IsLocalRing.ker_eq_maximalIdeal (algebraMap R k) hφ, RingHom.mem_ker, map_sub,
      ← IsScalarTower.algebraMap_apply k R k]; simp⟩

lemma projMaxIdeal_add (hφ : Function.Surjective (algebraMap R k)) (x y : R) :
    projMaxIdeal hφ (x + y) = projMaxIdeal hφ x + projMaxIdeal hφ y := by
  apply Subtype.ext; simp [projMaxIdeal, map_add]; ring

lemma projMaxIdeal_smul (hφ : Function.Surjective (algebraMap R k)) (c : k) (x : R) :
    projMaxIdeal hφ (c • x) = c • projMaxIdeal hφ x := by
  apply Subtype.ext
  show (projMaxIdeal hφ (c • x)).val = c • (projMaxIdeal hφ x : R)
  simp only [projMaxIdeal, Subtype.coe_mk, Algebra.smul_def (R := k) (A := R),
    map_mul (f := algebraMap R k), algebraMap_comp_section, map_mul (f := algebraMap k R)]
  ring

lemma projMaxIdeal_one (hφ : Function.Surjective (algebraMap R k)) :
    projMaxIdeal hφ 1 = 0 := by
  apply Subtype.ext; simp [projMaxIdeal]

lemma projMaxIdeal_of_mem
    (hφ : Function.Surjective (algebraMap R k)) (m : maximalIdeal R) :
    (maximalIdeal R).toCotangent (projMaxIdeal hφ m.val) =
    (maximalIdeal R).toCotangent m := by
  rw [Ideal.toCotangent_eq]
  have hm : algebraMap R k m.val = 0 := mem_maximalIdeal_map_zero hφ m
  have hsub : (projMaxIdeal hφ m.val - m : maximalIdeal R).val = 0 := by
    simp only [projMaxIdeal, Submodule.coe_sub]; ring_nf; simp [hm]
  rw [show (projMaxIdeal hφ m.val - m : R) =
    (projMaxIdeal hφ m.val - m : maximalIdeal R).val from rfl, hsub]
  exact zero_mem _

lemma projCotangent_leibniz (hφ : Function.Surjective (algebraMap R k)) (x y : R) :
    (maximalIdeal R).toCotangent (projMaxIdeal hφ (x * y)) =
    algebraMap k R (algebraMap R k x) • (maximalIdeal R).toCotangent (projMaxIdeal hφ y) +
    algebraMap k R (algebraMap R k y) • (maximalIdeal R).toCotangent (projMaxIdeal hφ x) := by
  set d := projMaxIdeal hφ (x * y) -
      algebraMap k R (algebraMap R k x) • projMaxIdeal hφ y -
      algebraMap k R (algebraMap R k y) • projMaxIdeal hφ x
  have hd : (maximalIdeal R).toCotangent d = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    have hval : (d : R) = (projMaxIdeal hφ x).val * (projMaxIdeal hφ y).val := by
      change (projMaxIdeal hφ (x * y)).val -
        algebraMap k R (algebraMap R k x) * (projMaxIdeal hφ y).val -
        algebraMap k R (algebraMap R k y) * (projMaxIdeal hφ x).val =
        (projMaxIdeal hφ x).val * (projMaxIdeal hφ y).val
      simp only [projMaxIdeal, Subtype.coe_mk]
      have : algebraMap k R (algebraMap R k (x * y)) =
          algebraMap k R (algebraMap R k x) * algebraMap k R (algebraMap R k y) := by
        rw [map_mul, map_mul]
      rw [this]; ring
    rw [hval, pow_two]
    exact Ideal.mul_mem_mul (projMaxIdeal hφ x).2 (projMaxIdeal hφ y).2
  have expand : (maximalIdeal R).toCotangent d =
      (maximalIdeal R).toCotangent (projMaxIdeal hφ (x * y)) -
      algebraMap k R (algebraMap R k x) • (maximalIdeal R).toCotangent (projMaxIdeal hφ y) -
      algebraMap k R (algebraMap R k y) • (maximalIdeal R).toCotangent (projMaxIdeal hφ x) := by
    rw [map_sub, map_sub, map_smul, map_smul]
  rw [expand] at hd; rw [← sub_eq_zero, sub_add_eq_sub_sub]; exact hd

noncomputable def derivRestrict (D : Derivation k R k) : (maximalIdeal R) →ₗ[k] k where
  toFun m := D m.val
  map_add' x y := by simp [map_add]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    show D (c • x).val = c * D x.val
    have : (c • x : maximalIdeal R).val = algebraMap k R c * x.val := by simp [Algebra.smul_def]
    rw [this, show algebraMap k R c * x.val = c • x.val from (Algebra.smul_def c x.val).symm]
    exact D.toLinearMap.map_smul c x.val

omit [IsScalarTower k R k] in
lemma derivRestrict_vanishes
    (hφ : Function.Surjective (algebraMap R k))
    (D : Derivation k R k) (x y : maximalIdeal R) :
    derivRestrict D (x * y) = 0 := by
  show D (x.val * y.val) = 0
  rw [D.leibniz]
  simp [Algebra.smul_def, mem_maximalIdeal_map_zero hφ x, mem_maximalIdeal_map_zero hφ y]

noncomputable def derivToDual
    (hφ : Function.Surjective (algebraMap R k))
    (D : Derivation k R k) : Module.Dual k (CotangentSpace R) :=
  Ideal.Cotangent.lift (derivRestrict D) (derivRestrict_vanishes hφ D)

noncomputable def dualToDeriv
    (hφ : Function.Surjective (algebraMap R k))
    (ψ : Module.Dual k (CotangentSpace R)) : Derivation k R k where
  toLinearMap := {
    toFun := fun r => ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ r))
    map_add' := fun x y => by rw [projMaxIdeal_add, map_add, map_add]
    map_smul' := fun c x => by
      simp only [RingHom.id_apply]
      rw [projMaxIdeal_smul, LinearMap.map_smul_of_tower, map_smul]
  }
  map_one_eq_zero' := by
    show ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ 1)) = 0
    rw [projMaxIdeal_one, map_zero, map_zero]
  leibniz' := fun a b => by
    show ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ (a * b))) =
      a • ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ b)) +
      b • ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ a))
    rw [projCotangent_leibniz hφ, map_add]
    simp_rw [algebraMap_smul R]; simp_rw [map_smul]
    simp only [Algebra.algebraMap_self_apply, Algebra.smul_def]

noncomputable def derivToDualLinear
    (hφ : Function.Surjective (algebraMap R k)) :
    Derivation k R k →ₗ[k] Module.Dual k (CotangentSpace R) where
  toFun := derivToDual hφ
  map_add' D₁ D₂ := by
    ext v; induction v using Quotient.inductionOn with
    | h m =>
      show (derivToDual hφ (D₁ + D₂)) ((maximalIdeal R).toCotangent m) =
        ((derivToDual hφ D₁) + (derivToDual hφ D₂)) ((maximalIdeal R).toCotangent m)
      simp only [derivToDual, Ideal.Cotangent.lift_toCotangent, derivRestrict,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]; rfl
  map_smul' c D := by
    ext v; induction v using Quotient.inductionOn with
    | h m =>
      show (derivToDual hφ (c • D)) ((maximalIdeal R).toCotangent m) =
        (c • (derivToDual hφ D)) ((maximalIdeal R).toCotangent m)
      simp only [derivToDual, Ideal.Cotangent.lift_toCotangent, derivRestrict,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul]; rfl

noncomputable def dualToDerivLinear
    (hφ : Function.Surjective (algebraMap R k)) :
    Module.Dual k (CotangentSpace R) →ₗ[k] Derivation k R k where
  toFun := dualToDeriv hφ
  map_add' ψ₁ ψ₂ := by ext r; simp [dualToDeriv]
  map_smul' c ψ := by ext r; simp [dualToDeriv]

noncomputable def cotangentDualEquivDerivation
    (hφ : Function.Surjective (algebraMap R k)) :
    Module.Dual k (CotangentSpace R) ≃ₗ[k] Derivation k R k :=
  LinearEquiv.ofLinear (dualToDerivLinear hφ) (derivToDualLinear hφ)
    (by
      ext D a
      show (derivToDual hφ D) ((maximalIdeal R).toCotangent (projMaxIdeal hφ a)) = D a
      show D (projMaxIdeal hφ a).val = D a
      simp only [projMaxIdeal, Subtype.coe_mk, map_sub, Derivation.map_algebraMap, sub_zero])
    (by
      ext ψ v
      induction v using Quotient.inductionOn with
      | h m =>
        show (derivToDual hφ (dualToDeriv hφ ψ)) ((maximalIdeal R).toCotangent m) =
          ψ ((maximalIdeal R).toCotangent m)
        simp only [derivToDual, Ideal.Cotangent.lift_toCotangent, derivRestrict,
          LinearMap.coe_mk, AddHom.coe_mk]
        show ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ m.val)) =
          ψ ((maximalIdeal R).toCotangent m)
        rw [projMaxIdeal_of_mem])

theorem cotangent_dual_tangent
    (hφ : Function.Surjective (algebraMap R k)) :
    Nonempty (Module.Dual k (CotangentSpace R) ≃ₗ[k] Derivation k R k) :=
  ⟨cotangentDualEquivDerivation hφ⟩

end CotangentDual
