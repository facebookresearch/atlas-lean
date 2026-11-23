/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.FiniteStability
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

open TensorProduct
set_option autoImplicit false

class IsAffineAlgebra (k : Type*) (R : Type*) [Field k] [CommRing R] [Algebra k R] : Prop where
  isDomain : IsDomain R
  finiteType : Algebra.FiniteType k R


attribute [instance] IsAffineAlgebra.isDomain IsAffineAlgebra.finiteType

section Helpers

variable {k : Type*} [Field k] [IsAlgClosed k]
  {R : Type*} [CommRing R] [Algebra k R] [IsDomain R] [Algebra.FiniteType k R]
  {S : Type*} [CommRing S] [Algebra k S] [IsDomain S]

noncomputable def algHomOfMaximalIdeal (k : Type*) {R : Type*}
    [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R] [IsDomain R] [Algebra.FiniteType k R]
    (m : Ideal R) [hm : m.IsMaximal] : R →ₐ[k] k := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) := Algebra.FiniteType.quotient k m
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := Algebra.IsIntegral.of_finite k (R ⧸ m)
  exact (AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := R ⧸ m))).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom k R (R ⧸ m))

lemma algHomOfMaximalIdeal_ker (m : Ideal R) [hm : m.IsMaximal] (r : R) :
    algHomOfMaximalIdeal k m r = 0 ↔ r ∈ m := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) := Algebra.FiniteType.quotient k m
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := Algebra.IsIntegral.of_finite k (R ⧸ m)
  unfold algHomOfMaximalIdeal
  simp only [AlgHom.coe_comp, AlgEquiv.coe_algHom, Function.comp_apply]
  constructor
  · intro h
    have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := R ⧸ m)
    let e := AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) hbij
    have heq : e (e.symm (IsScalarTower.toAlgHom k R (R ⧸ m) r)) = e 0 := congr_arg e h
    simp only [AlgEquiv.apply_symm_apply, map_zero] at heq
    simp only [IsScalarTower.toAlgHom, AlgHom.coe_mk, Ideal.Quotient.algebraMap_eq] at heq
    rwa [Ideal.Quotient.eq_zero_iff_mem] at heq
  · intro h
    simp only [IsScalarTower.toAlgHom, AlgHom.coe_mk,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

noncomputable def evalTensorMap (φ : R →ₐ[k] k) : R ⊗[k] S →ₐ[k] S :=
  Algebra.TensorProduct.productMap ((Algebra.ofId k S).comp φ) (AlgHom.id k S)

omit [IsAlgClosed k] [IsDomain R] [Algebra.FiniteType k R] [IsDomain S] in
lemma coord_evalTensorMap {ι : Type*} (bS : Module.Basis ι k S) (φ : R →ₐ[k] k)
    (u : R ⊗[k] S) (i : ι) :
    bS.repr (evalTensorMap φ u) i = φ ((Algebra.TensorProduct.basisAux R bS u) i) := by
  induction u using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul r s =>
    have heval : evalTensorMap φ (r ⊗ₜ[k] s) = algebraMap k S (φ r) * s := by
      simp [evalTensorMap, Algebra.TensorProduct.productMap_apply_tmul, Algebra.ofId_apply]
    rw [heval, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [Algebra.TensorProduct.basisAux_tmul]
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply]
    rw [map_mul, AlgHom.commutes]; simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Helpers

section MainTheorem

variable {k : Type*} [Field k] [IsAlgClosed k]

theorem IsAffineAlgebra.tensorProduct (R S : Type*) [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [IsAffineAlgebra k R] [IsAffineAlgebra k S] :
    IsAffineAlgebra k (R ⊗[k] S) where
  finiteType :=


    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R)
      (Algebra.FiniteType.baseChange R)
  isDomain := by
    haveI : Nontrivial (R ⊗[k] S) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k R S
        (RingHom.injective _) (RingHom.injective _)
    haveI : NoZeroDivisors (R ⊗[k] S) := by
      constructor
      intro u v huv
      classical

      let bS := Module.Free.chooseBasis k S

      let B := Algebra.TensorProduct.basisAux R bS


      have key : ∀ (J : Ideal R) [J.IsMaximal],
          (∀ i, (B u) i ∈ J) ∨ (∀ i, (B v) i ∈ J) := by
        intro J hJ
        have h0 : evalTensorMap (algHomOfMaximalIdeal k J) (u * v) = 0 := by
          rw [huv, map_zero]
        rw [map_mul] at h0
        rcases mul_eq_zero.mp h0 with hhu | hhv
        · left; intro i
          have := congr_arg (bS.repr · i) hhu
          simp only [map_zero, Finsupp.zero_apply] at this
          rw [coord_evalTensorMap] at this
          exact (algHomOfMaximalIdeal_ker J _).mp this
        · right; intro i
          have := congr_arg (bS.repr · i) hhv
          simp only [map_zero, Finsupp.zero_apply] at this
          rw [coord_evalTensorMap] at this
          exact (algHomOfMaximalIdeal_ker J _).mp this


      haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
      have hjac : (⊥ : Ideal R).jacobson = ⊥ :=
        (inferInstance : IsJacobsonRing R).out Ideal.isRadical_bot_of_noZeroDivisors
      have hab_zero : ∀ i j, (B u) i * (B v) j = 0 := by
        intro i j
        have h_mem : (B u) i * (B v) j ∈ (⊥ : Ideal R).jacobson := by
          rw [Ideal.jacobson, Submodule.mem_sInf]
          intro J ⟨_, hJmax⟩
          rcases @key J hJmax with hu_sub | hv_sub
          · exact Ideal.mul_mem_right _ _ (hu_sub i)
          · exact Ideal.mul_mem_left _ _ (hv_sub j)
        rw [hjac, Ideal.mem_bot] at h_mem
        exact h_mem


      by_contra h
      push Not at h
      obtain ⟨hu, hv⟩ := h
      have hBu : B u ≠ 0 := fun h0 => hu (B.map_eq_zero_iff.mp h0)
      obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hBu
      simp only [Finsupp.zero_apply] at hi₀
      have hBv : B v = 0 := by
        ext j; simp only [Finsupp.zero_apply]
        exact (mul_eq_zero.mp (hab_zero i₀ j)).resolve_left hi₀
      exact hv (B.map_eq_zero_iff.mp hBv)
    exact NoZeroDivisors.to_isDomain (R ⊗[k] S)

end MainTheorem
