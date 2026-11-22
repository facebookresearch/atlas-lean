/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.SweedlerConcrete
import Atlas.TensorCategories.code.HopfAlgebraExamples

set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]

namespace SweedlerH4

/-- Every element of `SweedlerH4 k` is the sum of its coefficients times the standard basis
vectors `e i`. -/
lemma eq_sum_basis (a : SweedlerH4 k) : a = ∑ i : Fin 4, a.coeff i • e i := by
  ext m
  rw [show ∑ i : Fin 4, a.coeff i • e i =
    a.coeff 0 • e 0 + a.coeff 1 • e 1 + a.coeff 2 • e 2 + a.coeff 3 • (e 3 : SweedlerH4 k)
    from Fin.sum_univ_four _]
  simp only [coeff_add, coeff_smul, coeff_e]
  fin_cases m <;> simp

/-- Two `k`-linear maps out of `SweedlerH4 k` agree as soon as they agree on each of the four
basis vectors `e i`. -/
lemma linearMap_ext_basis {M : Type*} [AddCommMonoid M] [Module k M]
    {f g : SweedlerH4 k →ₗ[k] M} (h : ∀ i : Fin 4, f (e i) = g (e i)) :
    f = g := by
  ext a; rw [eq_sum_basis a]; simp_rw [map_sum, map_smul]
  congr 1; ext i; rw [h i]

/-- Build a `k`-linear map `SweedlerH4 k →ₗ[k] M` by prescribing its values on the four basis
vectors `e 0, e 1, e 2, e 3`. -/
noncomputable def lmOfBasis {M : Type*} [AddCommMonoid M] [Module k M]
    (v : Fin 4 → M) : SweedlerH4 k →ₗ[k] M where
  toFun a := ∑ i : Fin 4, a.coeff i • v i
  map_add' a b := by simp [coeff_add, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp [coeff_smul, smul_eq_mul, Finset.smul_sum, smul_smul]

/-- A linear map built via `lmOfBasis` evaluates to its prescribed value on each basis vector. -/
@[simp] lemma lmOfBasis_e {M : Type*} [AddCommMonoid M] [Module k M]
    (v : Fin 4 → M) (i : Fin 4) : lmOfBasis v (e i : SweedlerH4 k) = v i := by
  simp only [lmOfBasis, LinearMap.coe_mk, AddHom.coe_mk, coeff_e, Fin4_sum]
  fin_cases i <;> simp

/-- The counit of `H₄` as a `k`-linear map: `1 ↦ 1`, `g ↦ 1`, `x ↦ 0`, `gx ↦ 0`. -/
noncomputable def counitLM : SweedlerH4 k →ₗ[k] k := lmOfBasis ![1, 1, 0, 0]

/-- The counit evaluates on basis vectors according to the tuple `![1, 1, 0, 0]`. -/
@[simp] lemma counitLM_e (i : Fin 4) :
    counitLM (e i : SweedlerH4 k) = ![1, 1, 0, 0] i := by simp [counitLM]

/-- Counit value on `e 0`: `ε(1) = 1`. -/
@[simp] lemma counitLM_e0 : counitLM (e 0 : SweedlerH4 k) = 1 := by simp [counitLM]
/-- Counit value on `e 1 = g`: `ε(g) = 1`. -/
@[simp] lemma counitLM_e1 : counitLM (e 1 : SweedlerH4 k) = 1 := by simp [counitLM]
/-- Counit value on `e 2 = x`: `ε(x) = 0`. -/
@[simp] lemma counitLM_e2 : counitLM (e 2 : SweedlerH4 k) = 0 := by simp [counitLM]
/-- Counit value on `e 3 = gx`: `ε(gx) = 0`. -/
@[simp] lemma counitLM_e3 : counitLM (e 3 : SweedlerH4 k) = 0 := by simp [counitLM]
/-- Counit preserves the unit: `ε(1) = 1`. -/
@[simp] lemma counitLM_one : counitLM (1 : SweedlerH4 k) = 1 := by
  rw [← e_zero_eq_one]; exact counitLM_e0

/-- The comultiplication of `H₄` as a `k`-linear map: `1 ↦ 1 ⊗ 1`, `g ↦ g ⊗ g`,
`x ↦ x ⊗ g + 1 ⊗ x`, `gx ↦ gx ⊗ 1 + g ⊗ gx`. -/
noncomputable def comulLM : SweedlerH4 k →ₗ[k] SweedlerH4 k ⊗[k] SweedlerH4 k :=
  lmOfBasis ![
    e 0 ⊗ₜ e 0,
    e 1 ⊗ₜ e 1,
    e 2 ⊗ₜ e 1 + e 0 ⊗ₜ e 2,
    e 3 ⊗ₜ e 0 + e 1 ⊗ₜ e 3
  ]

/-- Comultiplication value on `e 0 = 1`: `Δ(1) = 1 ⊗ 1`. -/
@[simp] lemma comulLM_e0 : comulLM (e 0 : SweedlerH4 k) = e 0 ⊗ₜ e 0 := by simp [comulLM]
/-- Comultiplication value on `e 1 = g`: `Δ(g) = g ⊗ g`, exhibiting `g` as grouplike. -/
@[simp] lemma comulLM_e1 : comulLM (e 1 : SweedlerH4 k) = e 1 ⊗ₜ e 1 := by simp [comulLM]
/-- Comultiplication value on `e 2 = x`: `Δ(x) = x ⊗ g + 1 ⊗ x`, exhibiting `x` as
`(g, 1)`-skew-primitive. -/
@[simp] lemma comulLM_e2 :
    comulLM (e 2 : SweedlerH4 k) = e 2 ⊗ₜ e 1 + e 0 ⊗ₜ e 2 := by simp [comulLM]
/-- Comultiplication value on `e 3 = gx`: `Δ(gx) = gx ⊗ 1 + g ⊗ gx`. -/
@[simp] lemma comulLM_e3 :
    comulLM (e 3 : SweedlerH4 k) = e 3 ⊗ₜ e 0 + e 1 ⊗ₜ e 3 := by simp [comulLM]
/-- Comultiplication preserves the unit: `Δ(1) = 1 ⊗ 1`. -/
@[simp] lemma comulLM_one : comulLM (1 : SweedlerH4 k) = e 0 ⊗ₜ e 0 := by
  rw [← e_zero_eq_one]; exact comulLM_e0

/-- The antipode of `H₄` as a `k`-linear map: `1 ↦ 1`, `g ↦ g`, `x ↦ gx`, `gx ↦ -x`. -/
noncomputable def antipodeLM : SweedlerH4 k →ₗ[k] SweedlerH4 k :=
  lmOfBasis ![e 0, e 1, e 3, -(e 2)]

/-- Antipode value on `e 0 = 1`: `S(1) = 1`. -/
@[simp] lemma antipodeLM_e0 : antipodeLM (e 0 : SweedlerH4 k) = e 0 := by simp [antipodeLM]
/-- Antipode preserves the unit: `S(1) = 1`. -/
@[simp] lemma antipodeLM_one : antipodeLM (1 : SweedlerH4 k) = 1 := by
  rw [← e_zero_eq_one]; simp [antipodeLM]
/-- Antipode value on `e 1 = g`: `S(g) = g = g⁻¹`. -/
@[simp] lemma antipodeLM_e1 : antipodeLM (e 1 : SweedlerH4 k) = e 1 := by simp [antipodeLM]
/-- Antipode value on `e 2 = x`: `S(x) = gx`. -/
@[simp] lemma antipodeLM_e2 : antipodeLM (e 2 : SweedlerH4 k) = e 3 := by simp [antipodeLM]
/-- Antipode value on `e 3 = gx`: `S(gx) = -x`. -/
@[simp] lemma antipodeLM_e3 : antipodeLM (e 3 : SweedlerH4 k) = -(e 2) := by simp [antipodeLM]

/-- Left multiplication by `e 0 = 1` is the identity. -/
@[simp] lemma e0_mul (a : SweedlerH4 k) : e 0 * a = a := by rw [e_zero_eq_one, one_mul]
/-- Right multiplication by `e 0 = 1` is the identity. -/
@[simp] lemma mul_e0 (a : SweedlerH4 k) : a * e 0 = a := by rw [e_zero_eq_one, mul_one]

/-- Basis multiplication: `g · g = 1`. -/
lemma e1_mul_e1 : (e 1 : SweedlerH4 k) * e 1 = e 0 := by
  rw [show e 1 = (gen_g : SweedlerH4 k) from rfl, gen_g_sq, e_zero_eq_one]

/-- Basis multiplication: `g · x = gx`. -/
lemma e1_mul_e2 : (e 1 : SweedlerH4 k) * e 2 = e 3 := by
  rw [show e 1 = (gen_g : SweedlerH4 k) from rfl,
      show e 2 = (gen_x : SweedlerH4 k) from rfl]
  exact gen_g_mul_x

/-- Basis multiplication: `g · gx = x` (using `g² = 1`). -/
lemma e1_mul_e3 : (e 1 : SweedlerH4 k) * e 3 = e 2 := by
  ext m; simp only [coeff_mul, coeff_e, Fin4_sum, basisMul]; fin_cases m <;> simp

/-- Basis multiplication: `x · g = -gx`, expressing the anti-commutation `gx = -xg`. -/
lemma e2_mul_e1 : (e 2 : SweedlerH4 k) * e 1 = -(e 3) := by
  ext m; simp only [coeff_mul, coeff_e, coeff_neg, Fin4_sum, basisMul]; fin_cases m <;> simp

/-- Basis multiplication: `gx · g = -x`. -/
lemma e3_mul_e1 : (e 3 : SweedlerH4 k) * e 1 = -(e 2) := by
  ext m; simp only [coeff_mul, coeff_e, coeff_neg, Fin4_sum, basisMul]; fin_cases m <;> simp

/-- Basis multiplication: `x · x = 0` (nilpotency of `x`). -/
lemma e2_mul_e2 : (e 2 : SweedlerH4 k) * e 2 = 0 := gen_x_sq
/-- Basis multiplication: `x · gx = 0`. -/
lemma e2_mul_e3 : (e 2 : SweedlerH4 k) * e 3 = 0 := by
  ext m; simp only [coeff_mul, coeff_e, coeff_zero', Fin4_sum, basisMul]; fin_cases m <;> simp
/-- Basis multiplication: `gx · x = 0`. -/
lemma e3_mul_e2 : (e 3 : SweedlerH4 k) * e 2 = 0 := by
  ext m; simp only [coeff_mul, coeff_e, coeff_zero', Fin4_sum, basisMul]; fin_cases m <;> simp
/-- Basis multiplication: `(gx)² = 0`. -/
lemma e3_mul_e3 : (e 3 : SweedlerH4 k) * e 3 = 0 := by
  ext m; simp only [coeff_mul, coeff_e, coeff_zero', Fin4_sum, basisMul]; fin_cases m <;> simp


set_option maxHeartbeats 800000 in
/-- The counit is multiplicative on pairs of basis vectors, verified case-by-case. -/
lemma counitLM_mul_basis (i j : Fin 4) :
    counitLM ((e i : SweedlerH4 k) * e j) = counitLM (e i) * counitLM (e j) := by
  fin_cases i <;> fin_cases j <;>
    simp [e_zero_eq_one, e1_mul_e1, e1_mul_e2, e1_mul_e3, e2_mul_e1,
      e2_mul_e2, e2_mul_e3, e3_mul_e1, e3_mul_e2, e3_mul_e3]


/-- The counit is multiplicative on arbitrary elements, by bilinear extension of
`counitLM_mul_basis`. -/
lemma counitLM_mul (a b : SweedlerH4 k) :
    counitLM (a * b : SweedlerH4 k) = counitLM a * counitLM b := by
  conv_lhs => rw [eq_sum_basis a, eq_sum_basis b]
  conv_rhs => rw [eq_sum_basis a, eq_sum_basis b]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, map_smul, smul_eq_mul,
    smul_mul_smul_comm]
  congr 1; ext i; congr 1; ext j
  rw [counitLM_mul_basis]; ring


/-- The unit in `SweedlerH4 k ⊗[k] SweedlerH4 k` is `e 0 ⊗ e 0`. -/
lemma one_tensor_eq : (1 : SweedlerH4 k ⊗[k] SweedlerH4 k) = e 0 ⊗ₜ e 0 := by
  rw [Algebra.TensorProduct.one_def, e_zero_eq_one]


/-- Multiplicativity of `Δ` on the `(e 0, e j)` cases. -/
lemma comulLM_mul_e0j (j : Fin 4) :
    comulLM ((e 0 : SweedlerH4 k) * e j) = comulLM (e 0) * comulLM (e j) := by
  simp only [e0_mul, comulLM_e0, ← one_tensor_eq, one_mul]

/-- Multiplicativity of `Δ` on the `(e i, e 0)` cases. -/
lemma comulLM_mul_ei0 (i : Fin 4) :
    comulLM ((e i : SweedlerH4 k) * e 0) = comulLM (e i) * comulLM (e 0) := by
  simp only [mul_e0, comulLM_e0, ← one_tensor_eq, mul_one]

set_option maxHeartbeats 800000 in
/-- Multiplicativity of `Δ` on `g · g`. -/
lemma comulLM_mul_e11 :
    comulLM ((e 1 : SweedlerH4 k) * e 1) = comulLM (e 1) * comulLM (e 1) := by
  simp [e1_mul_e1, e_zero_eq_one, Algebra.TensorProduct.tmul_mul_tmul]

set_option maxHeartbeats 800000 in
/-- Multiplicativity of `Δ` on `g · x`. -/
lemma comulLM_mul_e12 :
    comulLM ((e 1 : SweedlerH4 k) * e 2) = comulLM (e 1) * comulLM (e 2) := by
  simp only [e1_mul_e2, comulLM_e3, comulLM_e1, comulLM_e2, comulLM_e0, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, e1_mul_e1, e_zero_eq_one,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, mul_one, one_mul]

set_option maxHeartbeats 800000 in
/-- Multiplicativity of `Δ` on `g · gx`. -/
lemma comulLM_mul_e13 :
    comulLM ((e 1 : SweedlerH4 k) * e 3) = comulLM (e 1) * comulLM (e 3) := by
  simp only [e1_mul_e3, comulLM_e2, comulLM_e1, comulLM_e3, comulLM_e0, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, e1_mul_e1, e_zero_eq_one,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, mul_one, one_mul]

set_option maxHeartbeats 800000 in
/-- Multiplicativity of `Δ` on `x · g`. -/
lemma comulLM_mul_e21 :
    comulLM ((e 2 : SweedlerH4 k) * e 1) = comulLM (e 2) * comulLM (e 1) := by
  simp only [e2_mul_e1, map_neg, comulLM_e3, comulLM_e2, comulLM_e1, comulLM_e0, add_mul,
    Algebra.TensorProduct.tmul_mul_tmul, e2_mul_e1, e1_mul_e1, e_zero_eq_one,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, mul_one, one_mul]
  abel


set_option maxHeartbeats 800000 in
/-- Multiplicativity of `Δ` on `x · gx`. -/
lemma comulLM_mul_e23 :
    comulLM ((e 2 : SweedlerH4 k) * e 3) = comulLM (e 2) * comulLM (e 3) := by
  simp only [e2_mul_e3, map_zero, comulLM_e2, comulLM_e0, comulLM_e1, comulLM_e3,
    add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    e2_mul_e1, e2_mul_e2, e2_mul_e3, e1_mul_e3,
    e_zero_eq_one, TensorProduct.tmul_zero, TensorProduct.zero_tmul,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, add_zero, zero_add,
    neg_add_cancel, add_neg_cancel, neg_zero, mul_one, one_mul]

set_option maxHeartbeats 800000 in
/-- Multiplicativity of `Δ` on `gx · g`. -/
lemma comulLM_mul_e31 :
    comulLM ((e 3 : SweedlerH4 k) * e 1) = comulLM (e 3) * comulLM (e 1) := by
  simp only [e3_mul_e1, map_neg, comulLM_e2, comulLM_e3, comulLM_e0, comulLM_e1,
    add_mul, Algebra.TensorProduct.tmul_mul_tmul,
    e3_mul_e1, e1_mul_e1, e_zero_eq_one,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, mul_one, one_mul]
  abel

set_option maxHeartbeats 800000 in
/-- Multiplicativity of `Δ` on `gx · x`. -/
lemma comulLM_mul_e32 :
    comulLM ((e 3 : SweedlerH4 k) * e 2) = comulLM (e 3) * comulLM (e 2) := by
  simp only [e3_mul_e2, map_zero, comulLM_e3, comulLM_e0, comulLM_e1, comulLM_e2,
    add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    e3_mul_e1, e3_mul_e2, e1_mul_e2,
    e_zero_eq_one, TensorProduct.tmul_zero, TensorProduct.zero_tmul,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, add_zero, zero_add,
    neg_add_cancel, add_neg_cancel, neg_zero, mul_one, one_mul]

set_option maxHeartbeats 800000 in
/-- Multiplicativity of `Δ` on `gx · gx`. -/
lemma comulLM_mul_e33 :
    comulLM ((e 3 : SweedlerH4 k) * e 3) = comulLM (e 3) * comulLM (e 3) := by
  simp only [e3_mul_e3, map_zero, comulLM_e3, comulLM_e0, comulLM_e1, comulLM_e2,
    add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    e3_mul_e1, e1_mul_e3, e3_mul_e3, e3_mul_e2,
    e_zero_eq_one, TensorProduct.tmul_zero, TensorProduct.zero_tmul,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, add_zero, zero_add,
    neg_add_cancel, add_neg_cancel, neg_zero, mul_one, one_mul]




set_option maxHeartbeats 800000 in

/-- The `k`-coalgebra structure on `SweedlerH4 k`, packaged from `comulLM` and `counitLM`. -/
noncomputable instance : CoalgebraStruct k (SweedlerH4 k) where
  comul := comulLM
  counit := counitLM

/-- The coalgebra-structure comultiplication unfolds to `comulLM`. -/
@[simp] lemma comul_is : (CoalgebraStruct.comul : SweedlerH4 k →ₗ[k] _) = comulLM := rfl
/-- The coalgebra-structure counit unfolds to `counitLM`. -/
@[simp] lemma counit_is : (CoalgebraStruct.counit : SweedlerH4 k →ₗ[k] k) = counitLM := rfl

set_option maxHeartbeats 800000 in
/-- The full `k`-coalgebra structure on `SweedlerH4 k`, verifying coassociativity and the
counit axioms on the basis. -/
noncomputable instance : Coalgebra k (SweedlerH4 k) where
  coassoc := by
    apply linearMap_ext_basis; intro i
    simp only [LinearMap.comp_apply, comul_is]
    fin_cases i <;>
      simp [map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.assoc_tmul, TensorProduct.add_tmul, TensorProduct.tmul_add,
        add_assoc]
  rTensor_counit_comp_comul := by
    apply linearMap_ext_basis; intro i
    simp only [LinearMap.comp_apply, comul_is, counit_is]
    fin_cases i <;>
      simp [map_add, LinearMap.rTensor_tmul, TensorProduct.mk_apply]
  lTensor_counit_comp_comul := by
    apply linearMap_ext_basis; intro i
    simp only [LinearMap.comp_apply, comul_is, counit_is]
    fin_cases i <;>
      simp [map_add, LinearMap.lTensor_tmul,
        TensorProduct.mk_apply, LinearMap.flip_apply]







/-- The generator `g` is grouplike: `Δ(g) = g ⊗ g`. -/
lemma comul_gen_g :
    (Coalgebra.comul (R := k)) (gen_g : SweedlerH4 k) =
      (gen_g : SweedlerH4 k) ⊗ₜ gen_g := by
  show comulLM (e 1 : SweedlerH4 k) = e 1 ⊗ₜ e 1; simp

/-- The generator `x` is `(g, 1)`-skew-primitive: `Δ(x) = x ⊗ g + 1 ⊗ x`. -/
lemma comul_gen_x :
    (Coalgebra.comul (R := k)) (gen_x : SweedlerH4 k) =
      (gen_x : SweedlerH4 k) ⊗ₜ gen_g + (1 : SweedlerH4 k) ⊗ₜ gen_x := by
  show comulLM (e 2 : SweedlerH4 k) =
    (e 2 : SweedlerH4 k) ⊗ₜ e 1 + (1 : SweedlerH4 k) ⊗ₜ e 2
  rw [← e_zero_eq_one]; simp

/-- Counit value `ε(g) = 1`. -/
lemma counit_gen_g :
    (Coalgebra.counit (R := k)) (gen_g : SweedlerH4 k) = (1 : k) := by
  show counitLM (e 1 : SweedlerH4 k) = 1; simp

/-- Counit value `ε(x) = 0`. -/
lemma counit_gen_x :
    (Coalgebra.counit (R := k)) (gen_x : SweedlerH4 k) = (0 : k) := by
  show counitLM (e 2 : SweedlerH4 k) = 0; simp




end SweedlerH4
