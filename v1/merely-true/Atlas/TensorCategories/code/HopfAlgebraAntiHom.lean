/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.HopfAlgebra

set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra LinearMap
open scoped TensorProduct

universe u v


section Corollary_1_22_6_Prerequisites

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

end Corollary_1_22_6_Prerequisites


section Corollary_1_22_6_RightDual

variable {k : Type u} [CommSemiring k] {H : Type v} [Semiring H] [HopfAlgebra k H]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module H V] [SMulCommClass k H V]

/-- `k`-linear map given by scalar multiplication by an element `h : H`. -/
noncomputable def Corollary_1_22_6_smul_map (h : H) : V →ₗ[k] V where
  toFun v := h • v
  map_add' := smul_add h
  map_smul' r v := by
    dsimp
    haveI : SMulCommClass H k V := SMulCommClass.symm k H V
    rw [smul_comm]

/-- The right-dual `H`-action on `V^*` from Corollary 1.22.6: `(a · f)(v) = f(S(a) · v)`. -/
noncomputable def Corollary_1_22_6_right_dual_action (a : H) (f : Module.Dual k V) :
    Module.Dual k V :=
  f.comp (Corollary_1_22_6_smul_map (k := k) (antipode k a))

/-- The unit of `H` acts trivially on the right-dual action. -/
@[simp]
theorem Corollary_1_22_6_right_dual_action_one (f : Module.Dual k V) :
    Corollary_1_22_6_right_dual_action (k := k) (H := H) 1 f = f := by
  ext v
  simp [Corollary_1_22_6_right_dual_action, Corollary_1_22_6_smul_map]

/-- The right-dual action satisfies the multiplicative law `(ab) · f = a · (b · f)`, using
that the antipode is an antihomomorphism of algebras. -/
theorem Corollary_1_22_6_right_dual_action_mul (a b : H) (f : Module.Dual k V) :
    Corollary_1_22_6_right_dual_action (k := k) (a * b) f =
    Corollary_1_22_6_right_dual_action (k := k) a
      (Corollary_1_22_6_right_dual_action (k := k) b f) := by
  ext v
  simp only [Corollary_1_22_6_right_dual_action, Corollary_1_22_6_smul_map,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [HopfAlgebra.antipode_mul_anti]
  rw [mul_smul]

/-- The right-dual action is additive in the acting element. -/
theorem Corollary_1_22_6_right_dual_action_add (a b : H) (f : Module.Dual k V) :
    Corollary_1_22_6_right_dual_action (k := k) (a + b) f =
    Corollary_1_22_6_right_dual_action (k := k) a f +
    Corollary_1_22_6_right_dual_action (k := k) b f := by
  ext v
  simp only [Corollary_1_22_6_right_dual_action, Corollary_1_22_6_smul_map,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
    map_add, add_smul]

end Corollary_1_22_6_RightDual
