/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.HopfAlgebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.RepresentationTheory.FDRep

set_option maxHeartbeats 400000

open CategoryTheory Coalgebra HopfAlgebra LinearMap
open scoped TensorProduct

universe u v


section DualActionAlgebraic

variable {k : Type u} [CommSemiring k] {H : Type v} [Semiring H] [HopfAlgebra k H]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module H V] [SMulCommClass k H V]

/-- The `k`-linear map `v ↦ h • v` on a Hopf-algebra module `V`. -/
noncomputable def corollary_1_22_6_smul_map (h : H) : V →ₗ[k] V where
  toFun v := h • v
  map_add' := smul_add h
  map_smul' r v := by
    dsimp
    haveI : SMulCommClass H k V := SMulCommClass.symm k H V
    rw [smul_comm]

/-- The dual right action of `H` on `V*`: `a · f = f ∘ (S(a) • -)`, used to give the linear
dual the structure of a right `H`-module via the antipode. -/
noncomputable def corollary_1_22_6_right_dual_action (a : H) (f : Module.Dual k V) :
    Module.Dual k V :=
  f.comp (corollary_1_22_6_smul_map (k := k) (antipode k a))

/-- The dual right action of `1 ∈ H` is the identity on `V*`. -/
@[simp]
theorem corollary_1_22_6_right_dual_action_one (f : Module.Dual k V) :
    corollary_1_22_6_right_dual_action (k := k) (H := H) 1 f = f := by
  ext v
  simp [corollary_1_22_6_right_dual_action, corollary_1_22_6_smul_map]

/-- Multiplicativity of the dual right action: `(ab) · f = a · (b · f)`, using the
anti-multiplicativity of the antipode. -/
theorem corollary_1_22_6_right_dual_action_mul (a b : H) (f : Module.Dual k V) :
    corollary_1_22_6_right_dual_action (k := k) (a * b) f =
    corollary_1_22_6_right_dual_action (k := k) a
      (corollary_1_22_6_right_dual_action (k := k) b f) := by
  ext v
  simp only [corollary_1_22_6_right_dual_action, corollary_1_22_6_smul_map,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [HopfAlgebra.antipode_mul_anti]
  rw [mul_smul]

/-- Additivity of the dual right action in the algebra argument: `(a + b) · f = a · f + b · f`. -/
theorem corollary_1_22_6_right_dual_action_add (a b : H) (f : Module.Dual k V) :
    corollary_1_22_6_right_dual_action (k := k) (a + b) f =
    corollary_1_22_6_right_dual_action (k := k) a f +
    corollary_1_22_6_right_dual_action (k := k) b f := by
  ext v
  simp only [corollary_1_22_6_right_dual_action, corollary_1_22_6_smul_map,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
    map_add, add_smul]

end DualActionAlgebraic


section CategoricalStatements



/-- Instance specialization of Corollary 1.22.6 (i) to the group case: `FDRep(k, G)` is
right rigid. -/
noncomputable instance corollary_1_22_6_right_rigid_group
    (k G : Type u) [Field k] [Group G] :
    RightRigidCategory (FDRep k G) :=
  inferInstance

/-- Instance specialization of Corollary 1.22.6 (ii) to the group case: `FDRep(k, G)` is
rigid. -/
noncomputable instance corollary_1_22_6_rigid_group
    (k G : Type u) [Field k] [Group G] :
    RigidCategory (FDRep k G) :=
  inferInstance

end CategoricalStatements
