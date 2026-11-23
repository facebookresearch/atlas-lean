/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.PicardGroup

open TensorProduct

universe u

namespace InvertibleSheaves

/-- For an invertible module M over R, the natural evaluation M^∨ ⊗ M → R is an
isomorphism, witnessing M as a unit in the Picard group. -/
theorem dual_tensor_self_equiv (R : Type u) [CommSemiring R]
    (M : Type*) [AddCommMonoid M] [Module R M] [Module.Invertible R M] :
    Nonempty (Module.Dual R M ⊗[R] M ≃ₗ[R] R) :=
  ⟨Module.Invertible.linearEquiv R M⟩

/-- The tensor product of two invertible modules is invertible (Pic is closed under
multiplication). -/
instance invertible_tensor (R : Type u) [CommSemiring R]
    (M : Type*) [AddCommMonoid M] [Module R M] [Module.Invertible R M]
    (N : Type*) [AddCommMonoid N] [Module R N] [Module.Invertible R N] :
    Module.Invertible R (M ⊗[R] N) := inferInstance

/-- The dual of an invertible module is invertible: this gives inverses in Pic. -/
instance invertible_dual (R : Type u) [CommSemiring R]
    (M : Type*) [AddCommMonoid M] [Module R M] [Module.Invertible R M] :
    Module.Invertible R (Module.Dual R M) := inferInstance

/-- R itself is invertible as an R-module, serving as the identity element of Pic. -/
instance invertible_self (R : Type u) [CommSemiring R] :
    Module.Invertible R R := inferInstance

/-- The Picard group of R is a commutative group under tensor product
(Corollary 19, Lecture 14/15). -/
noncomputable instance picardGroup_commGroup (R : Type u) [CommSemiring R] :
    CommGroup (CommRing.Pic R) := inferInstance

/-- Multiplication in the Picard group is given by tensor product of invertible
modules. -/
theorem pic_mul_eq_tensor {R : Type u} [CommSemiring R]
    {M N : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M]
    [AddCommMonoid N] [Module R N] [Module.Invertible R N] :
    CommRing.Pic.mk R (M ⊗[R] N) = CommRing.Pic.mk R M * CommRing.Pic.mk R N :=
  CommRing.Pic.mk_tensor

/-- The class of R is the identity element 1 of Pic(R). -/
theorem pic_identity {R : Type u} [CommSemiring R] :
    CommRing.Pic.mk R R = 1 :=
  CommRing.Pic.mk_self

/-- The inverse in Pic of the class of M is the class of its dual M^∨. -/
theorem pic_inv_eq_dual {R : Type u} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M] :
    CommRing.Pic.mk R (Module.Dual R M) = (CommRing.Pic.mk R M)⁻¹ :=
  CommRing.Pic.mk_dual

/-- Commutativity of Pic: the group law (tensor product) is commutative. -/
theorem pic_comm {R : Type u} [CommSemiring R]
    (a b : CommRing.Pic R) : a * b = b * a :=
  mul_comm a b

/-- Two invertible modules represent the same Pic class iff they are linearly
isomorphic. -/
theorem pic_eq_iff_iso {R : Type u} [CommSemiring R]
    {M N : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M]
    [AddCommMonoid N] [Module R N] [Module.Invertible R N] :
    CommRing.Pic.mk R M = CommRing.Pic.mk R N ↔ Nonempty (M ≃ₗ[R] N) :=
  CommRing.Pic.mk_eq_mk_iff

/-- An invertible module is trivial in Pic iff it is free as an R-module. -/
theorem pic_trivial_iff_free {R : Type u} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M] :
    CommRing.Pic.mk R M = 1 ↔ Module.Free R M :=
  CommRing.Pic.mk_eq_one_iff_free

end InvertibleSheaves
