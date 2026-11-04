/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.PicardGroup

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

noncomputable section

namespace Corollary19










section AffineCase

variable (R : Type u) [CommRing R]

/-- The Picard group of a commutative ring is naturally a commutative
group. -/
instance picardGroup_affine_commGroup : CommGroup (CommRing.Pic R) := inferInstance


end AffineCase

/-- Multiplication in `Pic R` corresponds to tensor product of invertible
modules. -/
theorem pic_mul_eq_tensor {R : Type u} [CommSemiring R]
    {M N : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M]
    [AddCommMonoid N] [Module R N] [Module.Invertible R N] :
    CommRing.Pic.mk R (M ⊗[R] N) = CommRing.Pic.mk R M * CommRing.Pic.mk R N :=
  CommRing.Pic.mk_tensor

/-- The trivial line bundle `R` represents the identity in `Pic R`. -/
theorem pic_identity {R : Type u} [CommSemiring R] :
    CommRing.Pic.mk R R = 1 :=
  CommRing.Pic.mk_self

/-- The inverse of a Picard class is represented by the dual module. -/
theorem pic_inv_eq_dual {R : Type u} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M] :
    CommRing.Pic.mk R (Module.Dual R M) = (CommRing.Pic.mk R M)⁻¹ :=
  CommRing.Pic.mk_dual

/-- Commutativity of multiplication in `Pic R`. -/
theorem pic_comm {R : Type u} [CommSemiring R]
    (a b : CommRing.Pic R) : a * b = b * a :=
  mul_comm a b

/-- Two invertible modules represent the same Picard class iff they are
isomorphic as `R`-modules. -/
theorem pic_eq_iff_iso {R : Type u} [CommSemiring R]
    {M N : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M]
    [AddCommMonoid N] [Module R N] [Module.Invertible R N] :
    CommRing.Pic.mk R M = CommRing.Pic.mk R N ↔ Nonempty (M ≃ₗ[R] N) :=
  CommRing.Pic.mk_eq_mk_iff

/-- A Picard class is trivial iff the underlying invertible module is free. -/
theorem pic_trivial_iff_free {R : Type u} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M] :
    CommRing.Pic.mk R M = 1 ↔ Module.Free R M :=
  CommRing.Pic.mk_eq_one_iff_free

end Corollary19

end
