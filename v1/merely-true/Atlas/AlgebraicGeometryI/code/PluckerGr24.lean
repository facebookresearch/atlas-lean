/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Atlas.AlgebraicGeometryI.code.Lec4Grassmannian
import Atlas.AlgebraicGeometryI.code.GrassmannianProjective

open ExteriorAlgebra

namespace PluckerGr24

section Anticommutativity

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Anticommutativity in the exterior algebra: for x, y in M, ι(x) ι(y) = -ι(y) ι(x). -/
theorem ι_anticomm (x y : M) :
    (ι R (M := M)) x * (ι R) y = -((ι R) y * (ι R (M := M)) x) := by
  have h := @ι_add_mul_swap R _ M _ _ y x
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

end Anticommutativity

section ForwardDirection

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A decomposable 2-vector v_1 ∧ v_2 satisfies (v_1 ∧ v_2)^2 = 0 in the exterior
algebra (Plücker forward direction). -/
theorem wedge_sq_zero_of_decomposable (v₁ v₂ : M) :
    (ι R v₁ * ι R v₂) * (ι R v₁ * ι R v₂) = (0 : ExteriorAlgebra R M) := by
  have anticomm : ι R v₂ * ι R v₁ = -((ι R (M := M)) v₁ * ι R v₂) := by
    have h := @ι_add_mul_swap R _ M _ _ v₁ v₂
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [mul_assoc, ← mul_assoc (ι R v₂) (ι R v₁) (ι R v₂)]
  rw [anticomm]
  rw [neg_mul, mul_neg, mul_assoc, ← mul_assoc (ι R v₁) (ι R v₁)]
  rw [ι_sq_zero, zero_mul, neg_zero]

/-- A 2-vector ω is decomposable if it can be written as v_1 ∧ v_2 for some vectors. -/
def IsDecomposable2 (ω : ExteriorAlgebra R M) : Prop :=
  ∃ v₁ v₂ : M, ω = ι R v₁ * ι R v₂

/-- Every decomposable 2-vector squares to zero in the exterior algebra. -/
theorem wedge_sq_zero_of_isDecomposable2 {ω : ExteriorAlgebra R M} (h : IsDecomposable2 ω) :
    ω * ω = 0 := by
  obtain ⟨v₁, v₂, rfl⟩ := h
  exact wedge_sq_zero_of_decomposable v₁ v₂

end ForwardDirection

section GradedCommutativity

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Graded commutativity for products of two pairs: (a∧b)(c∧d) = (c∧d)(a∧b) since
even-degree elements commute in the exterior algebra. -/
theorem ι_pair_comm (a b c d : M) :
    (ι R a * ι R b) * (ι R c * ι R d) = (ι R c * ι R d) * ((ι R (M := M)) a * ι R b) := by
  have hAC := ι_anticomm (R := R) a c
  have hBC := ι_anticomm (R := R) b c
  have hBD := ι_anticomm (R := R) b d
  have hAD := ι_anticomm (R := R) a d
  calc (ι R a * ι R b) * (ι R c * ι R d)
      = ι R a * (ι R b * ι R c) * ι R d := by rw [mul_assoc, mul_assoc, mul_assoc]
    _ = ι R a * (-(ι R c * ι R b)) * ι R d := by rw [hBC]
    _ = -(ι R a * (ι R c * ι R b) * ι R d) := by rw [mul_neg, neg_mul]
    _ = -((ι R a * ι R c) * ι R b * ι R d) := by rw [mul_assoc (ι R a) (ι R c)]
    _ = -((-(ι R c * ι R a)) * ι R b * ι R d) := by rw [hAC]
    _ = (ι R c * ι R a) * ι R b * ι R d := by simp [neg_mul, neg_neg]
    _ = ι R c * (ι R a * (ι R b * ι R d)) := by rw [mul_assoc, mul_assoc]
    _ = ι R c * (ι R a * (-(ι R d * ι R b))) := by rw [hBD]
    _ = -(ι R c * (ι R a * (ι R d * ι R b))) := by rw [mul_neg, mul_neg]
    _ = -(ι R c * ((ι R a * ι R d) * ι R b)) := by rw [mul_assoc (ι R a)]
    _ = -(ι R c * ((-(ι R d * ι R a)) * ι R b)) := by rw [hAD]
    _ = ι R c * (ι R d * ι R a * ι R b) := by simp [neg_mul, mul_neg, neg_neg]
    _ = ι R c * (ι R d * (ι R a * ι R b)) := by rw [mul_assoc (ι R d)]
    _ = ι R c * ι R d * (ι R a * ι R b) := by rw [mul_assoc]

/-- For a sum of two decomposable 2-vectors, the square equals 2 (v_1∧v_2) (v_3∧v_4). -/
theorem wedge_sq_sum_decomposable (v₁ v₂ v₃ v₄ : M) :
    (ι R v₁ * ι R v₂ + ι R v₃ * ι R v₄) * (ι R v₁ * ι R v₂ + ι R v₃ * ι R v₄)
    = 2 * ((ι R (M := M)) v₁ * ι R v₂ * (ι R v₃ * ι R v₄)) := by
  rw [add_mul, mul_add, mul_add]
  rw [wedge_sq_zero_of_decomposable v₁ v₂, wedge_sq_zero_of_decomposable v₃ v₄]
  rw [zero_add, add_zero]
  rw [ι_pair_comm v₁ v₂ v₃ v₄]
  rw [two_mul]

end GradedCommutativity

section DimensionCount

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
  [Module.Free k V] [Module.Finite k V]

/-- For a 4-dimensional vector space V, ⋀²V has dimension 6 = C(4,2), giving the
ambient P^5 for the Plücker embedding of Gr(2,4). -/
theorem exteriorPower_two_finrank_of_four
    (hdim : Module.finrank k V = 4) :
    Module.finrank k (⋀[k]^2 V) = 6 := by
  rw [exteriorPower.finrank_eq, hdim]
  decide

/-- General dimension formula: dim ⋀^n V = C(dim V, n). -/
theorem exteriorPower_finrank :
    Module.finrank k (⋀[k]^(n : ℕ) V) = Nat.choose (Module.finrank k V) n := by
  rw [exteriorPower.finrank_eq]

/-- For a 4-dimensional vector space V, ⋀⁴V is 1-dimensional. -/
theorem exteriorPower_four_finrank_of_four
    (hdim : Module.finrank k V = 4) :
    Module.finrank k (⋀[k]^4 V) = 1 := by
  rw [exteriorPower.finrank_eq, hdim]
  decide

end DimensionCount

section PluckerConverse

variable {k : Type*} [Field k]

/-- Forward Plücker relation in k^4: decomposable 2-vectors square to zero. -/
theorem decomposable_iff_wedge_sq_zero_forward (ω : ExteriorAlgebra k (Fin 4 → k))
    (hω : IsDecomposable2 ω) : ω * ω = 0 :=
  wedge_sq_zero_of_isDecomposable2 hω


/-- The product e_0 ∧ e_1 ∧ e_2 ∧ e_3 of the four standard basis vectors equals the
top wedge ιMulti(e_0, e_1, e_2, e_3). -/
theorem product_basis_eq_ιMulti :
    ι k (Pi.single 0 1 : Fin 4 → k) * ι k (Pi.single 1 1) *
      (ι k (Pi.single 2 1) * ι k (Pi.single 3 1)) =
    ExteriorAlgebra.ιMulti k 4 (Pi.basisFun k (Fin 4) : Fin 4 → Fin 4 → k) := by
  simp only [ιMulti_apply, List.ofFn_succ, Fin.isValue, List.prod_cons]
  simp [List.ofFn_zero]
  rw [mul_assoc]

variable [CharZero k]


end PluckerConverse

section Converse

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  [Module.Free k V] [Module.Finite k V]




end Converse

open scoped LinearAlgebra.Projectivization


end PluckerGr24
