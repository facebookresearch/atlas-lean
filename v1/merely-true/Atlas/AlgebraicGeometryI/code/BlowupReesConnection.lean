/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Atlas.AlgebraicGeometryI.code.BlowupChart

open Polynomial

noncomputable section

namespace BlowupReesConnection

variable (k : Type*) [CommRing k]

/-- The ideal `(X, Y) ⊂ k[X][Y]` cutting out the origin in the affine plane. -/
def originIdeal : Ideal (Polynomial (Polynomial k)) :=
  Ideal.span {C X, X}

/-- The generator `X` (as `C X ∈ k[X][Y]`) lies in the origin ideal. -/
theorem x_mem_originIdeal :
    (C (X : Polynomial k) : Polynomial (Polynomial k)) ∈ originIdeal k :=
  Ideal.subset_span (Set.mem_insert _ _)

/-- The generator `Y` (as `X ∈ k[X][Y]`) lies in the origin ideal. -/
theorem y_mem_originIdeal :
    (X : Polynomial (Polynomial k)) ∈ originIdeal k :=
  Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))

/-- The monomial `X · t` belongs to the Rees algebra of the origin ideal. -/
theorem xt_mem_reesAlgebra :
    Polynomial.monomial 1 (C (X : Polynomial k) : Polynomial (Polynomial k)) ∈
    reesAlgebra (originIdeal k) := by
  rw [reesAlgebra.monomial_mem, pow_one]
  exact x_mem_originIdeal k

/-- The monomial `Y · t` belongs to the Rees algebra of the origin ideal. -/
theorem yt_mem_reesAlgebra :
    Polynomial.monomial 1 (X : Polynomial (Polynomial k)) ∈
    reesAlgebra (originIdeal k) := by
  rw [reesAlgebra.monomial_mem, pow_one]
  exact y_mem_originIdeal k

/-- The product `C(Y) · t` rewrites as the monomial `Y · t`. -/
theorem CX_mul_X_eq_monomial :
    (C (X : Polynomial (Polynomial k)) : Polynomial (Polynomial (Polynomial k))) *
    (X : Polynomial (Polynomial (Polynomial k))) =
    Polynomial.monomial 1 (X : Polynomial (Polynomial k)) :=
  C_mul_X_eq_monomial

/-- The product `C(Y) · t` (rewritten form of `Y · t`) belongs to the Rees algebra. -/
theorem yt_product_mem_reesAlgebra :
    (C (X : Polynomial (Polynomial k)) : Polynomial (Polynomial (Polynomial k))) *
    (X : Polynomial (Polynomial (Polynomial k))) ∈
    reesAlgebra (originIdeal k) := by
  rw [CX_mul_X_eq_monomial]
  exact yt_mem_reesAlgebra k

/-- Embedding `k[X] → k[X][Y][t]` sending a polynomial to its image as a doubly-constant
coefficient; used as the scalar part of the Rees lift. -/
def coeffEmbed : Polynomial k →+* Polynomial (Polynomial (Polynomial k)) :=
  (C : Polynomial (Polynomial k) →+* Polynomial (Polynomial (Polynomial k))).comp
  (C : Polynomial k →+* Polynomial (Polynomial k))

/-- Lift of a polynomial in `k[X][Y]` to the Rees algebra by sending `Y ↦ C(Y) · t`, exhibiting
the Rees algebra structure relevant to the blow-up at the origin. -/
def reesLift : Polynomial (Polynomial k) →+* Polynomial (Polynomial (Polynomial k)) :=
  eval₂RingHom (coeffEmbed k)
    ((C (X : Polynomial (Polynomial k)) : Polynomial (Polynomial (Polynomial k))) *
     (X : Polynomial (Polynomial (Polynomial k))))

/-- The image of `coeffEmbed` lies inside the Rees algebra of the origin ideal. -/
theorem coeffEmbed_mem_reesAlgebra (a : Polynomial k) :
    coeffEmbed k a ∈ reesAlgebra (originIdeal k) :=
  Subalgebra.algebraMap_mem (reesAlgebra (originIdeal k)) (C a)

/-- The Rees lift of any element of `k[X][Y]` lies in the Rees algebra of the origin ideal. -/
theorem reesLift_mem_reesAlgebra (f : Polynomial (Polynomial k)) :
    reesLift k f ∈ reesAlgebra (originIdeal k) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact (reesAlgebra (originIdeal k)).add_mem hp hq
  | monomial n a =>
    show eval₂ (coeffEmbed k) _ (monomial n a) ∈ _
    rw [eval₂_monomial]
    exact (reesAlgebra (originIdeal k)).mul_mem
      (coeffEmbed_mem_reesAlgebra k a)
      ((reesAlgebra (originIdeal k)).pow_mem (yt_product_mem_reesAlgebra k) n)

/-- Evaluation map specialising the Rees variable `t` to `X`; recovers the blow-up chart map
after composing with the Rees lift. -/
def evalAtX :
    Polynomial (Polynomial (Polynomial k)) →+* Polynomial (Polynomial k) :=
  evalRingHom (C (X : Polynomial k) : Polynomial (Polynomial k))

/-- Key factorisation: the blow-up chart map is the composition of the Rees lift with
evaluation at `t = X`. -/
theorem blowup_chart_factors_through_rees :
    (evalAtX k).comp (reesLift k) = blowupChartMap k := by
  apply Polynomial.ringHom_ext
  ·
    intro a
    simp [evalAtX, reesLift, coeffEmbed, blowupChartMap]
  ·
    simp [evalAtX, reesLift, coeffEmbed, blowupChartMap]

/-- Pointwise version of `blowup_chart_factors_through_rees`. -/
theorem blowup_chart_eq_eval_reesLift (f : Polynomial (Polynomial k)) :
    blowupChartMap k f = evalAtX k (reesLift k f) :=
  RingHom.congr_fun (blowup_chart_factors_through_rees k).symm f

/-- The Rees lift fixes the base variable `X`. -/
theorem reesLift_x :
    reesLift k (C (X : Polynomial k)) = coeffEmbed k (X : Polynomial k) := by
  simp [reesLift, coeffEmbed]

/-- The Rees lift sends the fibre variable `Y` to `C(Y) · t`. -/
theorem reesLift_y :
    reesLift k (X : Polynomial (Polynomial k)) =
    (C (X : Polynomial (Polynomial k)) : Polynomial (Polynomial (Polynomial k))) *
    (X : Polynomial (Polynomial (Polynomial k))) := by
  simp [reesLift, coeffEmbed]

/-- Equivalent monomial form: `reesLift Y = Y · t = monomial 1 Y`. -/
theorem reesLift_y_eq_monomial :
    reesLift k (X : Polynomial (Polynomial k)) =
    Polynomial.monomial 1 (X : Polynomial (Polynomial k)) := by
  rw [reesLift_y, CX_mul_X_eq_monomial]

end BlowupReesConnection
