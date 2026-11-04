/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.SheafCohomology
import Atlas.AlgebraicGeometryI.code.DedekindCurve
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

namespace ArithmeticGeometricGenus

/-- The arithmetic genus of `ℙ¹_k`: `g_a := dim_k H¹(ℙ¹, O)`. -/
def arithmeticGenusP1 (k : Type) [Field k] : ℕ :=
  Module.finrank k (SheafCohomology.H1 k 0)

/-- The geometric genus of `ℙ¹_k`: `g_m := dim_k Γ(ℙ¹, ω) = dim_k H⁰(ℙ¹, O(-2))`. -/
def geometricGenusP1 (k : Type) [Field k] : ℕ :=
  Module.finrank k (SheafCohomology.H0 k (-2))

/-- The arithmetic genus of `ℙ¹` is `0`. -/
theorem arithmeticGenusP1_eq_zero (k : Type) [Field k] :
    arithmeticGenusP1 k = 0 := by
  unfold arithmeticGenusP1
  exact SheafCohomology.finrank_H1_of_nonneg k 0 le_rfl

/-- The geometric genus of `ℙ¹` is `0`, since `H⁰(ℙ¹, O(-2)) = 0`. -/
theorem geometricGenusP1_eq_zero (k : Type) [Field k] :
    geometricGenusP1 k = 0 := by
  unfold geometricGenusP1
  exact SheafCohomology.finrank_H0_of_neg k (-2) (by norm_num)

/-- For `ℙ¹`, the arithmetic and geometric genera coincide (instance of Cor 29, Lec 25). -/
theorem arith_eq_geom_genus_P1 (k : Type) [Field k] :
    arithmeticGenusP1 k = geometricGenusP1 k := by
  unfold arithmeticGenusP1 geometricGenusP1

  exact SheafCohomology.serre_duality_nonneg k 0 le_rfl

variable {k : Type*} [Field k]

/-- Corollary 29 (Lec 25), abstract form: Serre duality `H¹(O) ≃ Γ(K_X)*` implies
`dim H¹(O) = dim Γ(K_X)`, so the arithmetic and geometric genera agree. -/
theorem cor29_arithmetic_eq_geometric_genus
    (C : DedekindCurve k)
    (H1_O : Type*) [AddCommGroup H1_O] [Module k H1_O]
    [FiniteDimensional k H1_O] [FiniteDimensional k (Ω[C.A⁄k])]
    (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[C.A⁄k])) :
    Module.finrank k H1_O = Module.finrank k (Ω[C.A⁄k]) := by
  rw [LinearEquiv.finrank_eq hSD, Subspace.dual_finrank_eq]

/-- Restatement of Corollary 29 in terms of the differential-defined genus `ddGenus` of a
Dedekind curve: `dim H¹(O) = g`. -/
theorem cor29_arith_genus_eq_ddGenus
    (C : DedekindCurve k)
    (H1_O : Type*) [AddCommGroup H1_O] [Module k H1_O]
    [FiniteDimensional k H1_O] [FiniteDimensional k (Ω[C.A⁄k])]
    (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[C.A⁄k])) :
    Module.finrank k H1_O = C.ddGenus := by
  unfold DedekindCurve.ddGenus
  exact cor29_arithmetic_eq_geometric_genus C H1_O hSD

/-- Numerical Serre duality on `ℙ¹`: `dim H¹(O(n)) = dim H⁰(O(-2-n))`. -/
theorem serre_duality_numerical_P1 (k : Type) [Field k] (n : ℤ) :
    Module.finrank k (SheafCohomology.H1 k n) =
    Module.finrank k (SheafCohomology.H0 k (-2 - n)) := by
  by_cases hn : 0 ≤ n
  · exact SheafCohomology.serre_duality_nonneg k n hn
  · exact SheafCohomology.serre_duality_neg k n (not_le.mp hn)

/-- Euler characteristic of `O` on `ℙ¹`: `χ(O) = 1 - g_a = 1`. -/
theorem euler_char_eq_one_minus_arithmeticGenus_P1 (k : Type) [Field k] :
    (Module.finrank k (SheafCohomology.H0 k 0) : ℤ) -
    (Module.finrank k (SheafCohomology.H1 k 0) : ℤ) =
    1 - (arithmeticGenusP1 k : ℤ) := by
  simp only [arithmeticGenusP1,
    SheafCohomology.finrank_H0_of_nonneg k 0 le_rfl,
    SheafCohomology.finrank_H1_of_nonneg k 0 le_rfl]
  norm_num

end ArithmeticGeometricGenus
