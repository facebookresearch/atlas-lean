/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannRoch

open RiemannRoch

/-- Riemann–Roch for line bundles on `ℙ¹`: `h⁰(O(d)) − h¹(O(d)) = d + 1`. -/
theorem riemann_roch_line_bundle_p1 (k : Type) [Field k] (d : ℤ) :
    (dimH0 k d : ℤ) - (dimH1 k d : ℤ) = d + 1 :=
  riemann_roch_P1 k d

/-- Classical Serre form of Riemann–Roch on `ℙ¹`:
`h⁰(O(d)) − h⁰(O(K - d)) = d + 1`, with `K_{ℙ¹}` of degree `-2`. -/
theorem serre_duality_classical_P1 (k : Type) [Field k] (d : ℤ) :
    (dimH0 k d : ℤ) - (dimH0 k (-2 - d) : ℤ) = d + 1 :=
  riemann_roch_serre_form k d

/-- The genus of `ℙ¹`: `h¹(O_{ℙ¹}) = 0`. -/
theorem genus_P1 (k : Type) [Field k] : dimH1 k 0 = 0 := by
  rw [show (0 : ℤ) = ↑(0 : ℕ) from rfl]; exact dimH1_nonneg k 0

/-- Arithmetic genus equals geometric genus on `ℙ¹`: both vanish. -/
theorem arithmetic_eq_geometric_genus_P1 (k : Type) [Field k] :
    dimH1 k 0 = dimH0 k (-2) := by
  rw [show (0 : ℤ) = ↑(0 : ℕ) from rfl, dimH1_nonneg, dimH0_neg k (-2) (by norm_num)]

/-- The degree of the canonical divisor on `ℙ¹` equals `2g − 2 = -2`. -/
theorem deg_canonical_P1 : ((-2 : ℤ) = 2 * 0 - 2) := by ring

/-- Riemann's inequality on `ℙ¹`: `h⁰(O(d)) ≥ d + 1 − g_{ℙ¹} = d + 1`. -/
theorem dimH0_ge_P1 (k : Type) [Field k] (d : ℤ) :
    (dimH0 k d : ℤ) ≥ d + 1 - 0 := by
  linarith [riemann_roch_P1 k d, show (dimH1 k d : ℤ) ≥ 0 from Int.natCast_nonneg _]

/-- Čech-level Serre duality on `ℙ¹`: `dim H¹(O(n)) = dim H⁰(O(-2 - n))`. -/
theorem cech_duality_dimension_P1 (k : Type) [Field k] (n : ℤ) :
    dimH1 k n = dimH0 k (-2 - n) :=
  serre_duality_P1 k n
