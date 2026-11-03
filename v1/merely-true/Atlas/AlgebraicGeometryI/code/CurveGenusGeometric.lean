/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 400000

noncomputable section

namespace CurveGenusGeometric

variable (k : Type*) [Field k]
variable (A : Type*) [CommRing A] [Algebra k A]

/-- The geometric genus `g_m` of a curve over `k`, defined as the `k`-dimension of the global
sections of the canonical sheaf, modeled here as `Ω[A⁄k]`. -/
def geometricGenus : ℕ :=
  Module.finrank k (Ω[A⁄k])

/-- The arithmetic genus of a curve, defined as the `k`-dimension of `H¹(O_X)`. -/
def arithmeticGenus (H1_O : Type*) [AddCommGroup H1_O] [Module k H1_O] : ℕ :=
  Module.finrank k H1_O

/-- Corollary 29: Under Serre duality (here as a `k`-linear equivalence `H¹(O_X) ≃ (Ω[A⁄k])*`),
the arithmetic genus equals the geometric genus. -/
theorem cor29_arithmetic_eq_geometric_genus
    (H1_O : Type*) [AddCommGroup H1_O] [Module k H1_O]
    [FiniteDimensional k H1_O] [FiniteDimensional k (Ω[A⁄k])]
    (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[A⁄k])) :
    arithmeticGenus k H1_O = geometricGenus k A := by
  unfold arithmeticGenus geometricGenus
  rw [LinearEquiv.finrank_eq hSD, Subspace.dual_finrank_eq]

/-- The arithmetic genus equals the Kähler-differential dimension `dim_k Ω[A⁄k]`, via
Serre duality between `H¹(O_X)` and the dual of the global differentials. -/
theorem genus_eq_finrank_kahler
    (H1_O : Type*) [AddCommGroup H1_O] [Module k H1_O]
    [FiniteDimensional k H1_O] [FiniteDimensional k (Ω[A⁄k])]
    (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[A⁄k])) :
    arithmeticGenus k H1_O = Module.finrank k (Ω[A⁄k]) := by
  unfold arithmeticGenus
  rw [LinearEquiv.finrank_eq hSD, Subspace.dual_finrank_eq]

/-- Euler characteristic identity for the structure sheaf: given `h⁰(O_X) = 1` and
`h¹(O_X) = g`, we get `χ(O_X) = 1 - g`. -/
theorem euler_char_structure_sheaf
    (H0_O : Type*) [AddCommGroup H0_O] [Module k H0_O]
    (H1_O : Type*) [AddCommGroup H1_O] [Module k H1_O]
    (h_h0 : Module.finrank k H0_O = 1)
    (h_h1 : Module.finrank k H1_O = geometricGenus k A) :
    (Module.finrank k H0_O : ℤ) - (Module.finrank k H1_O : ℤ) =
    1 - (geometricGenus k A : ℤ) := by
  rw [h_h0, h_h1]
  simp

/-- Serre duality consistency: the Euler characteristics `χ(O_X) = 1 - g` and
`χ(ω_X) = g - 1` sum to zero. -/
theorem serre_duality_euler_char (g : ℤ) :
    (1 - g) + (g - 1) = (0 : ℤ) := by
  ring

/-- The geometric genus is non-negative when viewed as an integer. -/
theorem geometricGenus_nonneg :
    0 ≤ (geometricGenus k A : ℤ) :=
  Int.natCast_nonneg _

/-- Genus-zero (rational) curves: if the geometric genus vanishes, then so does the
arithmetic genus, via Serre duality. -/
theorem genus_zero_iff_rational
    (H1_O : Type*) [AddCommGroup H1_O] [Module k H1_O]
    [FiniteDimensional k H1_O] [FiniteDimensional k (Ω[A⁄k])]
    (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[A⁄k]))
    (hg : geometricGenus k A = 0) :
    arithmeticGenus k H1_O = 0 := by
  rw [cor29_arithmetic_eq_geometric_genus k A H1_O hSD, hg]

/-- Genus-one (elliptic) case: if the geometric genus equals `1`, then so does the
arithmetic genus. -/
theorem genus_one_elliptic
    (H1_O : Type*) [AddCommGroup H1_O] [Module k H1_O]
    [FiniteDimensional k H1_O] [FiniteDimensional k (Ω[A⁄k])]
    (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[A⁄k]))
    (hg : geometricGenus k A = 1) :
    arithmeticGenus k H1_O = 1 := by
  rw [cor29_arithmetic_eq_geometric_genus k A H1_O hSD, hg]

end CurveGenusGeometric
