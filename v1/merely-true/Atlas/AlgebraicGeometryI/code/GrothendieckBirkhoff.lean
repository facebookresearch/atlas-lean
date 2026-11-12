/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.PID
import Atlas.AlgebraicGeometryI.code.SheafCohomology
import Atlas.AlgebraicGeometryI.code.Lec10SheavesP1

namespace GrothendieckBirkhoff

/-- Over a PID, every submodule of `R^n` is free (used for the Grothendieck-Birkhoff splitting). -/
instance pid_submodule_Rn_free (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (n : ℕ) (N : Submodule R (Fin n → R)) :
    Module.Free R N :=
  inferInstance

/-- Euler characteristic of `O(n)` on `P^1`: `χ(O(n)) = dim H^0 - dim H^1`. -/
noncomputable def eulerCharP1 (k : Type) [Field k] (n : ℤ) : ℤ :=
  (Module.finrank k (SheafCohomology.H0 k n) : ℤ) -
  (Module.finrank k (SheafCohomology.H1 k n) : ℤ)

/-- Closed-form Euler characteristic: `χ(O_{P^1}(n)) = n + 1`. -/
theorem eulerCharP1_eq (k : Type) [Field k] (n : ℤ) :
    eulerCharP1 k n = n + 1 :=
  SheafCohomology.euler_characteristic k n

/-- `χ(O_{P^1}) = 1`. -/
theorem eulerCharP1_structure_sheaf (k : Type) [Field k] :
    eulerCharP1 k 0 = 1 := by
  rw [eulerCharP1_eq]; ring

/-- Genus of `P^1` is zero: `h^1(O_{P^1}) = 0`. -/
theorem genusP1_eq_zero (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H1 k 0) = 0 :=
  SheafCohomology.finrank_H1_of_nonneg k 0 le_rfl

/-- Genus of a smooth plane curve of degree `d`: `g = (d - 1)(d - 2)/2`, the adjunction formula. -/
def genus_plane_curve (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

/-- A line (`d = 1`) has genus zero. -/
theorem genus_plane_curve_line : genus_plane_curve 1 = 0 := by decide
/-- A smooth conic (`d = 2`) has genus zero. -/
theorem genus_plane_curve_conic : genus_plane_curve 2 = 0 := by decide
/-- A smooth plane cubic (`d = 3`) has genus `1` (an elliptic curve). -/
theorem genus_plane_curve_cubic : genus_plane_curve 3 = 1 := by decide
/-- A smooth plane quartic (`d = 4`) has genus `3`. -/
theorem genus_plane_curve_quartic : genus_plane_curve 4 = 3 := by decide

/-- Euler characteristic of a split bundle on `P^1` equals `∑ (d_i + 1)`. -/
theorem split_bundle_euler_char (k : Type) [Field k] (n : ℕ) (degrees : Fin n → ℤ) :
    ∑ i, eulerCharP1 k (degrees i) = ∑ i, (degrees i + 1) := by
  congr 1; ext i; exact eulerCharP1_eq k (degrees i)

/-- Riemann-Roch for a split bundle on `P^1`: `χ(⊕ O(d_i)) = (∑ d_i) + n`. -/
theorem split_bundle_rr_P1 (k : Type) [Field k] (n : ℕ) (degrees : Fin n → ℤ) :
    ∑ i, eulerCharP1 k (degrees i) = (∑ i, degrees i) + n := by
  rw [split_bundle_euler_char]
  simp [Finset.sum_add_distrib, Finset.sum_const]

end GrothendieckBirkhoff
