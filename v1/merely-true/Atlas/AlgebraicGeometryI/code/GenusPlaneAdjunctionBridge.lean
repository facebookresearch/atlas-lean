/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoff
import Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves

open GrothendieckBirkhoff CanonicalSheafCurves

namespace GenusPlaneAdjunctionBridge

/-- The product `(d - 1)(d - 2)` is always even, since one of two consecutive integers is even. -/
theorem two_dvd_shifted_product (d : ℕ) : 2 ∣ (d - 1) * (d - 2) := by
  rcases Nat.even_or_odd (d - 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (d - 2), by rw [hm]; ring⟩
  · have hd2 : d - 2 = m + m := by omega
    exact ⟨(d - 1) * m, by rw [hd2]; ring⟩

/-- `2 g = (d - 1)(d - 2)` for the plane-curve genus formula in `ℕ`. -/
theorem two_mul_genus_plane_curve (d : ℕ) :
    2 * genus_plane_curve d = (d - 1) * (d - 2) :=
  Nat.mul_div_cancel' (two_dvd_shifted_product d)

/-- Integer version of `two_mul_genus_plane_curve`, valid for `d ≥ 2`. -/
theorem two_mul_genus_plane_curve_int (d : ℕ) (hd : 2 ≤ d) :
    2 * ((genus_plane_curve d : ℕ) : ℤ) = ((d : ℤ) - 1) * ((d : ℤ) - 2) := by
  have _h1 : 1 ≤ d := by omega
  exact_mod_cast two_mul_genus_plane_curve d

/-- Algebraic step from adjunction: `deg K_D = d(d - 3) = 2g - 2` implies `2g = (d-1)(d-2)`. -/
theorem adjunction_chain_two_g (d g : ℤ) (hdegK : d * (d - 3) = 2 * g - 2) :
    2 * g = (d - 1) * (d - 2) := by
  linarith [show d * (d - 3) + 2 = (d - 1) * (d - 2) from by ring]

/-- Divide `2g = (d - 1)(d - 2)` by 2 to obtain the genus formula `g = (d-1)(d-2)/2`. -/
theorem adjunction_chain_genus (d g : ℤ) (h : 2 * g = (d - 1) * (d - 2)) :
    g = (d - 1) * (d - 2) / 2 := by
  have h2 : (2 : ℤ) ≠ 0 := by norm_num
  rw [← h, Int.mul_ediv_cancel_left g h2]

/-- Combined adjunction chain: from `deg K_D = d(d - 3) = 2g - 2`, conclude
`g = (d - 1)(d - 2)/2`. -/
theorem adjunction_chain_degK_to_genus (d g : ℤ) (hdegK : d * (d - 3) = 2 * g - 2) :
    g = (d - 1) * (d - 2) / 2 :=
  adjunction_chain_genus d g (adjunction_chain_two_g d g hdegK)

/-- The packaged plane-curve genus matches the closed-form `(d - 1)(d - 2)/2` from adjunction. -/
theorem genus_plane_curve_eq_adjunction_genus (d : ℕ) (hd : 2 ≤ d) :
    ((genus_plane_curve d : ℕ) : ℤ) = ((d : ℤ) - 1) * ((d : ℤ) - 2) / 2 := by
  have h := two_mul_genus_plane_curve_int d hd
  have h2 : (2 : ℤ) ≠ 0 := by norm_num
  rw [← Int.mul_ediv_cancel_left ((genus_plane_curve d : ℕ) : ℤ) h2]
  rw [h]

end GenusPlaneAdjunctionBridge
