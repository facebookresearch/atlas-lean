/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.OrdinarySupersingular

open OrdinarySupersingular Hasse

namespace Supersingular

/-- Auxiliary number-theoretic fact: if `t = k * p` satisfies `t^2 ≤ 4p` with `p ≥ 5`,
then `t = 0`. Used to deduce that, for `p ≥ 5`, the only multiple of `p` in the Hasse
interval `[-2√p, 2√p]` is zero. -/
lemma trace_eq_zero_of_dvd_of_sq_le
    {p : ℕ} (t : ℤ) (hp5 : (p : ℤ) ≥ 5) (hle : t ^ 2 ≤ 4 * (p : ℤ))
    (hdvd : (p : ℤ) ∣ t) :
    t = 0 := by
  obtain ⟨k, rfl⟩ := hdvd
  suffices k = 0 by simp [this]
  by_contra hk

  have hk_sq : 1 ≤ k ^ 2 := by
    have h0 := sq_pos_of_ne_zero hk
    omega

  have hle' : k ^ 2 * (p : ℤ) ^ 2 ≤ 4 * (p : ℤ) := by
    have : (k * (p : ℤ)) ^ 2 = k ^ 2 * (p : ℤ) ^ 2 := by ring
    linarith

  have hp_sq : (p : ℤ) ^ 2 ≤ 4 * (p : ℤ) := by nlinarith

  nlinarith



/-- For `E/F_p` with `p` prime, `tr π_E = 0` iff `#E(F_p) = p + 1`, since
`tr π_E = (p + 1) - #E(F_p)` by definition. -/
theorem trace_zero_iff_card_eq
    (p : ℕ) [Fact (Nat.Prime p)]
    (E : WeierstrassCurve.Affine (ZMod p)) :
    Hasse.traceFrobenius E = 0 ↔
      (Hasse.numPoints E : ℤ) = (p : ℤ) + 1 := by
  unfold Hasse.traceFrobenius Hasse.numPoints
  rw [ZMod.card]
  omega



end Supersingular
