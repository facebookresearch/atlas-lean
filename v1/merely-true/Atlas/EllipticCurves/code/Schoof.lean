/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Atlas.EllipticCurves.code.FrobeniusEndomorphism
import Atlas.EllipticCurves.code.TorsionEndomorphism

universe u

namespace Schoof

variable {F : Type u} [Field F] [DecidableEq F]

/-- If `P` is a nonzero element of an additive group annihilated by a prime `ℓ`,
then the additive order of `P` equals `ℓ`. Used in Schoof's algorithm to control
the order of `ℓ`-torsion points on an elliptic curve. -/
lemma addOrderOf_eq_prime_of_torsion {G : Type*} [AddGroup G]
    {P : G} {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
    (hP : (ℓ : ℤ) • P = 0) (hne : P ≠ 0) : addOrderOf P = ℓ := by
  have h1 : addOrderOf P ∣ ℓ := by
    have := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hP
    exact_mod_cast this
  rcases hℓ.eq_one_or_self_of_dvd _ h1 with h | h
  · exfalso; apply hne
    rw [← one_smul ℤ P, ← addOrderOf_nsmul_eq_zero P]
    simp [h]
  · exact h

/-- If `ℓ` divides `c - t` in `ℤ`, then `c` and `t` represent the same residue
class in `ZMod ℓ`. A small bridging lemma used to read off the trace of Frobenius
modulo `ℓ` from an integer congruence. -/
lemma zmod_eq_of_dvd_sub {c t : ℤ} {ℓ : ℕ} (hdvd : (ℓ : ℤ) ∣ (c - t)) :
    (c : ZMod ℓ) = (t : ZMod ℓ) := by
  have h : ((c - t : ℤ) : ZMod ℓ) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (c - t) ℓ).mpr hdvd
  simp only [Int.cast_sub] at h
  exact sub_eq_zero.mp h

section Lemma82

variable {W : WeierstrassCurve.Affine F}

/-- Lemma 8.2: let `E/𝔽_q` have Frobenius `π`, let `ℓ` be a prime with `ℓ ∤ q`,
and let `P ∈ E[ℓ]` be nonzero. If for some integer `c` the equation
`π_ℓ²(P) - c · π_ℓ(P) + q_ℓ · P = 0` holds, then `c ≡ tr π (mod ℓ)`. This is the
core congruence underlying Schoof's algorithm: any integer `c` solving the
characteristic equation on a single nonzero `ℓ`-torsion point must agree with
the trace of Frobenius modulo `ℓ`. -/
theorem frobenius_trace_mod_ell
    (π : W.Point →+ W.Point)
    (t q : ℤ) (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (char_eq : ∀ P : W.Point, (ℓ : ℤ) • P = 0 →
      π (π P) - t • (π P) + q • P = 0)
    (frob_torsion : ∀ P : W.Point, (ℓ : ℤ) • P = 0 → (ℓ : ℤ) • (π P) = 0)
    (frob_nonzero : ∀ P : W.Point, (ℓ : ℤ) • P = 0 → P ≠ 0 → π P ≠ 0)
    {P : W.Point}
    (hP_torsion : (ℓ : ℤ) • P = 0)
    (hP_ne : P ≠ 0)
    {c : ℤ}
    (hc : π (π P) - c • (π P) + q • P = 0) :
    (c : ZMod ℓ) = (t : ZMod ℓ) := by

  have hchar := char_eq P hP_torsion

  have h_c : π (π P) + q • P = c • (π P) := by
    rw [sub_add_eq_add_sub] at hc; exact sub_eq_zero.mp hc
  have h_t : π (π P) + q • P = t • (π P) := by
    rw [sub_add_eq_add_sub] at hchar; exact sub_eq_zero.mp hchar

  have h_eq : c • (π P) = t • (π P) := by rw [← h_c, h_t]
  have h_sub : (c - t) • (π P) = 0 := by rw [sub_smul, h_eq, sub_self]

  have hπP_ne := frob_nonzero P hP_torsion hP_ne
  have hπP_tor := frob_torsion P hP_torsion
  have hord := addOrderOf_eq_prime_of_torsion hℓ hπP_tor hπP_ne

  have hdvd : (ℓ : ℤ) ∣ (c - t) := by
    rw [← hord]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr h_sub

  exact zmod_eq_of_dvd_sub hdvd

end Lemma82

end Schoof
