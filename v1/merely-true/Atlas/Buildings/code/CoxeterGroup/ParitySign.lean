/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Basic

namespace CoxeterSystem

open List

/-- Helper: $(-1)^a = (-1)^b$ in $\mathbb{Z}^\times$ whenever $a \equiv b \pmod 2$. -/
lemma neg_one_units_pow_eq_of_mod_two_eq {a b : ℕ} (h : a % 2 = b % 2) :
    ((-1 : ℤˣ) ^ a) = ((-1 : ℤˣ) ^ b) := by
  ext
  show ((-1 : ℤ) ^ a) = ((-1 : ℤ) ^ b)
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
  rcases Nat.even_or_odd b with ⟨l, hl⟩ | ⟨l, hl⟩
  · simp [hk, hl]
  · exfalso; omega
  · exfalso; omega
  · simp [hk, hl, show Odd (2 * k + 1) from ⟨k, rfl⟩, show Odd (2 * l + 1) from ⟨l, rfl⟩,
          Odd.neg_one_pow]

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Parity sign homomorphism $\varepsilon : W \to \{\pm 1\}$ defined by
$\varepsilon(w) = (-1)^{\ell(w)}$; well-defined because $\ell$ is well-defined modulo $2$
under multiplication. -/
noncomputable def paritySign : W →* ℤˣ where
  toFun w := (-1 : ℤˣ) ^ cs.length w
  map_one' := by simp [cs.length_one]
  map_mul' w₁ w₂ := by
    have h := cs.length_mul_mod_two w₁ w₂
    have heq := neg_one_units_pow_eq_of_mod_two_eq h
    rw [heq]
    ext
    change ((-1 : ℤ) ^ (cs.length w₁ + cs.length w₂)) =
      ((-1 : ℤ) ^ cs.length w₁) * ((-1 : ℤ) ^ cs.length w₂)
    exact pow_add (-1 : ℤ) _ _

/-- Unfolding equation: $\varepsilon(w) = (-1)^{\ell(w)}$. -/
@[simp]
theorem paritySign_eq (w : W) : cs.paritySign w = (-1 : ℤˣ) ^ cs.length w := rfl

end CoxeterSystem
