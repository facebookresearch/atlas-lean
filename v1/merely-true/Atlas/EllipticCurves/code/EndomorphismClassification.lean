/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.Theorem136
import Atlas.EllipticCurves.code.OrdinarySupersingular

set_option autoImplicit false

/-- Number-theoretic lemma: if `k² = pⁿ` for a prime `p` and natural number `k`,
then `n` is even. Proved by strong induction on `n` using that primes are not
squares. -/
lemma even_of_sq_eq_prime_pow (p : ℕ) (hp : Nat.Prime p) :
    ∀ n k : ℕ, k ^ 2 = p ^ n → Even n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k hk
    match n with
    | 0 => exact ⟨0, by omega⟩
    | 1 =>
      exfalso
      simp [pow_one] at hk
      exact Irreducible.not_isSquare hp ⟨k, by rw [← hk]; ring⟩
    | n + 2 =>
      have hpk2 : p ∣ k ^ 2 := ⟨p ^ (n + 1), by rw [hk]; ring⟩
      have hpk : p ∣ k := hp.dvd_of_dvd_pow hpk2
      obtain ⟨j, rfl⟩ := hpk
      have hpn : j ^ 2 = p ^ n := by
        have h1 : (p * j) ^ 2 = p ^ (n + 2) := hk
        have h2 : p ^ 2 * j ^ 2 = p ^ 2 * p ^ n := by
          have : p * p * (j * j) = p * p * p ^ n := by
            calc p * p * (j * j) = (p * j) * (p * j) := by ring
            _ = (p * j) ^ 2 := by ring
            _ = p ^ (n + 2) := h1
            _ = p * p * p ^ n := by ring
          linarith
        exact Nat.eq_of_mul_eq_mul_left
          (Nat.pos_of_ne_zero (pow_ne_zero 2 hp.ne_zero)) h2
      have heven := ih n (by omega) j hpn
      obtain ⟨m, rfl⟩ := heven
      exact ⟨m + 1, by omega⟩

/-- Integer analogue: if an integer satisfies `t² = 4·pⁿ` for a prime `p`, then
`n` is even. This is used to detect when `tr π_E)² = 4q` forces special
behavior over even-degree extensions. -/
lemma even_of_int_sq_eq_four_mul_prime_pow (p : ℕ) (hp : Nat.Prime p) (n : ℕ) (t : ℤ)
    (h : t ^ 2 = 4 * (p ^ n : ℤ)) : Even n := by

  have heven_t : 2 ∣ t := by
    have heven_sq : Even (t ^ 2) := ⟨2 * (p ^ n : ℤ), by omega⟩
    rw [Int.even_pow] at heven_sq
    exact even_iff_two_dvd.mp heven_sq.1

  obtain ⟨k, rfl⟩ := heven_t
  have hk2 : k ^ 2 = (p : ℤ) ^ n := by nlinarith

  have hnat : (k.natAbs) ^ 2 = p ^ n := by
    have h1 : ((k.natAbs : ℤ) ^ 2 : ℤ) = k ^ 2 := Int.natAbs_sq k
    have h2 : ((k.natAbs ^ 2 : ℕ) : ℤ) = (k.natAbs : ℤ) ^ 2 := by push_cast; ring
    have h3 : ((p ^ n : ℕ) : ℤ) = (p : ℤ) ^ n := by push_cast; ring
    exact_mod_cast (show ((k.natAbs ^ 2 : ℕ) : ℤ) = ((p ^ n : ℕ) : ℤ) by
      rw [h2, h1, hk2, h3])
  exact even_of_sq_eq_prime_pow p hp n k.natAbs hnat

open OrdinarySupersingular EndomorphismRingOverFiniteField

section Corollary137_EC

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]



end Corollary137_EC
