/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open Classical

namespace MillerRabin

/-- Predicate stating that `a` is a Miller-Rabin witness for compositeness of `N`:
i.e., writing `N - 1 = 2^s * d` with `d` odd and `s > 0`, neither `a^d ≡ 1 (mod N)` nor
`a^(2^r * d) ≡ -1 (mod N)` holds for any `0 ≤ r < s`. -/
def IsMillerRabinWitness (N a : ℕ) : Prop :=
  ∃ (s d : ℕ), 0 < s ∧ Odd d ∧ N - 1 = 2 ^ s * d ∧
    (a : ZMod N) ^ d ≠ 1 ∧
    ∀ r : ℕ, r < s → (a : ZMod N) ^ (2 ^ r * d) ≠ -1

/-- The set of odd integers in the interval `[2^(k-1), 2^k]`. -/
def oddIntRange (k : ℕ) : Finset ℕ :=
  (Finset.Icc (2 ^ (k - 1)) (2 ^ k)).filter Odd

/-- The set of pairs `(N, a)` where `N` is an odd integer in `[2^(k-1), 2^k]`,
`a ∈ [1, N-1]`, and `a` is **not** a Miller-Rabin witness for `N`. -/
def nonWitnessPairs (k : ℕ) : Finset (ℕ × ℕ) :=
  ((oddIntRange k) ×ˢ (Finset.range (2 ^ k))).filter
    fun p => p.2 ∈ Finset.Icc 1 (p.1 - 1) ∧ ¬ IsMillerRabinWitness p.1 p.2

/-- The subset of `nonWitnessPairs k` for which `N` is actually prime. -/
def primeNonWitnessPairs (k : ℕ) : Finset (ℕ × ℕ) :=
  (nonWitnessPairs k).filter fun p => Nat.Prime p.1


end MillerRabin

end
