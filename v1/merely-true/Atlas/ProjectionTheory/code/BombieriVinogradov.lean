/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Nat Real

namespace BombieriVinogradov

/-- The number of primes `p ≤ N` lying in the arithmetic progression `a (mod q)`,
i.e. `π(N; q, a) = #{ p ≤ N : p prime, p ≡ a (mod q) }`. -/
noncomputable def primeCountingArithProg (N q a : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ p % q = a % q)).card

/-- Discrepancy of the distribution of primes modulo `q` at scale `N`:
`Δ_q(N) = sup_{(a, q) = 1} |π(N; q, a) − π(N) / φ(q)|`. It measures how far the
counting function on each invertible residue class deviates from the expected value
`π(N)/φ(q)`. -/
noncomputable def primeArithProgDiscrepancy (N q : ℕ) : ℝ :=
  ⨆ (a : ℕ) (_ : Nat.Coprime a q),
    |(↑(primeCountingArithProg N q a) : ℝ) - (↑(Nat.primeCounting N) : ℝ) / (↑(Nat.totient q) : ℝ)|


end BombieriVinogradov
