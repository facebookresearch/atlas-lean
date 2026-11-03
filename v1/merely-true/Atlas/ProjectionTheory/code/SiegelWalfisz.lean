/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace SiegelWalfisz

open Finset Real

/-- The prime counting function for an arithmetic progression: the number of primes
$p \le N$ with $p \equiv a \pmod{q}$. -/
noncomputable def primeCountingArithProg (N q a : ℕ) : ℕ :=
  (Finset.filter (fun p => Nat.Prime p ∧ p % q = a % q) (Finset.range (N + 1))).card


end SiegelWalfisz
