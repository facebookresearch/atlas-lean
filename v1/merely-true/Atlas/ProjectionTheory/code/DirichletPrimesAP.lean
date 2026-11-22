/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Prime.Basic

open Filter Finset

namespace DirichletPrimesAP

/-- The prime-counting function `π(N) = #{p ≤ N : p prime}`. -/
def pi_count (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter Nat.Prime).card

/--
The number of primes up to `N` lying in the arithmetic progression `a (mod q)`:
`π(N; q, a) = #{p ≤ N : p prime, p ≡ a (mod q)}`.
-/
def pi_count_mod (N q a : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p % q = a % q)).card

/-- The set of residues `a ∈ {0, …, q − 1}` coprime to `q`, i.e. `(ℤ/qℤ)ˣ`. -/
def coprimeResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (Nat.Coprime · q)

/--
The discrepancy `Δ_q(N) = max_{a ∈ (ℤ/qℤ)ˣ} |π(N; q, a) − π(N)/φ(q)|` measuring
how far primes up to `N` are from being equidistributed among the reduced
residue classes modulo `q`.
-/
noncomputable def delta_q (q N : ℕ) : ℝ :=
  if h : (coprimeResidues q).Nonempty then
    (coprimeResidues q).sup' h
      (fun a => |(↑(pi_count_mod N q a) : ℝ) - (↑(pi_count N) : ℝ) / (↑(Nat.totient q) : ℝ)|)
  else 0


end DirichletPrimesAP
