/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option maxHeartbeats 400000

namespace BoundedDiffLemma

/-- A single term in the union-bound used in Lemma 9.3.5: the expected number of vertex
subsets of size $t$ in $G(n, p)$ that contain at least $\lceil 3t/2 \rceil$ edges, bounded
by $\binom{n}{t}\binom{t(t-1)/2}{3t/2} p^{3t/2}$. -/
noncomputable def unionBoundTerm (n t : ℕ) (p : ℝ) : ℝ :=
  (↑(Nat.choose n t) : ℝ) *
  (↑(Nat.choose (t * (t - 1) / 2) (3 * t / 2)) : ℝ) *
  p ^ (3 * t / 2)

/-- Sum of the union-bound terms over subset sizes $t = 4, 5, \dots, k+3$. -/
noncomputable def unionBoundSum (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ Finset.range k, unionBoundTerm n (t + 4) p

/-- The number of subset sizes $t$ to sum over in the union bound: $\lfloor C\sqrt{n} \rfloor - 3$. -/
noncomputable def numTerms (C : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (C * Real.sqrt (n : ℝ)) - 3





end BoundedDiffLemma
