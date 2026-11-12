/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Order.UpperLower.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter7.MaxDegree

set_option maxHeartbeats 800000
set_option maxRecDepth 1000

open Finset Filter
open scoped Classical

namespace MaxDegreeRandomGraph

/-- The number of labeled simple graphs on $\{1, \dots, n\}$ whose maximum degree is at
most $\lfloor n/2 \rfloor$. -/
noncomputable def numGraphsMaxDegBounded (n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
    G.maxDegree ≤ n / 2))

/-- Total number of labeled simple graphs on $n$ vertices, equal to $2^{\binom{n}{2}}$. -/
noncomputable def numGraphsTotal (n : ℕ) : ℕ :=
  Fintype.card (SimpleGraph (Fin n))

/-- Probability that the uniform random labeled graph $G(n, 1/2)$ has maximum degree at most
$\lfloor n/2 \rfloor$. -/
noncomputable def probMaxDegAtMostHalf (n : ℕ) : ℝ :=
  (numGraphsMaxDegBounded n : ℝ) / (numGraphsTotal n : ℝ)

end MaxDegreeRandomGraph


