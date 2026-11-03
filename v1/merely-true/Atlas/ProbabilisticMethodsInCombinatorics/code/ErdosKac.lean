/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open ArithmeticFunction Finset Filter MeasureTheory ProbabilityTheory Real
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace ErdosKac

/-- Normalized version of the number-of-distinct-prime-factors function:
$(\nu(x) - \log\log n) / \sqrt{\log\log n}$. This is the standardization that should
converge in distribution to a standard normal. -/
noncomputable def normalizedOmega (n : ℕ) (x : ℕ) : ℝ :=
  ((cardDistinctFactors x : ℝ) - Real.log (Real.log (n : ℝ))) /
    Real.sqrt (Real.log (Real.log (n : ℝ)))

/-- Empirical density at level $t$: the fraction of integers in $[1,n]$ whose normalized
omega is at least $t$. The Erdős–Kac theorem describes its limit as $n \to \infty$. -/
noncomputable def erdosKacDensity (n : ℕ) (t : ℝ) : ℝ :=
  ((Icc 1 n).filter (fun x => normalizedOmega n x ≥ t)).card / (n : ℝ)

/-- The standard Gaussian upper-tail probability $\Pr(Z \ge t)$ for $Z \sim \mathcal{N}(0,1)$. -/
noncomputable def gaussianTailProb (t : ℝ) : ℝ :=
  ((gaussianReal 0 1) (Set.Ici t)).toReal

/-- The $k$-th empirical moment of `normalizedOmega n ·` averaged uniformly over
$x \in [1,n]$. -/
noncomputable def empiricalMoment (n : ℕ) (k : ℕ) : ℝ :=
  (∑ x ∈ Icc 1 n, (normalizedOmega n x) ^ k) / (n : ℝ)

/-- The $k$-th moment of the standard normal distribution
$\mathbb{E}[Z^k]$ for $Z \sim \mathcal{N}(0,1)$. -/
noncomputable def standardNormalMoment (k : ℕ) : ℝ :=
  ∫ (x : ℝ), x ^ k ∂(gaussianReal 0 1)

end ErdosKac







namespace ErdosKac

open Filter



end ErdosKac
