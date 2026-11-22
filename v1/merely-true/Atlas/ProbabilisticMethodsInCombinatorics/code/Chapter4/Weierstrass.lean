/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.ContinuousMap.Weierstrass

open Polynomial Set

namespace Weierstrass

/-- **Weierstrass approximation theorem (Theorem 4.7.1, 1885).** Every continuous function
$f : [0, 1] \to \mathbb{R}$ can be uniformly approximated by polynomials: for every
$\varepsilon > 0$ there exists a polynomial $p \in \mathbb{R}[X]$ such that
$|p(x) - f(x)| \le \varepsilon$ for all $x \in [0, 1]$. -/
theorem weierstrass_approximation (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Icc (0 : ℝ) 1, |p.eval x - f x| ≤ ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf ε hε
  exact ⟨p, fun x hx => le_of_lt (hp x hx)⟩

end Weierstrass
