/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace BourgainMultiscale

open Set MeasureTheory

/-- `IsAlmostLinear f a b t_I ε` says that on the interval $[a,b]$, $f$ is within $\varepsilon$
of the linear function $x \mapsto f(a) + t_I (x - a)$ of slope $t_I$. -/
def IsAlmostLinear (f : ℝ → ℝ) (a b : ℝ) (t_I : ℝ) (ε : ℝ) : Prop :=
  ∀ x ∈ Icc a b, |f x - (f a + t_I * (x - a))| ≤ ε

/-- `IsSemiWellSpaced f a b s` says that on the left half of $[a,b]$, $f$ grows at slope at
least $2-s$, and on the right half, $f$ grows at slope at least $s$ — encoding the
"semi-well-spaced" alternative of the multiscale decomposition. -/
def IsSemiWellSpaced (f : ℝ → ℝ) (a b : ℝ) (s : ℝ) : Prop :=
  let mid := (a + b) / 2
  (∀ x ∈ Icc a mid, f x ≥ f a + (2 - s) * (x - a)) ∧
  (∀ x ∈ Icc mid b, f x ≥ f mid + s * (x - mid))

/-- `AdmissibleBranching f t` packages the hypotheses on the branching profile $f : [0,1] \to
\mathbb{R}$: $f$ is monotone, $2$-Lipschitz, satisfies $f(0)=0$, $f(1)=t$, and the lower bound
$f(x) \geq t\cdot x$. -/
structure AdmissibleBranching (f : ℝ → ℝ) (t : ℝ) : Prop where
  monotone : MonotoneOn f (Icc 0 1)
  lipschitz : LipschitzOnWith 2 f (Icc 0 1)
  f_zero : f 0 = 0
  f_one : f 1 = t
  lower_bound : ∀ x ∈ Icc (0 : ℝ) 1, f x ≥ t * x



end BourgainMultiscale
