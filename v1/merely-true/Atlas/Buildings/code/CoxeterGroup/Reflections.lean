/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.OrderAxiom
import Atlas.Buildings.code.CoxeterGroup.Roots

open CoxeterGroup

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

set_option linter.unusedSectionVars false

/-- A vector $v \in \mathbb{R}^B$ is a root if $v = \sigma_w(\alpha_s)$ for some word $w$
and simple generator $s$. -/
def IsRoot (M : CoxeterMatrix B) (v : B → ℝ) : Prop :=
  ∃ (w : List B) (s : B), v = sigmaWord M w (e s)

/-- The root system $\Phi = W \cdot \{\alpha_s : s \in S\}$ of $M$. -/
def roots (M : CoxeterMatrix B) : Set (B → ℝ) :=
  { v | IsRoot M v }

/-- The positive roots $\Phi^+ \subseteq \Phi$: roots with all coordinates $\geq 0$. -/
def positiveRoots (M : CoxeterMatrix B) : Set (B → ℝ) :=
  { v | IsRoot M v ∧ IsPositive v }

/-- The negative roots $\Phi^- \subseteq \Phi$: roots with all coordinates $\leq 0$. -/
def negativeRoots (M : CoxeterMatrix B) : Set (B → ℝ) :=
  { v | IsRoot M v ∧ IsNegative v }

/-- Inversion set of a word $w$: positive roots $v$ such that $\sigma_w(v) \in \Phi^-$. -/
def inversions (M : CoxeterMatrix B) (w : List B) : Set (B → ℝ) :=
  { v | IsPositive v ∧ IsRoot M v ∧ IsNegative (sigmaWord M w v) }

/-- Generalized reflection along a root $\beta$:
$s_\beta(v) = v - 2\,B_M(v, \beta)\,\beta$. -/
noncomputable def generalizedReflection (M : CoxeterMatrix B) (β : B → ℝ) :
    (B → ℝ) → (B → ℝ) :=
  fun v t => v t - 2 * bilinForm M v β * β t

end CoxeterGroup
