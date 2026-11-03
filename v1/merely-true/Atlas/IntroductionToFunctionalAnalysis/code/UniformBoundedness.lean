/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

namespace UniformBoundedness

open scoped NNReal ENNReal

/-- **Uniform Boundedness Theorem (Banach–Steinhaus).** Let $B$ be a Banach space and
let $\{T_\alpha\}_{\alpha \in A}$ be a family in $\mathcal{B}(B, V)$ (bounded linear
operators from $B$ into a normed space $V$). If $\{T_\alpha\}$ is pointwise bounded,
i.e. for every $v \in B$ there exists $C \in \mathbb{R}$ with
$\|T_\alpha v\| \le C$ for all $\alpha$, then the operator norms are uniformly
bounded: there exists $C \in \mathbb{R}$ with $\|T_\alpha\| \le C$ for all $\alpha$. -/
theorem uniform_boundedness
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {A : Type*} {T : A → V →L[ℝ] W}
    (h : ∀ v : V, ∃ C : ℝ, ∀ α : A, ‖T α v‖ ≤ C) :
    ∃ C : ℝ, ∀ α : A, ‖T α‖ ≤ C :=
  banach_steinhaus h

end UniformBoundedness
