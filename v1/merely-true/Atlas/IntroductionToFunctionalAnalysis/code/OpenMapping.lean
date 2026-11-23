/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Operator.Banach

namespace OpenMapping

open Function

/-- **Open Mapping Theorem.** Let $B_1, B_2$ be two Banach spaces, and let
$T \in \mathcal{B}(B_1, B_2)$ be a surjective bounded linear operator. Then $T$ is an
open map, meaning that for every open subset $U \subset B_1$, the image $T(U)$ is open
in $B_2$. -/
theorem open_mapping_theorem
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
    (T : V →L[𝕜] W) (hT : Surjective T) : IsOpenMap T :=
  T.isOpenMap hT

/-- The continuous linear equivalence $V \simeq_L W$ constructed from a bijective bounded
linear operator $T : V \to W$ between Banach spaces. By the Open Mapping Theorem, the
set-theoretic inverse is automatically continuous, so $T$ upgrades to a continuous linear
equivalence. -/
noncomputable def continuousLinearEquivOfBijective
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
    (T : V →L[𝕜] W) (hT : Bijective T) : V ≃L[𝕜] W :=
  ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hT.1)
    (LinearMap.range_eq_top.mpr hT.2)

/-- **Bounded Inverse Theorem (Corollary of the Open Mapping Theorem).** If $B_1, B_2$
are two Banach spaces and $T \in \mathcal{B}(B_1, B_2)$ is bijective, then there exists a
bounded linear operator $S : B_2 \to B_1$ which is a two-sided inverse of $T$, i.e.
$T \circ S = \mathrm{id}_{B_2}$ and $S \circ T = \mathrm{id}_{B_1}$. In particular,
$T^{-1} \in \mathcal{B}(B_2, B_1)$. -/
theorem bijective_bounded_inverse
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
    (T : V →L[𝕜] W) (hT : Bijective T) :
    ∃ S : W →L[𝕜] V, (∀ w, T (S w) = w) ∧ (∀ v, S (T v) = v) := by
  let e := continuousLinearEquivOfBijective T hT
  exact ⟨e.symm.toContinuousLinearMap,
    fun w => e.apply_symm_apply w,
    fun v => e.symm_apply_apply v⟩

end OpenMapping
