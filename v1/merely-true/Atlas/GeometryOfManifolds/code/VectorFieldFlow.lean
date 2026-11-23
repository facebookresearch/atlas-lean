/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Compactness.Compact

open Manifold Topology Metric Set

set_option checkBinderAnnotations false

noncomputable section

/-- A smooth flow $\varphi_t : M \to M$ on a smooth $n$-manifold $M$: a time-parameterized
family of smooth self-maps with $\varphi_0 = \mathrm{id}_M$. -/
structure SmoothFlow (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ⊤ M] where
  toFun : ℝ → M → M
  map_zero : ∀ x, toFun 0 x = x
  smooth : ∀ t, ContMDiff (𝓡 n) (𝓡 n) ⊤ (toFun t)

/-- The flow at time $t = 0$ is the identity: $\varphi_0(x) = x$. -/
@[simp]
theorem SmoothFlow.toFun_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ⊤ M]
    (φ : SmoothFlow n M) (x : M) : φ.toFun 0 x = x :=
  φ.map_zero x

/-- A smooth isotopy: a smooth flow $\varphi_t : M \to M$ whose evaluation map
$(t, x) \mapsto \varphi_t(x)$ is jointly smooth on $\mathbb{R} \times M$. -/
structure SmoothIsotopy (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ⊤ M] extends SmoothFlow n M where
  jointly_smooth : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod (𝓡 n)) (𝓡 n) ⊤
    (fun (p : ℝ × M) => toFun p.1 p.2)



end
