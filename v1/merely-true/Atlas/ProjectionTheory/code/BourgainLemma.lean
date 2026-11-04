/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Order.Filter.Basic

open scoped NNReal ENNReal
open Set

noncomputable section

namespace BourgainUniform

variable {d : ℕ}

/-- The half-open dyadic mesh cube indexed by $k \in \mathbb{Z}^d$ at scale $\delta$:
$\{x : k_i \delta \leq x_i < (k_i+1)\delta\ \forall i\}$. -/
def meshCube (δ : ℝ) (k : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, (k i : ℝ) * δ ≤ x i ∧ x i < ((k i : ℝ) + 1) * δ}

/-- The set of mesh-cube indices $k \in \mathbb{Z}^d$ such that the cube at scale $\delta$
indexed by $k$ has nonempty intersection with $X$. -/
def meshCubesIntersecting (δ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d))) :
    Set (Fin d → ℤ) :=
  {k | (meshCube δ k ∩ X).Nonempty}

/-- The mesh-counting function $|X|_\delta$: the (possibly infinite) number of $\delta$-mesh
cubes that intersect $X$. -/
def meshCount (δ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d))) : ℕ∞ :=
  Set.encard (meshCubesIntersecting δ X)

/-- `IsUniform Δ m X` is Bourgain's $(\Delta, m)$-uniformity: $X \subset [0,1]^d$, $\Delta = 1/n$
for some $n \in \mathbb{N}$, and for each $j < m$ the number of $\Delta^{j+1}$-mesh cubes
inside any given $\Delta^j$-mesh cube of $X$ is a constant $R_j$ independent of the cube
(the "branching factor" at step $j$). -/
structure IsUniform (Δ : ℝ) (m : ℕ) (X : Set (EuclideanSpace ℝ (Fin d))) : Prop where
  delta_recip_nat : ∃ n : ℕ, 0 < n ∧ Δ = 1 / (n : ℝ)
  subset_unitCube : X ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
  branching_uniform : ∀ j : ℕ, j < m →
    ∃ R : ℕ∞, ∀ k ∈ meshCubesIntersecting (Δ ^ j) X,
      meshCount (Δ ^ (j + 1)) (meshCube (Δ ^ j) k ∩ X) = R

/-- `IsRegularSet δ s C X` says that $X$ is a $(\delta, s, C)$-regular set: for every scale
$\rho \in [\delta, 1]$ and every $\rho$-mesh cube $Q$, $|X \cap Q|_\delta \leq C \rho^s |X|_\delta$,
the discrete analogue of Frostman regularity with exponent $s$. -/
def IsRegularSet (δ : ℝ) (s : ℝ) (C : ℝ≥0) (X : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ (ρ : ℝ), δ ≤ ρ → ρ ≤ 1 →
    ∀ k ∈ meshCubesIntersecting ρ X,
      (meshCount δ (meshCube ρ k ∩ X) : ℝ≥0∞) ≤
        C * (ENNReal.ofReal ρ) ^ s * (meshCount δ X : ℝ≥0∞)

end BourgainUniform
