/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option maxHeartbeats 400000

open Set

namespace SphereArrangement

/-- Three-dimensional Euclidean space $\mathbb{R}^3$ used for the sphere-cutting bound. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- A sphere in $\mathbb{R}^3$ specified by a center and a strictly positive radius. -/
structure Sphere3 where
  center : R3
  radius : ℝ
  radius_pos : 0 < radius

/-- The underlying point set of a sphere: $\{x \in \mathbb{R}^3 : \|x - c\| = r\}$. -/
def Sphere3.toSet (S : Sphere3) : Set R3 :=
  Metric.sphere S.center S.radius

/-- The union $\bigcup_i S_i$ of a finite family of spheres in $\mathbb{R}^3$. -/
def sphereUnion (spheres : Fin n → Sphere3) : Set R3 :=
  ⋃ i, (spheres i).toSet

/-- Number of connected components of the complement of $\bigcup_i S_i$ in $\mathbb{R}^3$. -/
noncomputable def numComponentsComplement (spheres : Fin n → Sphere3) : ℕ :=
  Nat.card (ConnectedComponents (↥(sphereUnion spheres)ᶜ))




end SphereArrangement
