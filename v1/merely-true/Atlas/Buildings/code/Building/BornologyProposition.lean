/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.BornologyGroups
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry

set_option linter.unusedSectionVars false

open Set

namespace BornologyProp

variable {G : Type*} {X : Type*}

/-- Orbit of a point $x$ under the action of a set $E \subseteq G$: $\{g \cdot x : g \in E\}$. -/
def pointOrbit (act : G → X → X) (E : Set G) (x : X) : Set X :=
  {z | ∃ g ∈ E, z = act g x}

/-- Orbit of a set $Y \subseteq X$ under the action of $E \subseteq G$: $\{g \cdot y : g \in E, y \in Y\}$. -/
def setOrbit (act : G → X → X) (E : Set G) (Y : Set X) : Set X :=
  {z | ∃ g ∈ E, ∃ y ∈ Y, z = act g y}

variable [PseudoMetricSpace X]

/-- If an isometric action has bounded point orbit at some $x$ and $Y$ is bounded, then the set
orbit $E \cdot Y$ is bounded — by the triangle inequality. -/
theorem setOrbit_bounded_of_pointOrbit_bounded
    (act : G → X → X)
    (hiso : ∀ g : G, ∀ a b : X, dist (act g a) (act g b) = dist a b)
    (E : Set G) (x : X) (Y : Set X)
    (hEx : Bornology.IsBounded (pointOrbit act E x))
    (hY : Bornology.IsBounded Y) :
    Bornology.IsBounded (setOrbit act E Y) := by
  rw [Metric.isBounded_iff_subset_closedBall x] at hEx hY ⊢
  obtain ⟨δ, hδ⟩ := hEx
  obtain ⟨D, hD⟩ := hY
  refine ⟨δ + D, fun z hz => ?_⟩
  obtain ⟨g, hg, y, hy, rfl⟩ := hz
  have h1 : dist (act g x) x ≤ δ := hδ ⟨g, hg, rfl⟩
  have h2 : dist y x ≤ D := hD hy
  simp only [Metric.mem_closedBall]
  calc dist (act g y) x
      ≤ dist (act g y) (act g x) + dist (act g x) x := dist_triangle _ _ _
    _ = dist y x + dist (act g x) x := by rw [hiso g y x]
    _ ≤ D + δ := by linarith
    _ = δ + D := by ring



variable [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx} {Ω : Type*}



end BornologyProp
