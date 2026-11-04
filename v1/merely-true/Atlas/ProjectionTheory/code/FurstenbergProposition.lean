/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open Real Set

namespace FurstenbergSets

/-- A planar finset $E$ is a $(\delta, s, C)$-set in the unit ball: every point has norm
$\le 1$, distinct points are $\ge \delta$ apart, and for every ball $B(x, r)$ with
$r \ge \delta$, $|E \cap B(x,r)| \le C r^s |E|$. -/
def IsDeltaSC (E : Finset (EuclideanSpace ℝ (Fin 2))) (δ s C : ℝ) : Prop :=
  (∀ x ∈ E, ‖x‖ ≤ 1) ∧
  (∀ x₁ ∈ E, ∀ x₂ ∈ E, x₁ ≠ x₂ → dist x₁ x₂ ≥ δ) ∧
  ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), r ≥ δ →
    ((E.filter (fun y => dist y x < r)).card : ℝ) ≤ C * r ^ s * E.card

/-- A finset of angles $D \subset [0, 2\pi)$ is a $(\delta, s, C)$-set on $S^1$: distinct
angles are $\delta$-separated (mod $2\pi$), and for every arc of length $r \ge \delta$,
$|D \cap B(\theta_0, r)| \le C r^s |D|$. -/
def IsDeltaSC_S1 (D : Finset ℝ) (δ s C : ℝ) : Prop :=
  (∀ θ ∈ D, 0 ≤ θ ∧ θ < 2 * π) ∧
  (∀ θ₁ ∈ D, ∀ θ₂ ∈ D, θ₁ ≠ θ₂ →
    |θ₁ - θ₂| ≥ δ ∨ |θ₁ - θ₂ - 2 * π| ≥ δ ∨ |θ₂ - θ₁ - 2 * π| ≥ δ) ∧
  ∀ (θ₀ : ℝ) (r : ℝ), r ≥ δ →
    ((D.filter (fun θ => |θ - θ₀| < r)).card : ℝ) ≤ C * r ^ s * D.card

/-- Configuration data for the Furstenberg $\delta$-tube incidence proposition: a scale
$\delta$, exponents $t$ (for $E$) and $s$ (for the direction sets), a $(\delta, t, C)$-set
$E \subset \mathbb{R}^2$, and for each $x \in E$ a $(\delta, s, C)$-set of tube directions
$\mathbb{T}_x \subset S^1$, together with a total-tube count `totalTubes` bounding
$|\mathbb{T}_x|$ uniformly. -/
structure FurstenbergConfig where
  δ : ℝ
  t : ℝ
  s : ℝ
  C : ℝ
  E : Finset (EuclideanSpace ℝ (Fin 2))
  tubeDirections : EuclideanSpace ℝ (Fin 2) → Finset ℝ
  totalTubes : ℕ
  hδ_pos : 0 < δ
  hδ_le : δ ≤ 1
  hs_pos : 0 < s
  ht_pos : 0 < t
  hC : 1 ≤ C
  hE_spacing : IsDeltaSC E δ t C
  hDir_spacing : ∀ x ∈ E, IsDeltaSC_S1 (tubeDirections x) δ s C
  hTotalTubes_lower : ∀ x ∈ E, (tubeDirections x).card ≤ totalTubes

end FurstenbergSets
