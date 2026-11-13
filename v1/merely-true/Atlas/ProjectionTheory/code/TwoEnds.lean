/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting

noncomputable section

open Classical Finset BigOperators

namespace TwoEnds

/-- A point in the Euclidean plane `ℝ²`, modelled as `EuclideanSpace ℝ (Fin 2)`. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The `δ`-tube around the unit-length segment `{c + t v : |t| ≤ 1/2}`:
the set of points within Euclidean distance `δ` of some point on that segment. -/
def deltaTube (c v : Point) (δ : ℝ) : Set Point :=
  { x | ∃ t : ℝ, |t| ≤ 1/2 ∧ ‖x - (c + t • v)‖ ≤ δ }

/-- `IsDeltaTube T δ` says that `T` is a `δ`-tube, i.e. it is of the form
`deltaTube c v δ` for some centre `c` and unit-length direction `v`. -/
def IsDeltaTube (T : Set Point) (δ : ℝ) : Prop :=
  ∃ (c v : Point), ‖v‖ = 1 ∧ T = deltaTube c v δ

/-- A finite set `E ⊂ B(0,1)` of `N` points is "well-spaced" (with constant
`C`) in the sense of Sharp Projection Theorems III: it lies in the unit
ball, has cardinality comparable to `N`, and every ball of radius `N^{-1/2}`
contains at most `C` points of `E`. -/
structure WellSpaced (E : Finset Point) (N : ℕ) (C : ℝ) : Prop where
  subset_unitBall : ∀ x ∈ E, ‖x‖ ≤ 1
  card_lower : (N : ℝ) ≤ C * E.card
  card_upper : (E.card : ℝ) ≤ C * N
  spacing : ∀ x : Point,
    ((E.filter (fun y => ‖y - x‖ ≤ (N : ℝ) ^ (-(1 : ℝ) / 2))).card : ℝ) ≤ C


/-- A family of `δ`-tubes `𝕋` contained in a fixed `ρ`-tube `Tρ`, each of
which contains many points of `E` and additionally satisfies the
**two-ends condition**: for each `T ∈ 𝕋` one can split its `≳ R` points
of `E ∩ T` into two clusters `H₁ T`, `H₂ T`, both of cardinality at least
`C⁻¹ R`, separated by Euclidean distance at least `δ`. This is exactly
the hypothesis of the two-ends lemma. -/
structure TubeFamily (E : Finset Point) (Tρ : Set Point) (ρ δ : ℝ) (R : ℕ) (C : ℝ) where
  hTρ_tube : IsDeltaTube Tρ ρ
  hδ_le_ρ : δ ≤ ρ
  tubes : Finset (Set Point)
  is_tube : ∀ T ∈ tubes, IsDeltaTube T δ
  subset_Tρ : ∀ T ∈ tubes, T ⊆ Tρ
  H₁ : Set Point → Finset Point
  H₂ : Set Point → Finset Point
  H₁_sub : ∀ T ∈ tubes, H₁ T ⊆ E.filter (fun x => x ∈ Tρ)
  H₂_sub : ∀ T ∈ tubes, H₂ T ⊆ E.filter (fun x => x ∈ Tρ)
  H₁_in_tube : ∀ T ∈ tubes, ∀ x ∈ H₁ T, (x : Point) ∈ T
  H₂_in_tube : ∀ T ∈ tubes, ∀ x ∈ H₂ T, (x : Point) ∈ T
  separation : ∀ T ∈ tubes,
    ∀ x ∈ H₁ T, ∀ y ∈ H₂ T, ‖(x : Point) - y‖ ≥ δ
  H₁_card : ∀ T ∈ tubes, C⁻¹ * (R : ℝ) ≤ (H₁ T).card
  H₂_card : ∀ T ∈ tubes, C⁻¹ * (R : ℝ) ≤ (H₂ T).card



end TwoEnds
