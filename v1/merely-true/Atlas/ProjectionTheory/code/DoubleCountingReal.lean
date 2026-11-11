/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset BigOperators

namespace ProjectionTheory

/-- The finite range of dyadic exponents `{0, 1, …, ⌊log₂ R⌋}` used to index the scales
`r = 2^k` in dyadic decompositions up to a real cutoff `R`. -/
noncomputable def dyadicExponentRange (R : ℝ) : Finset ℕ :=
  Finset.range (Nat.log 2 ⌊R⌋₊ + 1)

/-- A point in the Euclidean plane `ℝ²`, encoded as `Fin 2 → ℝ`. -/
abbrev Point2 := Fin 2 → ℝ

/-- A direction vector in `ℝ²`, encoded as `Fin 2 → ℝ`. -/
abbrev Direction := Fin 2 → ℝ

/-- The projection `π_θ(x) = x · θ = ∑_i x_i θ_i` of a planar point `x` onto the
direction `θ ∈ ℝ²`. -/
noncomputable def projDir (θ : Direction) (x : Point2) : ℝ :=
  ∑ i : Fin 2, x i * θ i

/-- The set of triples `(x₁, x₂, θ) ∈ X × X × D` whose projections under `θ` are within
distance `2`, i.e. `|π_θ(x₁) − π_θ(x₂)| ≤ 2`. Its cardinality is the incidence quantity
that is bounded both from below and above in the real-version double counting argument. -/
noncomputable def collisionSet (X : Finset Point2) (D : Finset Direction) :
    Finset (Point2 × Point2 × Direction) :=
  (X ×ˢ X ×ˢ D).filter fun ⟨x₁, x₂, θ⟩ =>
    |projDir θ x₁ - projDir θ x₂| ≤ 2

/-- The data for the SETUP of the real-version double-counting theorem: a scale
parameter `R ≥ 1`, the cardinalities `|X|` and `|D|` of a planar point set and a
direction set, the maximal projection size `S` (with `0 < S ≤ |X|`), and the multiscale
covering numbers `N_X(r)`, `N_D(ρ)` at radii `r, ρ`. -/
structure DoubleCountingRealSetup where
  R : ℝ
  hR : 1 ≤ R
  cardX : ℕ
  cardD : ℕ
  S : ℕ
  hS_pos : 0 < S
  hS_le : S ≤ cardX
  N_X : ℝ → ℕ
  N_D : ℝ → ℕ
  hN_X_le : ∀ r, N_X r ≤ cardX
  hN_D_le : ∀ ρ, N_D ρ ≤ cardD

/-- The dyadic incidence-count sum `∑_{1 ≤ r ≤ R, dyadic} N_X(r) · N_D(1/r)` appearing
on the right-hand side of the real-version double-counting theorem. -/
noncomputable def dyadicSum (setup : DoubleCountingRealSetup) : ℕ :=
  ∑ k ∈ dyadicExponentRange setup.R, setup.N_X (2 ^ k) * setup.N_D ((2 : ℝ) ^ k)⁻¹

/-- **Theorem (Double Counting, real version).** Under the standard SETUP, an
incidence (collision) count `I` admits the lower bound
`I ≳ |D| · |X|² / S` and the upper bound `I ≲ |X| · ∑_r N_X(r) N_D(1/r)`. Combining
these gives `|D| ≲ (S/|X|) ∑_{1 ≤ r ≤ R} N_X(r) N_D(1/r)`. -/
theorem double_counting_real (setup : DoubleCountingRealSetup)
    (hX_pos : 0 < setup.cardX)
    (collisionCount : ℝ)
    (hLower : ∃ c₁ : ℝ, c₁ > 0 ∧
      c₁ * (setup.cardD : ℝ) * ((setup.cardX : ℝ) ^ 2 / (setup.S : ℝ)) ≤ collisionCount)
    (hUpper : ∃ c₂ : ℝ, c₂ > 0 ∧
      collisionCount ≤ c₂ * (setup.cardX : ℝ) *
        ((∑ k ∈ dyadicExponentRange setup.R, setup.N_X (2 ^ k) * setup.N_D ((2 : ℝ) ^ k)⁻¹ : ℕ) : ℝ)) :
    ∃ C : ℝ, C > 0 ∧
      (setup.cardD : ℝ) ≤ C * ((setup.S : ℝ) / (setup.cardX : ℝ)) *
        (dyadicSum setup : ℝ) := by
  obtain ⟨c₁, hc₁_pos, hLower⟩ := hLower
  obtain ⟨c₂, hc₂_pos, hUpper⟩ := hUpper
  have hchain : c₁ * (setup.cardD : ℝ) * ((setup.cardX : ℝ) ^ 2 / (setup.S : ℝ)) ≤
      c₂ * (setup.cardX : ℝ) * (dyadicSum setup : ℝ) :=
    le_trans hLower hUpper
  refine ⟨c₂ / c₁, div_pos hc₂_pos hc₁_pos, ?_⟩
  have hX_pos' : (0 : ℝ) < (setup.cardX : ℝ) := Nat.cast_pos.mpr hX_pos
  have hS_pos' : (0 : ℝ) < (setup.S : ℝ) := Nat.cast_pos.mpr setup.hS_pos
  have hc₁X_pos : (0 : ℝ) < c₁ * (setup.cardX : ℝ) := mul_pos hc₁_pos hX_pos'
  have hkey : (setup.cardD : ℝ) * (c₁ * (setup.cardX : ℝ)) ≤
      c₂ * (setup.S : ℝ) * (dyadicSum setup : ℝ) := by
    have h1 : c₁ * (setup.cardD : ℝ) * ((setup.cardX : ℝ) ^ 2 / (setup.S : ℝ)) =
        (setup.cardD : ℝ) * (c₁ * (setup.cardX : ℝ)) * ((setup.cardX : ℝ) / (setup.S : ℝ)) := by
      ring
    have h2 : c₂ * (setup.cardX : ℝ) * (dyadicSum setup : ℝ) =
        c₂ * (setup.S : ℝ) * (dyadicSum setup : ℝ) * ((setup.cardX : ℝ) / (setup.S : ℝ)) := by
      field_simp
    nlinarith [div_pos hX_pos' hS_pos']
  rw [show c₂ / c₁ * ((setup.S : ℝ) / (setup.cardX : ℝ)) * (dyadicSum setup : ℝ) =
      c₂ * (setup.S : ℝ) * (dyadicSum setup : ℝ) / (c₁ * (setup.cardX : ℝ)) from by ring]
  exact (le_div_iff₀ hc₁X_pos).mpr hkey

end ProjectionTheory
