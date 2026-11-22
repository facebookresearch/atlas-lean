/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

noncomputable section

open Matrix

namespace MinkowskiVectors

/-- The Minkowski metric on $\mathbb{R}^{1+n}$ in standard coordinates,
$m_{\mu\nu} = \mathrm{diag}(-1, 1, \ldots, 1)$. -/
def minkowskiMetric (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal fun i => if i = 0 then -1 else 1

/-- The Minkowski inner product $m(X, Y) = m_{\alpha\beta} X^\alpha Y^\beta$
for vectors $X, Y \in \mathbb{R}^{1+n}$. -/
def minkowskiInner (n : ℕ) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  dotProduct X (minkowskiMetric n *ᵥ Y)

/-- A vector $X$ is timelike if $m(X, X) < 0$ (Definition 2.0.1). -/
def IsTimelike (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X < 0

/-- A vector $X$ is spacelike if $m(X, X) > 0$ (Definition 2.0.1). -/
def IsSpacelike (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X > 0

/-- A vector $X$ is null if $m(X, X) = 0$ (Definition 2.0.1). -/
def IsNull (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X = 0

/-- A vector is causal if it is timelike or null (Definition 2.0.1). -/
def IsCausal (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  IsTimelike n X ∨ IsNull n X

/-- A vector $X \in \mathbb{R}^{1+n}$ is future-directed if its time-component
$X^0$ is positive (Definition 2.0.2). -/
def IsFutureDirected (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  X 0 > 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is past-directed if its time-component
$X^0$ is negative. -/
def IsPastDirected (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  X 0 < 0

/-- A Lorentz transformation is a linear map preserving the Minkowski metric,
i.e. $\Lambda^T m \Lambda = m$ (Definition 2.1.1). -/
def IsLorentzTransformation (n : ℕ) (Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  Λᵀ * minkowskiMetric n * Λ = minkowskiMetric n

/-- A Lorentz transformation preserves the Minkowski inner product:
$m(\Lambda X, \Lambda Y) = m(X, Y)$. -/
theorem lorentz_preserves_inner {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    (X Y : Fin (n + 1) → ℝ) :
    minkowskiInner n (Λ *ᵥ X) (Λ *ᵥ Y) = minkowskiInner n X Y := by
  simp only [minkowskiInner]
  rw [mulVec_mulVec]
  rw [dotProduct_mulVec (Λ *ᵥ X) (minkowskiMetric n * Λ) Y]
  rw [vecMul_mulVec Λ (minkowskiMetric n * Λ) X]
  rw [← Matrix.mul_assoc, hΛ]
  rw [← dotProduct_mulVec]

/-- Lorentz transformations preserve the timelike character of a vector
(Corollary 2.1.1, timelike case). -/
theorem lorentz_preserves_timelike {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsTimelike n X) :
    IsTimelike n (Λ *ᵥ X) := by
  unfold IsTimelike at *
  rw [lorentz_preserves_inner hΛ]
  exact hX

/-- Lorentz transformations preserve the spacelike character of a vector
(Corollary 2.1.1, spacelike case). -/
theorem lorentz_preserves_spacelike {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsSpacelike n X) :
    IsSpacelike n (Λ *ᵥ X) := by
  unfold IsSpacelike at *
  rw [lorentz_preserves_inner hΛ]
  exact hX

/-- Lorentz transformations preserve the null character of a vector
(Corollary 2.1.1, null case). -/
theorem lorentz_preserves_null {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsNull n X) :
    IsNull n (Λ *ᵥ X) := by
  unfold IsNull at *
  rw [lorentz_preserves_inner hΛ]
  exact hX

/-- Lorentz transformations preserve the causal character of a vector. -/
theorem lorentz_preserves_causal {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsCausal n X) :
    IsCausal n (Λ *ᵥ X) := by
  cases hX with
  | inl h => exact Or.inl (lorentz_preserves_timelike hΛ h)
  | inr h => exact Or.inr (lorentz_preserves_null hΛ h)

/-- Corollary 2.1.1 (packaged): a Lorentz transformation preserves each of
the three causal classifications — timelike, spacelike, and null. -/
theorem lorentz_preserves_causal_character {n : ℕ}
    (Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hΛ : IsLorentzTransformation n Λ)
    (X : Fin (n + 1) → ℝ) :
    (IsTimelike n X → IsTimelike n (Λ *ᵥ X)) ∧
    (IsSpacelike n X → IsSpacelike n (Λ *ᵥ X)) ∧
    (IsNull n X → IsNull n (Λ *ᵥ X)) :=
  ⟨fun h => lorentz_preserves_timelike hΛ h,
   fun h => lorentz_preserves_spacelike hΛ h,
   fun h => lorentz_preserves_null hΛ h⟩

end MinkowskiVectors
