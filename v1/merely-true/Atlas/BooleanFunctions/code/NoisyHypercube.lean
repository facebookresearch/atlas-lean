/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.FourierExpansion
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

open Finset BigOperators

namespace BooleanFourier

noncomputable def correlatedPairProb (ρ : ℝ) (_hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (a b : Bool) : ℝ :=
  (1 + ρ * (boolToReal a * boolToReal b)) / 2

noncomputable def correlatedProb {n : ℕ} (ρ : ℝ) (_hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (x y : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, (1 + ρ * (boolToReal (x i) * boolToReal (y i))) / 2

lemma correlatedProb_factor_nonneg {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (x y : Fin n → Bool) (i : Fin n) :
    0 ≤ (1 + ρ * (boolToReal (x i) * boolToReal (y i))) / 2 := by
  have hρ0 : (-1 : ℝ) ≤ ρ := hρ.1
  have hρ1 : ρ ≤ 1 := hρ.2
  cases x i <;> cases y i <;> simp [boolToReal] <;> linarith

lemma correlatedProb_factor_sum {n : ℕ} (ρ : ℝ) (x : Fin n → Bool) (i : Fin n) :
    ∑ b : Bool, (1 + ρ * (boolToReal (x i) * boolToReal b)) / 2 = 1 := by
  simp only [Fintype.sum_bool]
  cases x i <;> simp [boolToReal] <;> ring

structure NoisyHypercube where
  n : ℕ
  ρ : ℝ
  hρ_nonneg : 0 ≤ ρ
  hρ_le_one : ρ ≤ 1

noncomputable def noisyHypercubeTransitionProb {n : ℕ} (ρ : ℝ) (_hρ₀ : 0 ≤ ρ) (_hρ₁ : ρ ≤ 1)
    (x y : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, ((1 + ρ * (boolToReal (x i) * boolToReal (y i))) / 2)

noncomputable def NoisyHypercube.transitionProb (G : NoisyHypercube) (x y : Fin G.n → Bool) : ℝ :=
  noisyHypercubeTransitionProb G.ρ G.hρ_nonneg G.hρ_le_one x y

noncomputable def noiseOpProb {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) :
    (Fin n → Bool) → ℝ := fun x =>
  ∑ y : Fin n → Bool,
    (∏ i : Fin n, ((1 + ρ * (boolToReal (x i) * boolToReal (y i))) / 2)) * f y

end BooleanFourier
