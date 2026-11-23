/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
set_option maxHeartbeats 800000

open MeasureTheory Real Finset

noncomputable section

namespace TalagrandWeightedCertificates

variable {n : ℕ} {Ω : Fin n → Type*}

/-- The weighted Hamming distance between $x$ and $y$ with weights $α$:
$d_α(x, y) = \sum_{i : x_i \neq y_i} α_i$. -/
def weightedHammingDist [∀ i, DecidableEq (Ω i)]
    (α : Fin n → ℝ) (x y : (i : Fin n) → Ω i) : ℝ :=
  ∑ i : Fin n, if x i = y i then 0 else α i

/-- The Euclidean ($ℓ^2$) norm of the weight vector $α$:
$\|α\|_2 = \sqrt{\sum_i α_i^2}$. -/
def eucNorm (α : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, α i ^ 2)

/-- The weighted Hamming distance from $x$ to a set $A$:
$d_α(x, A) = \inf_{y \in A} d_α(x, y)$. -/
def weightedDistToSet [∀ i, DecidableEq (Ω i)]
    (α : Fin n → ℝ) (x : (i : Fin n) → Ω i)
    (A : Set ((i : Fin n) → Ω i)) : ℝ :=
  sInf (Set.image (weightedHammingDist α x) A)

/-- Talagrand's convex distance from $x$ to $A$, defined as the supremum of the
weighted distances $d_α(x, A)$ over all unit-norm weight vectors:
$d_T(x, A) = \sup_{\|α\|_2 = 1} d_α(x, A)$. -/
def convexDist [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) : ℝ :=
  sSup (Set.image (fun α => weightedDistToSet α x A) {α | eucNorm α = 1})

/-- The function $f$ admits weighted certificates with constant $K$: for every $x$
there exist nonnegative weights $α(x)$ with $\|α(x)\|_2 \leq K/2$ such that for all
$y$, $f(y) \geq f(x) - \sum_{i : x_i \neq y_i} α_i(x)$. -/
def HasWeightedCertificates [∀ i, DecidableEq (Ω i)]
    (f : ((i : Fin n) → Ω i) → ℝ) (K : ℝ) : Prop :=
  ∀ x, ∃ α : Fin n → ℝ,
    (∀ i, 0 ≤ α i) ∧
    eucNorm α ≤ K / 2 ∧
    ∀ y, f y ≥ f x - weightedHammingDist α x y



/-- Combining the two one-sided product bounds with the median property
$\mathbb{P}(f \leq m), \mathbb{P}(f \geq m) \geq 1/2$ yields the two-sided
tail bound $\mathbb{P}(f \geq m+t) + \mathbb{P}(f \leq m-t) \leq 4 e^{-t^2 / K^2}$. -/
theorem median_argument
    (prob_le_m prob_ge_mt prob_le_mt prob_ge_m : ℝ)
    (K t : ℝ)
    (hprod1 : prob_le_m * prob_ge_mt ≤ Real.exp (-(t ^ 2) / K ^ 2))
    (hprod2 : prob_le_mt * prob_ge_m ≤ Real.exp (-(t ^ 2) / K ^ 2))
    (hmed_le : prob_le_m ≥ 1 / 2)
    (hmed_ge : prob_ge_m ≥ 1 / 2) :
    prob_ge_mt + prob_le_mt ≤ 4 * Real.exp (-(t ^ 2) / K ^ 2) := by
  have hexp_pos := Real.exp_pos (-(t ^ 2) / K ^ 2)
  have h2 : prob_ge_mt ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) := by nlinarith
  have h4 : prob_le_mt ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) := by nlinarith
  linarith


end TalagrandWeightedCertificates
