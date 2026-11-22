/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Distribution.Support
import Mathlib.Algebra.MvPolynomial.Eval
import Atlas.DifferentialAnalysis.code.DifferentialOperators

open scoped SchwartzMap
open TemperedDistribution MvPolynomial Filter Topology

noncomputable section

namespace DifferentialOperators

variable {n : ℕ}

section Prop_11_2

variable {ι : Type*}

/-- Weak-* continuity of scalar multiplication on tempered distributions (Proposition 11.1
of Melrose, scalar part): if `u j → u₀` along the filter `p` then `c · u j → c · u₀`. -/
theorem prop_11_2_smul {p : Filter ι}
    {u : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {u₀ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (hu : Tendsto u p (𝓝 u₀)) (c : ℂ) :
    Tendsto (fun j => c • u j) p (𝓝 (c • u₀)) :=
  ((continuous_const_smul c).tendsto _).comp hu

/-- Weak-* continuity of addition on tempered distributions: if `u j → u₀` and `u' j → u₀'`,
then `(u j + u' j) → (u₀ + u₀')`. -/
theorem prop_11_2_add {p : Filter ι}
    {u u' : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {u₀ u₀' : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (hu : Tendsto u p (𝓝 u₀)) (hu' : Tendsto u' p (𝓝 u₀')) :
    Tendsto (fun j => u j + u' j) p (𝓝 (u₀ + u₀')) :=
  hu.add hu'

/-- Weak-* continuity of constant-coefficient differential operators: if `u j → u₀`, then
`P(D) u j → P(D) u₀` for every polynomial `P`. -/
theorem prop_11_2_diffOp {p : Filter ι}
    {u : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {u₀ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (hu : Tendsto u p (𝓝 u₀)) (P : MvPolynomial (Fin n) ℂ) :
    Tendsto (fun j => constCoeffDiffOp n P (u j)) p
      (𝓝 (constCoeffDiffOp n P u₀)) :=
  ((constCoeffDiffOp n P).continuous.tendsto _).comp hu

/-- Weak-* continuity of multiplication by a fixed smooth function: if `u j → u₀`, then
`g · u j → g · u₀` as tempered distributions, for any (admissible) function `g`. -/
theorem prop_11_2_smulLeft {p : Filter ι}
    {u : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {u₀ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (hu : Tendsto u p (𝓝 u₀)) (g : EuclideanSpace ℝ (Fin n) → ℂ) :
    Tendsto (fun j => TemperedDistribution.smulLeftCLM ℂ g (u j)) p
      (𝓝 (TemperedDistribution.smulLeftCLM ℂ g u₀)) :=
  ((TemperedDistribution.smulLeftCLM ℂ g).continuous.tendsto _).comp hu

/-- Proposition 11.1 of Melrose (combined): weak-* convergence of tempered distributions is
preserved under all the standard operations — scalar multiplication, addition, application of
a constant-coefficient differential operator, and multiplication by a function. -/
theorem proposition_11_2_combined {p : Filter ι}
    {u u' : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {u₀ u₀' : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (hu : Tendsto u p (𝓝 u₀)) (hu' : Tendsto u' p (𝓝 u₀'))
    (c : ℂ) (P : MvPolynomial (Fin n) ℂ) (g : EuclideanSpace ℝ (Fin n) → ℂ) :
    Tendsto (fun j => c • u j) p (𝓝 (c • u₀)) ∧
    Tendsto (fun j => u j + u' j) p (𝓝 (u₀ + u₀')) ∧
    Tendsto (fun j => constCoeffDiffOp n P (u j)) p (𝓝 (constCoeffDiffOp n P u₀)) ∧
    Tendsto (fun j => TemperedDistribution.smulLeftCLM ℂ g (u j)) p
      (𝓝 (TemperedDistribution.smulLeftCLM ℂ g u₀)) :=
  ⟨prop_11_2_smul hu c, prop_11_2_add hu hu', prop_11_2_diffOp hu P, prop_11_2_smulLeft hu g⟩

end Prop_11_2

end DifferentialOperators

end
