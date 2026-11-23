/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.FourierMultiplier
import Atlas.HighDimensionalStatistics.code.Chapter11.Defs_and_Props

set_option maxHeartbeats 800000

noncomputable section

open scoped SchwartzMap FourierTransform Laplacian BigOperators Pointwise
open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

namespace Chapter11

/-- Shorthand for the Euclidean space `ℝⁿ`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- Evaluate a complex multivariate polynomial at a point of `ℝⁿ` (viewed via the
`WithLp` equivalence). -/
def evalPolyAtRn (n : ℕ) (P : MvPolynomial (Fin n) ℂ) (ξ : Rn n) : ℂ :=
  MvPolynomial.aeval (fun i => (((WithLp.equiv 2 (Fin n → ℝ)) ξ) i : ℂ)) P

/-- Embed `ℝⁿ` into `ℝⁿ⁺¹` by setting the last coordinate to zero. -/
def embedHyperplane (n : ℕ) (x : Rn n) : Rn (n + 1) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm
    (fun i : Fin (n + 1) =>
      if h : (i : ℕ) < n then (WithLp.equiv 2 (Fin n → ℝ) x) ⟨i, h⟩ else 0)

/-- Lift a point `ξ' ∈ ℝⁿ` to `ℝⁿ⁺¹` by appending `t` as the last coordinate. -/
def liftPoint (n : ℕ) (ξ' : Rn n) (t : ℝ) : Rn (n + 1) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm
    (fun i : Fin (n + 1) =>
      if h : (i : ℕ) < n
      then (WithLp.equiv 2 (Fin n → ℝ) ξ') ⟨i, h⟩
      else t)

/-- Trace along the last coordinate: integrate `f : ℝⁿ⁺¹ → ℂ` over the line
`{(ξ', t) : t ∈ ℝ}`. -/
def fourierTrace (n : ℕ) (f : Rn (n + 1) → ℂ) : Rn n → ℂ :=
  fun ξ' => ∫ t : ℝ, f (liftPoint n ξ' t)

/-- The `i`-th standard basis vector in `ℝⁿ`. -/
def stdBasisVec (n : ℕ) (i : Fin n) : Rn n := EuclideanSpace.single i 1

/-- The `k`-fold iterated directional derivative in direction `v` on tempered
distributions. -/
def iterLineDeriv {n : ℕ} (v : Rn n) : ℕ → 𝓢'(Rn n, ℂ) → 𝓢'(Rn n, ℂ)
  | 0 => id
  | k + 1 => fun u => LineDeriv.lineDerivOp v (iterLineDeriv v k u)

/-- The multi-derivative `∂^α = ∂_1^{α₁} ⋯ ∂_n^{αₙ}` of a tempered distribution. -/
def iterMultiDeriv (n : ℕ) (α : Fin n → ℕ) (u : 𝓢'(Rn n, ℂ)) : 𝓢'(Rn n, ℂ) :=
  (Finset.univ.toList.map (fun i => iterLineDeriv (stdBasisVec n i) (α i))).foldl
    (fun acc f => f acc) u

/-- A tempered distribution is `L²`-represented if it acts on Schwartz functions
by pairing with an `L²` function. -/
def IsL2Represented {n : ℕ} (u : 𝓢'(Rn n, ℂ)) : Prop :=
  ∃ f : Rn n → ℂ,
    AEStronglyMeasurable f volume ∧
    Integrable (fun x : Rn n => ‖f x‖ ^ 2) volume ∧
    (∀ φ : 𝓢(Rn n, ℂ), u φ = ∫ x, f x • φ x)

/-- The support of a tempered distribution: the set of points such that no
compactly-supported smooth cutoff vanishes the distribution near them. -/
def DistribSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [(MeasureTheory.volume : Measure E).HasTemperateGrowth]
    (u : 𝓢'(E, ℂ)) : Set E :=
  {x : E | ∀ (φ : E → ℂ), ContDiff ℝ ⊤ φ → HasCompactSupport φ → φ x ≠ 0 →
    ¬(∀ ψ : 𝓢(E, ℂ), (∀ y, y ∉ Function.support φ → ψ y = 0) → u ψ = 0)}

/-- Iterated directional derivative on Schwartz functions in direction `v`. -/
def iterLineDerivSchwartz {n : ℕ} (v : Rn n) : ℕ → 𝓢(Rn n, ℂ) → 𝓢(Rn n, ℂ)
  | 0 => id
  | k + 1 => fun φ => LineDeriv.lineDerivOp v (iterLineDerivSchwartz v k φ)

/-- The multi-derivative `∂^α` on Schwartz functions. -/
def iterMultiDerivSchwartz (n : ℕ) (α : Fin n → ℕ) (φ : 𝓢(Rn n, ℂ)) : 𝓢(Rn n, ℂ) :=
  (Finset.univ.toList.map (fun i => iterLineDerivSchwartz (stdBasisVec n i) (α i))).foldl
    (fun acc f => f acc) φ

/-- Membership in the Sobolev space `H^s`: the Fourier transform is represented by
a function `f` with `(1 + |ξ|²)^s |f|²` integrable. -/
def MemSobolevSpace (n : ℕ) (s : ℝ) (u : 𝓢'(Rn n, ℂ)) : Prop :=
  ∃ f : Rn n → ℂ,
    AEStronglyMeasurable f volume ∧
    (∀ φ : 𝓢(Rn n, ℂ), (𝓕 u) φ = ∫ x, f x • φ x) ∧
    Integrable (fun ξ : Rn n =>
      ((1 + ‖ξ‖ ^ 2 : ℝ) ^ s : ℝ) * ‖f ξ‖ ^ 2) volume

/-- Textbook alias for `MemSobolevSpace` (Sobolev space definition). -/
abbrev def_11_8_sobolev := @MemSobolevSpace

/-- The fractional Laplacian `(-Δ)^{s/2}` defined as the Fourier multiplier with
symbol `(2π|ξ|)^s`. -/
def fractionalLaplacian (n : ℕ) (s : ℝ) : 𝓢'(Rn n, ℂ) →L[ℂ] 𝓢'(Rn n, ℂ) :=
  TemperedDistribution.fourierMultiplierCLM ℂ
    (fun ξ : Rn n => ((2 * Real.pi * ‖ξ‖) ^ s : ℝ) : Rn n → ℂ)

/-- Textbook alias for `fractionalLaplacian`. -/
abbrev def_11_11_fractional_laplacian := @fractionalLaplacian

section Prop_11_15_SingSuppConvolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] [(MeasureTheory.volume : Measure E).HasTemperateGrowth]

/-- A tempered distribution has compact support if it is annihilated by every
Schwartz function vanishing on some fixed compact set. -/
def HasCompactDistribSupport (u : 𝓢'(E, ℂ)) : Prop :=
  ∃ K : Set E, IsCompact K ∧
    ∀ φ : 𝓢(E, ℂ), (∀ x ∈ K, φ x = 0) → u φ = 0


end Prop_11_15_SingSuppConvolution

section Prop_11_16_HeatEquation

/-- The last coordinate of a point of `ℝⁿ⁺¹` (interpreted as the time variable
for the heat equation). -/
def lastCoord (n : ℕ) (x : Rn (n + 1)) : ℝ :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ) x) (Fin.last n)

/-- The unit vector pointing in the time direction (the last coordinate) of
`ℝⁿ⁺¹`. -/
def timeDir (n : ℕ) : Rn (n + 1) := EuclideanSpace.single (Fin.last n) 1

/-- The `i`-th spatial direction in `ℝⁿ⁺¹` (the first `n` coordinates). -/
def spatialDir (n : ℕ) (i : Fin n) : Rn (n + 1) :=
  EuclideanSpace.single (Fin.castSucc i) 1

/-- The time-derivative operator `∂_t` on tempered distributions over `ℝⁿ⁺¹`. -/
def timeDerivCLM (n : ℕ) : 𝓢'(Rn (n + 1), ℂ) →L[ℂ] 𝓢'(Rn (n + 1), ℂ) :=
  LineDeriv.lineDerivOpCLM ℂ 𝓢'(Rn (n + 1), ℂ) (timeDir n)

/-- The second-order spatial derivative `∂_i²` on tempered distributions. -/
def spatialSecondDerivCLM (n : ℕ) (i : Fin n) :
    𝓢'(Rn (n + 1), ℂ) →L[ℂ] 𝓢'(Rn (n + 1), ℂ) :=
  (LineDeriv.lineDerivOpCLM ℂ 𝓢'(Rn (n + 1), ℂ) (spatialDir n i)).comp
    (LineDeriv.lineDerivOpCLM ℂ 𝓢'(Rn (n + 1), ℂ) (spatialDir n i))

/-- The spatial Laplacian `Δ = ∑_i ∂_i²` acting in the first `n` coordinates. -/
def spatialLaplacianCLM (n : ℕ) : 𝓢'(Rn (n + 1), ℂ) →L[ℂ] 𝓢'(Rn (n + 1), ℂ) :=
  ∑ i : Fin n, spatialSecondDerivCLM n i

/-- The heat operator `∂_t + Δ_x` on tempered distributions over `ℝⁿ⁺¹`. -/
def heatOp (n : ℕ) : 𝓢'(Rn (n + 1), ℂ) →L[ℂ] 𝓢'(Rn (n + 1), ℂ) :=
  timeDerivCLM n + spatialLaplacianCLM n

/-- A tempered distribution has support in the future half-space `{t ≤ -T}` if it
is annihilated by every Schwartz function vanishing there. -/
def HasSupportInFutureHalfSpace (n : ℕ) (T : ℝ) (u : 𝓢'(Rn (n + 1), ℂ)) : Prop :=
  ∀ φ : 𝓢(Rn (n + 1), ℂ),
    (∀ x : Rn (n + 1), lastCoord n x ≥ -T → φ x = 0) → u φ = 0

end Prop_11_16_HeatEquation

/-- The principal symbol operator associated with a polynomial `P` of order `m`,
realised as the Fourier multiplier with symbol the degree-`m` homogeneous component
of `P`. -/
def principalSymbolOp {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (m : ℕ) :
    𝓢'(Rn n, ℂ) →L[ℂ] 𝓢'(Rn n, ℂ) :=
  TemperedDistribution.fourierMultiplierCLM ℂ
    (fun ξ => evalPolyAtRn n (MvPolynomial.homogeneousComponent m P) ξ)


end Chapter11
