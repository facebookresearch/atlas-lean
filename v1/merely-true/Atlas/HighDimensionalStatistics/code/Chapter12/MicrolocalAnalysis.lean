/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution

set_option maxHeartbeats 800000

noncomputable section

open scoped SchwartzMap FourierTransform Pointwise
open MeasureTheory Set Filter

variable {n : ℕ}

namespace Chapter12

/-- Shorthand for the Euclidean space `ℝⁿ`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `f` is homogeneous of degree `k` outside the unit ball: for `t > 0` and
`‖x‖ ≥ 1`, `f(tx) = t^k f(x)`. -/
def IsHomogeneousOutside (f : Rn n → ℂ) (k : ℤ) : Prop :=
  ∀ (t : ℝ) (x : Rn n), 0 < t → 1 ≤ ‖x‖ → f (t • x) = (t : ℂ) ^ k * f x

/-- `Γ` is a cone if it is invariant under positive scalar multiplication. -/
def IsCone (Γ : Set (Rn n)) : Prop :=
  ∀ (t : ℝ) (ξ : Rn n), 0 < t → ξ ∈ Γ → t • ξ ∈ Γ

/-- `g` is rapidly decreasing: for every `N` there is a constant `C` with
`‖g ξ‖ ≤ C (1 + ‖ξ‖)⁻ᴺ`. -/
def IsRapidlyDecreasing (g : Rn n → ℂ) : Prop :=
  ∀ (N : ℕ), ∃ (C : ℝ), 0 < C ∧ ∀ (ξ : Rn n), ‖g ξ‖ ≤ C * (1 + ‖ξ‖)⁻¹ ^ N

/-- `f` is homogeneous of degree zero away from the origin: `f(tx) = f(x)` for
`t > 0` and `x ≠ 0`. -/
def IsHomogeneousDegZero (f : Rn n → ℂ) : Prop :=
  ∀ (t : ℝ) (x : Rn n), 0 < t → x ≠ 0 → f (t • x) = f x

/-- The conic support of `u`: nonzero directions `ξ` such that every smooth
conic-cutoff with `φ(ξ) ≠ 0` produces a nonzero distribution `φ u`. -/
def ConeSupport (n : ℕ) (u : 𝓢'(Rn n, ℂ)) : Set (Rn n) :=
  {ξ : Rn n | ξ ≠ 0 ∧
    ∀ (φ : Rn n → ℂ), ContDiff ℝ ⊤ φ → IsHomogeneousOutside φ 0 → φ ξ ≠ 0 →
      TemperedDistribution.smulLeftCLM ℂ φ u ≠ 0}

/-- The conic singular support of `u`: nonzero directions `ξ` such that no
conic-cutoff with `φ(ξ) ≠ 0` makes `φ u` Schwartz. -/
def ConeSingularSupport (n : ℕ) (u : 𝓢'(Rn n, ℂ)) : Set (Rn n) :=
  {ξ : Rn n | ξ ≠ 0 ∧
    ∀ (φ : Rn n → ℂ), ContDiff ℝ ⊤ φ → IsHomogeneousOutside φ 0 → φ ξ ≠ 0 →
      TemperedDistribution.smulLeftCLM ℂ φ u ∉
        Set.range (SchwartzMap.toTemperedDistributionCLM (Rn n) ℂ)}

/-- Textbook alias for `ConeSupport` (Definition 12.2). -/
abbrev def_12_2_cone_support := @ConeSupport

/-- Textbook alias for `ConeSingularSupport` (Definition 12.2). -/
abbrev def_12_2_cone_singular_support := @ConeSingularSupport


/-- `v` is given by a conic cutoff: there is a smooth function `ψ_R` homogeneous
of degree zero outside the unit ball such that `v` integrates against it. -/
def IsConicCutoff (n : ℕ) (v : 𝓢'(Rn n, ℂ)) : Prop :=
  ∃ (ψ_R : Rn n → ℂ), ContDiff ℝ ⊤ ψ_R ∧ IsHomogeneousOutside ψ_R 0 ∧
    ∀ (f : 𝓢(Rn n, ℂ)), v f = ∫ x, f x • (ψ_R x : ℂ)

/-- The wavefront set `WF(u)`: pairs `(x, ξ)` with `ξ ≠ 0` such that, for every
compactly-supported smooth cutoff `φ` with `φ(x) ≠ 0`, the direction `ξ` lies in
the conic singular support of `φ u`. -/
def WavefrontSet (n : ℕ) (u : 𝓢'(Rn n, ℂ)) : Set (Rn n × Rn n) :=
  {p : Rn n × Rn n | p.2 ≠ 0 ∧
    ∀ (φ : Rn n → ℂ), ContDiff ℝ ⊤ φ → HasCompactSupport φ → φ p.1 ≠ 0 →
      p.2 ∈ ConeSingularSupport n (TemperedDistribution.smulLeftCLM ℂ φ u)}

/-- The scattering wavefront set `WF_sc(u)`: the usual wavefront set together
with pairs `(x, ξ)` of nonzero `x, ξ` such that every conic-cutoff `ψ` with
`ψ(x) ≠ 0` places `ξ` in the conic singular support of `ψ u`. -/
def ScatteringWavefrontSet (n : ℕ) (u : 𝓢'(Rn n, ℂ)) : Set (Rn n × Rn n) :=
  WavefrontSet n u ∪
    {p : Rn n × Rn n | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧
      ∀ (ψ : Rn n → ℂ), ContDiff ℝ ⊤ ψ → IsHomogeneousOutside ψ 0 → ψ p.1 ≠ 0 →
        p.2 ∈ ConeSingularSupport n (TemperedDistribution.smulLeftCLM ℂ ψ u)}

/-- Textbook alias for `WavefrontSet` (Definition 12.12). -/
abbrev def_12_12_wavefront_set := @WavefrontSet

/-- Textbook alias for `ScatteringWavefrontSet` (Definition 12.12). -/
abbrev def_12_12_scattering_wavefront_set := @ScatteringWavefrontSet

/-- The singular support of a tempered distribution on `ℝⁿ`. -/
def SingularSupport (n : ℕ) (u : 𝓢'(Rn n, ℂ)) : Set (Rn n) :=
  {x : Rn n |
    ∀ (φ : Rn n → ℂ), ContDiff ℝ ⊤ φ → HasCompactSupport φ → φ x ≠ 0 →
      TemperedDistribution.smulLeftCLM ℂ φ u ∉
        Set.range (SchwartzMap.toTemperedDistributionCLM (Rn n) ℂ)}


/-- The closed unit ball in `ℝⁿ`. -/
def closedUnitBall (n : ℕ) : Set (Rn n) := Metric.closedBall 0 1

/-- The unit sphere in `ℝⁿ`. -/
def unitSphere (n : ℕ) : Set (Rn n) := Metric.sphere 0 1

/-- Compatibility condition between `WF_sc(u)` and `WF_sc(v)` required for the
product distribution `u · v` to be defined in the scattering calculus. -/
def ProductWFscCondition (n : ℕ) (u v : 𝓢'(Rn n, ℂ)) : Prop :=
  ∀ (p ω : Rn n),
    (p, ω) ∈ ScatteringWavefrontSet n u →
    p ∈ closedUnitBall n →
    ω ∈ unitSphere n →
    (p, -ω) ∉ ScatteringWavefrontSet n v

/-- Compatibility condition between `WF_sc(u)` and `WF_sc(v)` required for the
convolution `u * v` to be defined in the scattering calculus. -/
def ConvolutionWFscCondition (n : ℕ) (u v : 𝓢'(Rn n, ℂ)) : Prop :=
  ∀ (θ q : Rn n),
    (θ, q) ∈ ScatteringWavefrontSet n u →
    θ ∈ unitSphere n →
    q ∈ closedUnitBall n →
    (-θ, q) ∉ ScatteringWavefrontSet n v





end Chapter12

end
