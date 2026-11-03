/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.Isogenies

open Polynomial

open scoped Polynomial.Bivariate

universe u

namespace CurveMorphism

variable {k : Type u} [Field k]

open ProjectiveCurve

/-- Predicate asserting that a function field element `φ` on the affine curve
defined by `f₀` is regular and nonzero at an affine point `P` over an extension `K`:
there is a representation `φ = g / h` with both `h(P)` and `g(P)` nonzero. -/
def IsRegularNonzeroAtOver {f₀ : k[X][Y]} {K : Type u}
    [Field K] [Algebra k K]
    (φ : FunctionField f₀) (P : AffinePointOver f₀ K) : Prop :=
  ∃ (g : CoordinateRing f₀) (h : ↥(nonZeroDivisors (CoordinateRing f₀))),
    φ = IsLocalization.mk' (FunctionField f₀) g h ∧
    P.evalRingHom (h : CoordinateRing f₀) ≠ 0 ∧
    P.evalRingHom g ≠ 0

/-- Predicate asserting that the projective rational map `φ` from the curve `f₁`
to the curve `f₂` is regular at an affine point `P`: there exists a nonzero common
scaling `μ` so that all three coordinate components are regular at `P` and at least
one is nonzero (so the resulting projective point is well-defined). -/
def IsRegularAtOver {f₁ f₂ : k[X][Y]}
    [IsDomain (CoordinateRing f₁)]
    (φ : ProjectiveCurve.RationalMap f₁ f₂) {K : Type u} [Field K] [Algebra k K]
    (P : AffinePointOver f₁ K) : Prop :=
  ∃ (μ : FunctionField f₁), μ ≠ 0 ∧
    (μ * φ.φ₁).IsRegularAtOver P ∧
    (μ * φ.φ₂).IsRegularAtOver P ∧
    (μ * φ.φ₃).IsRegularAtOver P ∧
    (IsRegularNonzeroAtOver (μ * φ.φ₁) P ∨
     IsRegularNonzeroAtOver (μ * φ.φ₂) P ∨
     IsRegularNonzeroAtOver (μ * φ.φ₃) P)

/-- The type of `K`-points of the projective curve cut out by `f₀`, encoded as
either an affine point or a point at infinity given by projective coordinates
`(a : b : 0)` with `(a, b)` not both zero. -/
inductive ProjectiveCurvePointOver (f₀ : k[X][Y]) (K : Type u) [Field K] [Algebra k K]
  |     affine : AffinePointOver f₀ K → ProjectiveCurvePointOver f₀ K
  |     atInfinity : (a : K) → (b : K) → (a ≠ 0 ∨ b ≠ 0) →
      ProjectiveCurvePointOver f₀ K

/-- Predicate asserting that the rational map `φ` is regular at a projective
point `P`, defined by cases: at an affine point we use `IsRegularAtOver`, and at
a point at infinity we ask for a common denominator whose numerators are not all
zero. -/
def IsRegularAtProjectivePoint {f₁ f₂ : k[X][Y]}
    [IsDomain (CoordinateRing f₁)]
    (φ : ProjectiveCurve.RationalMap f₁ f₂) {K : Type u} [Field K] [Algebra k K]
    (P : ProjectiveCurvePointOver f₁ K) : Prop :=
  match P with
  | .affine Q => IsRegularAtOver φ Q
  | .atInfinity _a _b _hab =>


    ∃ (g₁ g₂ g₃ : CoordinateRing f₁)
      (h : ↥(nonZeroDivisors (CoordinateRing f₁))),
      (∃ (μ : FunctionField f₁), μ ≠ 0 ∧
        μ * φ.φ₁ = IsLocalization.mk' (FunctionField f₁) g₁ h ∧
        μ * φ.φ₂ = IsLocalization.mk' (FunctionField f₁) g₂ h ∧
        μ * φ.φ₃ = IsLocalization.mk' (FunctionField f₁) g₃ h) ∧

      (g₁ ≠ 0 ∨ g₂ ≠ 0 ∨ g₃ ≠ 0)

/-- `IsMorphism φ` says the rational map `φ` is everywhere defined, i.e. regular
at every projective point over every algebraically closed extension of `k`. This
matches Definition 4.14: a rational map that is defined everywhere is called a
morphism. -/
def IsMorphism {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]
    (φ : ProjectiveCurve.RationalMap f₁ f₂) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
    ∀ P : ProjectiveCurvePointOver f₁ K,
      IsRegularAtProjectivePoint φ P

/-- A morphism of projective curves from `f₁` to `f₂`: a rational map together
with a proof that it is regular everywhere. Corresponds to the notion of morphism
of curves in Definition 4.14. -/
structure Morphism (f₁ f₂ : k[X][Y]) [IsDomain (CoordinateRing f₁)] where
  toRationalMap : ProjectiveCurve.RationalMap f₁ f₂
  regular_everywhere : IsMorphism toRationalMap

/-- A `Morphism` is in particular a rational map satisfying the `IsMorphism`
predicate. -/
theorem Morphism.isMorphism {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]
    (φ : Morphism f₁ f₂) : IsMorphism φ.toRationalMap :=
  φ.regular_everywhere

/-- Build a `Morphism` from a rational map together with a proof that it is
regular everywhere. -/
def Morphism.ofIsMorphism {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]
    (φ : ProjectiveCurve.RationalMap f₁ f₂) (h : IsMorphism φ) : Morphism f₁ f₂ :=
  ⟨φ, h⟩

end CurveMorphism
