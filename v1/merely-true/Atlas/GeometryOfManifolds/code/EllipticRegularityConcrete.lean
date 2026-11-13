/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false

namespace EllipticRegularityConcrete


/-- A differential $k$-form on $\mathbb{R}^n$: a map from $\mathbb{R}^n$ to the space of
continuous alternating $k$-multilinear forms on $\mathbb{R}^n$. -/
def DiffForm (n k : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ

/-- Pointwise addition gives `DiffForm n k` the structure of an additive abelian group. -/
noncomputable instance instAddCommGroup (n k : ℕ) : AddCommGroup (DiffForm n k) :=
  Pi.addCommGroup

/-- Pointwise scalar multiplication gives `DiffForm n k` the structure of an $\mathbb{R}$-module. -/
noncomputable instance instModule (n k : ℕ) : Module ℝ (DiffForm n k) :=
  Pi.module _ _ _


/-- A differential form is smooth ($C^\infty$) when its coefficient map is infinitely
differentiable as a function $\mathbb{R}^n \to (\mathbb{R}^n)^{[\Lambda^k]\to \mathbb{R}}$. -/
def IsSmoothForm {n k : ℕ} (ξ : DiffForm n k) : Prop :=
  ContDiff ℝ ⊤ ξ

/-- Smoothness is preserved under subtraction: $a, b \in C^\infty \Rightarrow a - b \in C^\infty$. -/
theorem isSmoothForm_sub {n k : ℕ} (a b : DiffForm n k)
    (ha : IsSmoothForm a) (hb : IsSmoothForm b) : IsSmoothForm (a - b) :=
  ha.sub hb


/-- A family of nonnegative Sobolev seminorms indexed by regularity index $s \in \mathbb{N}$,
acting on differential $(k+1)$-forms. -/
structure SobolevNorms (n k : ℕ) where
  norm : ℕ → DiffForm n (k + 1) → ℝ
  norm_nonneg : ∀ (s : ℕ) (ξ : DiffForm n (k + 1)), 0 ≤ norm s ξ

/-- The form $\xi$ has Sobolev regularity of order $s$ when $\|\xi\|_s$ is bounded by some
constant. (Trivially holds in this framework but records the membership in $H^s$ qualitatively.) -/
def HasSobolevRegularity {n k : ℕ} (snorms : SobolevNorms n k) (s : ℕ)
    (ξ : DiffForm n (k + 1)) : Prop :=
  ∃ (C : ℝ), snorms.norm s ξ ≤ C


/-- A smoothing (regularity-improving) operator: it gains one derivative in the Sobolev
scale and maps anything with finite Sobolev regularity into the smooth class $C^\infty$. -/
structure IsSmoothingOperator {n k : ℕ} (snorms : SobolevNorms n k)
    (S : DiffForm n (k + 1) → DiffForm n (k + 1)) where
  regularity_gain : ∀ (s : ℕ), ∃ (C : ℝ), C > 0 ∧
    ∀ (ξ : DiffForm n (k + 1)), snorms.norm (s + 1) (S ξ) ≤ C * snorms.norm s ξ
  maps_to_smooth : ∀ (s : ℕ) (ξ : DiffForm n (k + 1)),
    HasSobolevRegularity snorms s ξ → IsSmoothForm (S ξ)


/-- A concrete parametrix for an elliptic operator $L$: an approximate inverse $P$ with
$P \circ L = \mathrm{Id} + S$ for a smoothing remainder $S$. This is the key analytic input
for the elliptic regularity theorem $L\xi \in C^\infty \Rightarrow \xi \in C^\infty$. -/
structure ConcreteParametrix {n : ℕ} (k : ℕ)
    (L : DiffForm n (k + 1) → DiffForm n (k + 1)) where
  P : DiffForm n (k + 1) → DiffForm n (k + 1)
  S_left : DiffForm n (k + 1) → DiffForm n (k + 1)
  sobolevNorms : SobolevNorms n k
  PL_eq : ∀ (ξ : DiffForm n (k + 1)), P (L ξ) = ξ + S_left ξ
  S_left_smoothing : IsSmoothingOperator sobolevNorms S_left


end EllipticRegularityConcrete
