/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Atlas.DifferentialAnalysis.code.LaplacianExistence

noncomputable section

open scoped SchwartzMap
open Filter Topology MeasureTheory

namespace PoissonEquation

variable (n : ℕ)

/-- A smooth `ℂ`-valued function on `ℝⁿ` whose iterated derivatives of every order decay to zero at infinity (i.e. tend to `0` along the cocompact filter). -/
structure SmoothZeroAtInfty where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  smooth' : ContDiff ℝ (⊤ : ℕ∞) toFun
  zero_at_infty' : ∀ m : ℕ,
    Tendsto (fun x => ‖iteratedFDeriv ℝ m toFun x‖) (cocompact _) (𝓝 0)

namespace SmoothZeroAtInfty

variable {n}

/-- Treat `SmoothZeroAtInfty n` as a `FunLike` so that an element can be applied like a function. -/
instance : FunLike (SmoothZeroAtInfty n) (EuclideanSpace ℝ (Fin n)) ℂ where
  coe := SmoothZeroAtInfty.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- Pointwise extensionality for `SmoothZeroAtInfty`. -/
@[ext]
theorem ext {f g : SmoothZeroAtInfty n} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.coe_injective (funext h)

/-- An element of `SmoothZeroAtInfty n` is `C^∞` smooth. -/
theorem smooth (f : SmoothZeroAtInfty n) : ContDiff ℝ (⊤ : ℕ∞) (⇑f) := f.smooth'

/-- The `m`-th iterated derivative norm of `f : SmoothZeroAtInfty n` tends to `0` at infinity. -/
theorem zero_at_infty (f : SmoothZeroAtInfty n) (m : ℕ) :
    Tendsto (fun x => ‖iteratedFDeriv ℝ m (⇑f) x‖) (cocompact _) (𝓝 0) :=
  f.zero_at_infty' m

end SmoothZeroAtInfty

/-- `IsLaplacianOf n f g` says that `g = -Δ f` pointwise, where `Δ` is the standard Laplacian on `ℝⁿ` defined via the iterated Fréchet derivative. -/
def IsLaplacianOf (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    g x = -∑ j : Fin n,
      (iteratedFDeriv ℝ 2 f x) (fun _ => EuclideanSpace.single j (1 : ℝ))













end PoissonEquation

end
