/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.SobolevEmbedding
import Atlas.DifferentialAnalysis.code.WeightedSobolevSchwartz

open MeasureTheory Filter Topology
open scoped ZeroAtInfty

noncomputable section

namespace SchwartzWeightedSobolev

/-- The `k`-th weighted Sobolev space on `ℝⁿ`: a structure recording an
underlying Sobolev representative, used to model functions `f` such that
`⟨x⟩^k · f ∈ H^k`. -/
structure WeightedSobolevSpace (n : ℕ) (k : ℕ) where
  witness : SobolevEmbedding.SobolevSpace n k

/-- The underlying function of a `WeightedSobolevSpace n k` element: divide
the Sobolev witness by `⟨x⟩^k` so that the witness's `Hᵏ` regularity
translates into pointwise `⟨x⟩^k`-decay of the original function. -/
def WeightedSobolevSpace.toFun {n k : ℕ} (u : WeightedSobolevSpace n k)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (↑(TestFunctions.japaneseBracket n x ^ k))⁻¹ * u.witness.toFun x

/-- Coercion that lets an element of `WeightedSobolevSpace n k` be applied as
a function `EuclideanSpace ℝ (Fin n) → ℂ`. -/
instance {n k : ℕ} : CoeFun (WeightedSobolevSpace n k)
    (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨WeightedSobolevSpace.toFun⟩

/-- Bundle of a function lying in every weighted Sobolev space, with a
consistent family of weighted Sobolev witnesses. -/
structure MemAllWeightedSobolev (n : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  mem_weighted (k : ℕ) : WeightedSobolevSpace n k
  consistent (k : ℕ) :
    ∀ x, toFun x = WeightedSobolevSpace.toFun (mem_weighted k) x

/-- Coercion that lets an element of `MemAllWeightedSobolev n` be applied as
a function `EuclideanSpace ℝ (Fin n) → ℂ`. -/
instance {n : ℕ} : CoeFun (MemAllWeightedSobolev n)
    (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨MemAllWeightedSobolev.toFun⟩








/-- A function `f : ℝⁿ → ℂ` is Schwartz if it arises as the underlying
function of some element of `SchwartzTestFunctionSpace n`. -/
@[simp]

def IsSchwartz (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∃ u : TestFunctions.SchwartzTestFunctionSpace n, u.toFun = f

/-- A function `f : ℝⁿ → ℂ` lies in every weighted Sobolev space if it arises
as the underlying function of some `MemAllWeightedSobolev n`. -/
def IsInAllWeightedSobolev (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∃ w : MemAllWeightedSobolev n, w.toFun = f

end SchwartzWeightedSobolev
