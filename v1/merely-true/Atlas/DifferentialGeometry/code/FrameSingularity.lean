/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

namespace FrameSingularity

open Real Complex

def angularCoord (p : ℝ × ℝ) : ℝ :=
  Complex.arg (⟨p.1, p.2⟩ : ℂ)

structure IsOrthonormalTangentFrame
    (f : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
    (X : ℝ × ℝ → Fin 2 → EuclideanSpace ℝ (Fin 3))
    (S : Set (ℝ × ℝ)) : Prop where
  tangent : ∀ p ∈ S, ∀ i : Fin 2, ∃ (a b : ℝ),
    X p i = a • (fderiv ℝ f p (1, 0)) + b • (fderiv ℝ f p (0, 1))
  orthonormal : ∀ p ∈ S, ∀ i j : Fin 2,
    @inner ℝ _ _ (X p i) (X p j) = if i = j then (1 : ℝ) else (0 : ℝ)

structure HasFrameSingularity (m : ℤ)
    (X : ℝ × ℝ → Fin 2 → EuclideanSpace ℝ (Fin 3))
    (U : Set (ℝ × ℝ)) where
  f : ℝ × ℝ → EuclideanSpace ℝ (Fin 3)
  f_smooth : ContDiffOn ℝ ⊤ f U
  f_immersion : ∀ p ∈ U, Function.Injective (fderiv ℝ f p)
  hU : (0, 0) ∈ U
  frame_tangent : IsOrthonormalTangentFrame f X (U \ {(0, 0)})
  smoothFrame : ℝ × ℝ → Fin 2 → EuclideanSpace ℝ (Fin 3)
  smooth_extends : ContDiffOn ℝ ⊤ (fun p => (smoothFrame p 0, smoothFrame p 1)) U
  smoothFrame_tangent : IsOrthonormalTangentFrame f smoothFrame U
  rotation_eq_fst : ∀ p ∈ U \ {(0, 0)},
    let θ := angularCoord p
    X p 0 = (Real.cos (m * θ)) • (smoothFrame p 0) -
             (Real.sin (m * θ)) • (smoothFrame p 1)
  rotation_eq_snd : ∀ p ∈ U \ {(0, 0)},
    let θ := angularCoord p
    X p 1 = (Real.sin (m * θ)) • (smoothFrame p 0) +
             (Real.cos (m * θ)) • (smoothFrame p 1)

def dTheta (p : ℝ × ℝ) : ℝ × ℝ :=
  (-(p.2) / (p.1 ^ 2 + p.2 ^ 2), p.1 / (p.1 ^ 2 + p.2 ^ 2))

open Filter Topology MeasureTheory

def circleIntegral1Form (α : ℝ × ℝ → ℝ × ℝ) (ρ : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..(2 * π),
    let p := (ρ * Real.cos t, ρ * Real.sin t)
    let tangent := (-ρ * Real.sin t, ρ * Real.cos t)
    (α p).1 * tangent.1 + (α p).2 * tangent.2

end FrameSingularity

end

namespace FrameSingularity

open Real Filter Topology



end FrameSingularity
