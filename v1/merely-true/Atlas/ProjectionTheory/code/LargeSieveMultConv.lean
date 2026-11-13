/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.LinnikLargeSieve
import Atlas.ProjectionTheory.code.MultConvLinftyBound

open Finset Complex BigOperators

noncomputable section

namespace LargeSieveMultConv

/-- Squared $L^2$ norm of a function `f : Fin N → ℂ`: $\sum_n |f(n)|^2$. -/
def l2NormSq {N : ℕ} (f : Fin N → ℂ) : ℝ :=
  ∑ n : Fin N, ‖f n‖ ^ 2

/-- The $L^\infty(\mathbb{Z}_p^*)$ norm of the high-frequency part of the multiplicative
convolution `(π_p f *_M π_p g)_H^*` over the unit group of `ZMod p`. -/
def highFreqProjMulConvLinf (N₁ N₂ : ℕ) (p : ℕ) (hp : Nat.Prime p)
    (f : Fin N₁ → ℂ) (g : Fin N₂ → ℂ) : ℝ :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  ⨆ a : (ZMod p)ˣ,
    ‖HighFreqMultConv.highFreqUnits p
      (HighFreqMultConv.mulConvUnits p
        (fun u => LinnikLargeSieve.modProjection N₁ p f (u : ZMod p))
        (fun u => LinnikLargeSieve.modProjection N₂ p g (u : ZMod p))) a‖

/-- Left-hand side of the large-sieve / multiplicative convolution theorem:
`∑_{p ∈ P_M} ‖(π_p(f *_M g))_h^*‖_{L^∞}^2`. -/
def largeSieveMultConvLHS (N₁ N₂ M : ℕ) (f : Fin N₁ → ℂ) (g : Fin N₂ → ℂ) : ℝ :=
  ∑ p ∈ LinnikLargeSieve.primesInRange M,
    if hp : Nat.Prime p then (highFreqProjMulConvLinf N₁ N₂ p hp f g) ^ 2
    else 0

/-- $L^2$ norm of `f : Fin N → ℂ`: the square root of `l2NormSq f`. -/
def l2Norm {N : ℕ} (f : Fin N → ℂ) : ℝ :=
  Real.sqrt (l2NormSq f)

end LargeSieveMultConv

end



noncomputable section

open Finset BigOperators


end
