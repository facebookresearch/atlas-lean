/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Filter Topology

/-- A real function `f` is differentiable at `c` if and only if the difference quotient
`(f x - f c) / (x - c)` has a limit as `x → c` with `x ≠ c`. -/
theorem differentiable_at_iff_limit_exists (f : ℝ → ℝ) (c : ℝ) :
    DifferentiableAt ℝ f c ↔
    ∃ L : ℝ, Filter.Tendsto (fun x => (f x - f c) / (x - c)) (nhdsWithin c {c}ᶜ) (nhds L) := by
  constructor
  · intro hd
    exact ⟨deriv f c, by rw [show (fun x => (f x - f c) / (x - c)) = slope f c from
      (slope_fun_def_field f c).symm]; exact hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt⟩
  · rintro ⟨L, hL⟩
    have hslope : Filter.Tendsto (slope f c) (nhdsWithin c {c}ᶜ) (nhds L) := by
      rwa [show (fun x => (f x - f c) / (x - c)) = slope f c from
        (slope_fun_def_field f c).symm] at hL
    exact (hasDerivAt_iff_tendsto_slope.mpr hslope).differentiableAt

/-- Chain rule: if `g` is differentiable at `c` and `f` is differentiable at `g c`,
then the composition `f ∘ g` is differentiable at `c` and
`(f ∘ g)'(c) = f'(g c) * g'(c)`. -/
theorem chain_rule (f g : ℝ → ℝ) (c : ℝ)
    (hg : DifferentiableAt ℝ g c) (hf : DifferentiableAt ℝ f (g c)) :
    DifferentiableAt ℝ (f ∘ g) c ∧ deriv (f ∘ g) c = deriv f (g c) * deriv g c :=
  ⟨hf.comp c hg, deriv_comp c hf hg⟩
