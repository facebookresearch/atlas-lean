/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

namespace MeasureTheory

open MeasureTheory Finset

/-- The running maximum of `|f k ω|` over `0 ≤ k ≤ n`, i.e.
`maxProcess f n ω = max_{0 ≤ k ≤ n} |f k ω|`. -/
noncomputable def maxProcess {Ω : Type*} (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun k => |f k ω|)

/-- The **predictable quadratic variation** of `f` with respect to `ℱ` and `μ`,
defined pointwise by
`A_n(ω) = ∑_{k=0}^{n-1} E[(f_{k+1} - f_k)² | ℱ_k] (ω)`. -/
noncomputable def predictableQuadraticVariation {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) (ℱ : Filtration ℕ m0) (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range n).sum (fun k =>
    (condExp (ℱ k) μ (fun ω' => (f (k + 1) ω' - f k ω') ^ 2)) ω)



end MeasureTheory
