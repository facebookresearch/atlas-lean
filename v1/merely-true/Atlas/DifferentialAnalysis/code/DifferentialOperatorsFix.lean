/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.Support

open scoped SchwartzMap Topology
open MeasureTheory Distribution Set

noncomputable section

namespace Distribution

section SingularSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E]

/-- A tempered distribution `u` is smooth on the set `s` iff its action on test functions supported
in `s` is given by integration against a globally smooth function `g`. -/
def IsSmoothOn' (u : 𝓢'(E, ℂ)) (s : Set E) : Prop :=
  ∃ g : E → ℂ, ContDiff ℝ ⊤ g ∧
    ∀ φ : 𝓢(E, ℂ), tsupport φ ⊆ s → u φ = ∫ x, φ x • g x

/-- The singular support of a tempered distribution `u`: the complement of the largest open set on
which `u` is smooth. -/
def singSupp (u : 𝓢'(E, ℂ)) : Set E :=
  (⋃₀ {s : Set E | IsOpen s ∧ IsSmoothOn' u s})ᶜ

/-- The complement of the singular support equals the union of all open sets on which `u` is
smooth. -/
theorem singSupp_compl_eq {u : 𝓢'(E, ℂ)} :
    (singSupp u)ᶜ = ⋃₀ {s : Set E | IsOpen s ∧ IsSmoothOn' u s} := by
  simp [singSupp]

/-- A point `x` is not in the singular support iff there exists an open neighborhood of `x` on
which `u` is smooth. -/
theorem notMem_singSupp_iff {u : 𝓢'(E, ℂ)} {x : E} :
    x ∉ singSupp u ↔ ∃ s : Set E, IsOpen s ∧ IsSmoothOn' u s ∧ x ∈ s := by
  simp [← mem_compl_iff, singSupp_compl_eq, mem_sUnion, and_assoc]

end SingularSupport

end Distribution

end
