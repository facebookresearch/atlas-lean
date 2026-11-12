/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Compactness.Compact

set_option linter.unusedSectionVars false

open Classical

/-- If $f : X \to X$ is an isometry and the closure of $s$ is compact, then the closure of
$f(s)$ is also compact. -/
lemma isCompact_closure_image_of_isometry
    {X : Type*} [MetricSpace X]
    {f : X → X} (hf : Isometry f) {s : Set X}
    (hs : IsCompact (closure s)) :
    IsCompact (closure (f '' s)) := by
  have h1 : IsCompact (f '' closure s) := hs.image hf.continuous
  have h2 : closure (f '' s) ⊆ closure (f '' closure s) :=
    closure_mono (Set.image_mono subset_closure)
  rw [h1.isClosed.closure_eq] at h2
  exact h1.of_isClosed_subset isClosed_closure h2

section ChamberCompactClosure

variable {E : Type*} [MetricSpace E]
variable {W : Type*} [Group W]
variable (action : W → E → E)

/-- The group action $W \to E \to E$ acts by isometries iff every element $w \in W$ acts as an
isometry of the metric space $E$. -/
def ActsByIsometries : Prop :=
  ∀ w : W, Isometry (action w)

/-- The image $w \cdot S$ of a subset $S \subseteq E$ under the action of $w \in W$. -/
def orbitSet (w : W) (S : Set E) : Set E :=
  action w '' S

variable {action}

/-- Chambers have compact closure under translation: if $\overline{\sigma}$ is compact then so is
$\overline{w \cdot \sigma}$ for every $w \in W$ acting by isometries. -/
lemma chamber_compact_closure
    (hiso : ActsByIsometries action)
    {σ : Set E} (hσ : IsCompact (closure σ))
    (w : W) :
    IsCompact (closure (orbitSet action w σ)) :=
  isCompact_closure_image_of_isometry (hiso w) hσ

/-- The image $w \cdot \sigma$ of a chamber with compact closure is bounded. -/
lemma chamber_isBounded
    (hiso : ActsByIsometries action)
    {σ : Set E} (hσ : IsCompact (closure σ))
    (w : W) :
    Bornology.IsBounded (orbitSet action w σ) :=
  (chamber_compact_closure hiso hσ w).isBounded.subset subset_closure

/-- Isometric translation preserves diameter: $\operatorname{diam}(w \cdot \sigma)
= \operatorname{diam}(\sigma)$. -/
lemma chamber_diam_eq
    (hiso : ActsByIsometries action)
    (σ : Set E) (w : W) :
    Metric.diam (orbitSet action w σ) = Metric.diam σ :=
  (hiso w).diam_image σ

end ChamberCompactClosure
