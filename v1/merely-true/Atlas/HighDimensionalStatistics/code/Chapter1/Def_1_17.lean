/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cover

open Set Metric
open scoped NNReal

/-- **Definition 1.17 (ε-net).** A set `N ⊆ K` is an `ε`-net of `K` with
respect to the metric `d` if every point of `K` is within distance `ε` of some
point of `N`. -/
def IsEpsilonNet {α : Type*} [PseudoMetricSpace α] (K : Set α) (N : Set α) (ε : ℝ) : Prop :=
  N ⊆ K ∧ ∀ z ∈ K, ∃ x ∈ N, dist x z ≤ ε

namespace IsEpsilonNet

variable {α : Type*} [PseudoMetricSpace α] {K N : Set α} {ε : ℝ}

/-- The empty set is trivially an `ε`-net of the empty set, for any `ε`. -/
lemma empty (ε : ℝ) : IsEpsilonNet (∅ : Set α) ∅ ε :=
  ⟨Subset.rfl, fun _ hz => absurd hz (by simp)⟩

/-- Any `ε`-net is contained in the set it covers. -/
lemma subset_set (h : IsEpsilonNet K N ε) : N ⊆ K := h.1

/-- The defining covering property of an `ε`-net: every point of `K` has a
neighbour in `N` within distance `ε`. -/
lemma exists_dist_le (h : IsEpsilonNet K N ε) {z : α} (hz : z ∈ K) :
    ∃ x ∈ N, dist x z ≤ ε := h.2 z hz

/-- If `N` is an `ε`-net of `K` and `K' ⊆ K` still contains `N`, then `N` is
also an `ε`-net of `K'`. -/
lemma anti (h : IsEpsilonNet K N ε) {K' : Set α} (hK' : K' ⊆ K) (hN : N ⊆ K') :
    IsEpsilonNet K' N ε :=
  ⟨hN, fun z hz => h.2 z (hK' hz)⟩

end IsEpsilonNet
