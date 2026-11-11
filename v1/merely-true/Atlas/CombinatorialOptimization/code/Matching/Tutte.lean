/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open SimpleGraph

namespace SimpleGraph

variable {V : Type*} [Finite V] {G : SimpleGraph V}

noncomputable def oddComponentCount (G : SimpleGraph V) (X : Set V) : ℕ :=
  ((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard

theorem oddComponentCount_le_ncard_of_isPerfectMatching
    {M : G.Subgraph} (hM : M.IsPerfectMatching) (X : Set V) :
    G.oddComponentCount X ≤ X.ncard := by
  have := SimpleGraph.not_isTutteViolator_of_isPerfectMatching hM X
  unfold IsTutteViolator at this
  unfold oddComponentCount
  omega

theorem isPerfectMatching_of_oddComponentCount_le
    (h : ∀ X : Set V, G.oddComponentCount X ≤ X.ncard) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  rw [SimpleGraph.tutte]
  intro X
  unfold IsTutteViolator
  have := h X
  unfold oddComponentCount at this
  omega

theorem tutte_theorem :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
    ∀ X : Set V, G.oddComponentCount X ≤ X.ncard := by
  constructor
  · intro ⟨M, hM⟩ X
    exact oddComponentCount_le_ncard_of_isPerfectMatching hM X
  · exact isPerfectMatching_of_oddComponentCount_le

end SimpleGraph
