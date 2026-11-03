/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Matching.Berge

open SimpleGraph

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def augPathLengths (G : SimpleGraph V) (M : G.Subgraph) : Set ℕ∞ :=
  { n : ℕ∞ | ∃ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M ∧ (p.length : ℕ∞) = n }

noncomputable def shortestAugPathLength (G : SimpleGraph V) (M : G.Subgraph) : ℕ∞ :=
  sInf (augPathLengths G M)

structure VertexDisjointAugPaths (G : SimpleGraph V) (M : G.Subgraph) (k : ℕ) where
  ι : Type*
  src : ι → V
  tgt : ι → V
  path : (i : ι) → G.Walk (src i) (tgt i)
  isAug : ∀ i, (path i).IsAugmentingPath M
  hasLen : ∀ i, (path i).length = k
  disjoint : ∀ i j, i ≠ j →
    List.Disjoint ((path i).support) ((path j).support)

def VertexDisjointAugPaths.IsMaximal {G : SimpleGraph V} {M : G.Subgraph} {k : ℕ}
    (paths : VertexDisjointAugPaths G M k) : Prop :=
  ∀ (u v : V) (p : G.Walk u v),
    p.IsAugmentingPath M → p.length = k →
    ∃ i, ¬ List.Disjoint p.support ((paths.path i).support)

def IsAugmentationAlongPaths {G : SimpleGraph V} (M M' : G.Subgraph) {k : ℕ}
    (paths : VertexDisjointAugPaths G M k) : Prop :=
  M'.IsMatching ∧
  (∀ e ∈ M'.edgeSet, e ∉ M.edgeSet →
    ∃ i, e ∈ (paths.path i).edges.toFinset) ∧
  (∀ e ∈ M.edgeSet, e ∉ M'.edgeSet →
    ∃ i, e ∈ (paths.path i).edges.toFinset) ∧
  (∀ v : V, (∀ i, v ∉ (paths.path i).support) →
    (v ∈ M.verts ↔ v ∈ M'.verts))





end SimpleGraph
