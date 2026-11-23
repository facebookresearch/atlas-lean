/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open SimpleGraph Finset

namespace HighGirthChromatic

/-- If every short cycle of $G$ (length $\leq g$) passes through some vertex of $S$, then
the subgraph induced on $V \setminus S$ has girth strictly greater than $g$. -/
lemma induce_compl_no_short_cycles {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (S : Finset (Fin n)) (g : ℕ)
    (hS : ∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → w.length ≤ g →
      ∃ u, u ∈ S ∧ u ∈ w.support.toFinset) :
    ∀ (v : ↑(↑(Finset.univ \ S) : Set (Fin n)))
      (w : (G.induce (↑(Finset.univ \ S) : Set (Fin n))).Walk v v),
      w.IsCycle → g < w.length := by
  set T : Set (Fin n) := ↑(Finset.univ \ S)
  set ι := Embedding.induce (G := G) T
  intro v w hw
  by_contra hle
  push Not at hle
  have hw_mapped : (w.map ι.toHom).IsCycle := hw.map ι.injective
  have hlen : (w.map ι.toHom).length = w.length := Walk.length_map _ _
  obtain ⟨u, hu_S, hu_supp⟩ := hS _ _ hw_mapped (hlen ▸ hle)
  have huT : u ∈ T := by
    have hx : u ∈ (w.map ι.toHom).support := List.mem_toFinset.mp hu_supp
    rw [Walk.support_map] at hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    have hι_eq : ι.toHom y = (y : Fin n) := by
      show ι y = (y : Fin n)
      simp only [ι, Embedding.comap, RelEmbedding.coe_mk, Function.Embedding.subtype_apply]
    rw [hι_eq]
    exact y.prop
  have hunotS : u ∉ S := by
    simp only [T, Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
               true_and, Finset.mem_coe] at huT
    exact huT
  exact hunotS hu_S




end HighGirthChromatic
