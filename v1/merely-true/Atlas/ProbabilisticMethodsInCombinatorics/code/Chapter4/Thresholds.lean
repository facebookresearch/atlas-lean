/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.SubgraphThreshold
set_option maxHeartbeats 800000

open Filter Real SimpleGraph Classical

namespace Thresholds

/-- The number of ordered pairs $(u, v)$ in $S \times S$ with $u \neq v$ and $u \sim_H v$.
This is twice the number of edges in the induced subgraph $H[S]$. -/
noncomputable def directedEdgesInSubset {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) : ℕ :=
  Finset.card <| (S ×ˢ S).filter fun p => p.1 ≠ p.2 ∧ H.Adj p.1 p.2

/-- The maximum edge-to-vertex ratio over nonempty subsets of $V(H)$, i.e.
$m(H) = \max_{S \ne \emptyset} |E(H[S])| / |S|$. -/
noncomputable def maxEdgeVertexRatio {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [Nonempty V] : ℝ :=
  Finset.sup' (Finset.univ.filter (fun S : Finset V => S.Nonempty))
    (by
      simp only [Finset.filter_nonempty_iff]
      exact ⟨Finset.univ, Finset.mem_univ _,
        ⟨Classical.arbitrary V, Finset.mem_univ _⟩⟩)
    (fun S => (directedEdgesInSubset H S : ℝ) / (2 * S.card : ℝ))

/-- The probability that $G(n, p)$ contains $H$ as a (not necessarily induced) subgraph,
computed by summing Bernoulli edge weights over all graphs $G$ on $n$ vertices that admit
an injective graph homomorphism from $H$. -/
noncomputable def probContainsSubgraph {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (n : ℕ) (p : ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n),
    (if ∃ f : V ↪ Fin n, ∀ v w, H.Adj v w → G.Adj (f v) (f w) then 1 else 0) *
    (p ^ Fintype.card G.edgeSet * (1 - p) ^ (n.choose 2 - Fintype.card G.edgeSet))

/-- The indicator of "there exists an injective homomorphism $H \hookrightarrow G$" is
bounded by the sum of indicators over all injections, since at least one injection works
whenever the existential holds. -/
theorem indicator_exists_le_sum {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj] (G : SimpleGraph (Fin n)) :
    (if ∃ f : V ↪ Fin n, ∀ v w, H.Adj v w → G.Adj (f v) (f w) then (1 : ℝ) else 0) ≤
    ∑ f : V ↪ Fin n, (if ∀ v w, H.Adj v w → G.Adj (f v) (f w) then (1 : ℝ) else 0) := by
  by_cases h : ∃ f : V ↪ Fin n, ∀ v w, H.Adj v w → G.Adj (f v) (f w)
  · rw [if_pos h]
    obtain ⟨f, hf⟩ := h
    have hfterm : (if ∀ v w, H.Adj v w → G.Adj (f v) (f w) then (1 : ℝ) else 0) = 1 := if_pos hf
    calc (1 : ℝ) = if ∀ v w, H.Adj v w → G.Adj (f v) (f w) then 1 else 0 := hfterm.symm
      _ ≤ ∑ g : V ↪ Fin n, if ∀ v w, H.Adj v w → G.Adj (g v) (g w) then (1 : ℝ) else 0 := by
          apply Finset.single_le_sum _ (Finset.mem_univ f)
          intro i _
          split_ifs <;> linarith
  · rw [if_neg h]
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> linarith






end Thresholds
