/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option maxHeartbeats 400000

open Filter Real SimpleGraph Classical

namespace SubgraphThreshold

/-- A function $q : \mathbb{N} \to \mathbb{R}$ is a **threshold** for the property of containing $H$
if for any sequence $p_n$ with $p_n / q_n \to 0$ the probability $\mathbb{P}(H \subseteq G(n, p_n)) \to 0$,
and if $p_n / q_n \to \infty$ then this probability tends to $1$. -/
def IsSubgraphThreshold (probContainsH : ℕ → ℝ → ℝ) (q : ℕ → ℝ) : Prop :=
  (∀ p : ℕ → ℝ, Tendsto (fun n => p n / q n) atTop (nhds 0) →
    Tendsto (fun n => probContainsH n (p n)) atTop (nhds 0)) ∧
  (∀ p : ℕ → ℝ, Tendsto (fun n => p n / q n) atTop atTop →
    Tendsto (fun n => probContainsH n (p n)) atTop (nhds 1))

/-- The **maximum edge density** of a graph $H$, defined as
$m(H) = \max_{S \subseteq V(H), S \ne \emptyset} \frac{|E(H[S])|}{|S|}$,
where the numerator counts edges in the induced subgraph on $S$. -/
noncomputable def maxDensity {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [Nonempty V] : ℝ :=
  Finset.sup' (Finset.univ.filter (fun S : Finset V => S.Nonempty))
    (by
      simp only [Finset.filter_nonempty_iff]
      exact ⟨Finset.univ, Finset.mem_univ _,
        ⟨Classical.arbitrary V, Finset.mem_univ _⟩⟩)
    (fun S => ((((S ×ˢ S).filter fun p => p.1 ≠ p.2 ∧ H.Adj p.1 p.2).card : ℝ) / (2 * S.card : ℝ)))

/-- The probability that the Erdős–Rényi random graph $G(n, p)$ contains $H$ as a subgraph,
computed as the sum over all graphs $G$ on $n$ vertices weighted by their Bernoulli edge
probabilities, with indicator of containing an injective homomorphism from $H$. -/
noncomputable def probContainsSubgraph {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (n : ℕ) (p : ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n),
    (if ∃ f : V ↪ Fin n, ∀ v w, H.Adj v w → G.Adj (f v) (f w) then (1 : ℝ) else 0) *
    (p ^ Fintype.card G.edgeSet * (1 - p) ^ (n.choose 2 - Fintype.card G.edgeSet))

/-- The conjectural threshold function $q(n) = n^{-1/m(H)}$ for a subgraph $H$,
where $m(H)$ is the maximum edge density of $H$. -/
noncomputable def thresholdFunction {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [Nonempty V] (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / maxDensity H)


end SubgraphThreshold
