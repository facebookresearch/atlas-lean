/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
set_option maxHeartbeats 800000

namespace SidorenkoInequality

open SimpleGraph

/-- Number of graph homomorphisms from $F$ to $G$, denoted $\mathrm{hom}(F, G)$. -/
noncomputable def homCount {V : Type*} {W : Type*}
    (F : SimpleGraph V) (G : SimpleGraph W)
    [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableRel F.Adj] [DecidableRel G.Adj] : ℕ :=
  Fintype.card (F →g G)

/-- Homomorphism density of $F$ in $G$, defined as $\mathrm{hom}(F, G) / |V(G)|^{|V(F)|}$. -/
noncomputable def homDensity {V : Type*} {W : Type*}
    (F : SimpleGraph V) (G : SimpleGraph W)
    [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableRel F.Adj] [DecidableRel G.Adj] : ℝ :=
  (homCount F G : ℝ) / ((Fintype.card W : ℝ) ^ Fintype.card V)

/-- Sidorenko's property (Conjecture 10.3.2). A bipartite graph $F$ "satisfies Sidorenko"
if for every graph $G$,
$\mathrm{hom\text{-}density}(F, G) \ge \mathrm{hom\text{-}density}(K_2, G)^{|E(F)|}$,
where $\mathrm{hom\text{-}density}(K_2, G)$ is the edge density of $G$. -/
def SidorenkoProperty {V : Type*} (F : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel F.Adj] [Fintype F.edgeSet] : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    homDensity F G ≥ (homDensity (completeGraph (Fin 2)) G) ^ F.edgeFinset.card

end SidorenkoInequality

open SidorenkoInequality SimpleGraph


