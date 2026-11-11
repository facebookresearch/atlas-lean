/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option maxHeartbeats 400000

namespace GalvinTetali

open scoped Classical

/-- A `LoopGraph` on a vertex set $W$: a symmetric relation `Adj` on $W$, allowing
self-loops (unlike `SimpleGraph`). Used as the target graph $H$ in graph homomorphism
counts. -/
structure LoopGraph (W : Type*) where
  Adj : W → W → Prop
  symm : ∀ u v, Adj u v → Adj v u

/-- `IsGraphHom G H φ` says that $\varphi : V \to W$ is a graph homomorphism from the
simple graph $G$ on $V$ to the loop graph $H$ on $W$: adjacent vertices map to adjacent
vertices. -/
def IsGraphHom {V W : Type*} (G : SimpleGraph V) (H : LoopGraph W) (φ : V → W) : Prop :=
  ∀ u v, G.Adj u v → H.Adj (φ u) (φ v)

/-- The number $\mathrm{hom}(G, H)$ of graph homomorphisms from a finite simple graph $G$
to a finite loop graph $H$. -/
noncomputable def homCount {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : LoopGraph W) : ℕ :=
  Fintype.card { φ : V → W // IsGraphHom G H φ }



end GalvinTetali
