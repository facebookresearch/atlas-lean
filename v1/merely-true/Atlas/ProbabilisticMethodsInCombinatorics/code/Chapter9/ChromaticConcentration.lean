/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Combinatorics.SimpleGraph.Coloring
set_option maxHeartbeats 400000

open MeasureTheory Measure SimpleGraph Real

namespace ChromaticConcentration

/-- Two graphs $G$ and $G'$ on vertex set $V$ differ only at vertex $v$: their adjacency
relations agree on all pairs not involving $v$. -/
def DiffOnlyAt {V : Type*} (G G' : SimpleGraph V) (v : V) : Prop :=
  ∀ a b, a ≠ v → b ≠ v → (G.Adj a b ↔ G'.Adj a b)

/-- Symmetry of `DiffOnlyAt`: if $G$ and $G'$ differ only at $v$, so do $G'$ and $G$. -/
lemma DiffOnlyAt.symm {V : Type*} {G G' : SimpleGraph V} {v : V}
    (h : DiffOnlyAt G G' v) : DiffOnlyAt G' G v :=
  fun a b ha hb => (h a b ha hb).symm

/-- The chromatic number of a graph on `Fin n`, viewed as a real number. -/
noncomputable def chromaticNumberReal (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  (G.chromaticNumber.toNat : ℝ)






end ChromaticConcentration
