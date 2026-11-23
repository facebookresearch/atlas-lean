/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic

set_option maxHeartbeats 400000

open SimpleGraph Finset

namespace IndependentTransversal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A function `f : Fin r → V` is an *independent transversal* for the partition
`parts : Fin r → Finset V` of $V$ in the graph $G$ if it picks one vertex from each part
($f i \in $ `parts i`) and its image is an independent set in $G$. -/
def IsIndependentTransversal (G : SimpleGraph V) (parts : Fin r → Finset V)
    (f : Fin r → V) : Prop :=
  (∀ i, f i ∈ parts i) ∧ G.IsIndepSet (Set.range f)

omit [Fintype V] [DecidableEq V] in
/-- An independent transversal for smaller parts `parts'` is also one for any enlargement
`parts ⊇ parts'`. -/
lemma IsIndependentTransversal.of_subset {G : SimpleGraph V} {r : ℕ}
    {parts parts' : Fin r → Finset V}
    (h_sub : ∀ i, parts' i ⊆ parts i) {f : Fin r → V}
    (hf : IsIndependentTransversal G parts' f) :
    IsIndependentTransversal G parts f :=
  ⟨fun i => h_sub i (hf.1 i), hf.2⟩



end IndependentTransversal
