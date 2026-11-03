/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Powerset

set_option maxHeartbeats 400000

open Set Topology

namespace HypergraphColoring

variable {V : Type*}

/-- Set of 2-colorings of `V` that properly color every hyperedge `e ∈ edges` contained in the
finite vertex set `X` (no edge entirely monochromatic). Used in the compactness step of
Theorem 6.2.4. -/
def goodColorings624 (edges : Set (Finset V)) (X : Finset V) : Set (V → Bool) :=
  {c | ∀ e ∈ edges, (↑e : Set V) ⊆ ↑X →
    ¬(∀ v ∈ e, c v = true) ∧ ¬(∀ v ∈ e, c v = false)}

/-- For a finite edge `e` and a Boolean `b`, the set of colorings that are NOT identically `b`
on `e` is closed in the product (discrete) topology on `V → Bool`. -/
lemma isClosed_not_all_eq624 (e : Finset V) (b : Bool) :
    IsClosed {c : V → Bool | ¬(∀ v ∈ e, c v = b)} := by
  have heq : {c : V → Bool | ¬(∀ v ∈ e, c v = b)} = (Set.pi (↑e) (fun _ => {b}))ᶜ := by
    ext c; simp [Set.mem_pi]
  rw [heq]
  exact (isOpen_set_pi e.finite_toSet (fun _ _ => @isOpen_discrete Bool _ _ {b})).isClosed_compl

/-- The set `goodColorings624 edges X` of proper 2-colorings is closed in `V → Bool`. -/
lemma isClosed_goodColorings624 (edges : Set (Finset V)) (X : Finset V) :
    IsClosed (goodColorings624 edges X) := by
  have heq : goodColorings624 edges X =
      ⋂ (e : Finset V) (_ : e ∈ edges) (_ : (↑e : Set V) ⊆ ↑X),
        ({c : V → Bool | ¬(∀ v ∈ e, c v = true)} ∩
         {c | ¬(∀ v ∈ e, c v = false)}) := by
    ext c; simp only [goodColorings624, mem_setOf_eq, mem_iInter, mem_inter_iff]
  rw [heq]
  apply isClosed_iInter; intro e
  apply isClosed_iInter; intro _
  apply isClosed_iInter; intro _
  exact IsClosed.inter (isClosed_not_all_eq624 e true) (isClosed_not_all_eq624 e false)

/-- Antitonicity: enlarging the vertex set `X` shrinks the set of good colorings, since more
edges must be properly colored. -/
lemma goodColorings624_anti (edges : Set (Finset V)) {X Y : Finset V} (hYX : Y ⊆ X) :
    goodColorings624 edges X ⊆ goodColorings624 edges Y := by
  intro c hc e he hes
  exact hc e he (hes.trans (Finset.coe_subset.mpr hYX))



end HypergraphColoring
