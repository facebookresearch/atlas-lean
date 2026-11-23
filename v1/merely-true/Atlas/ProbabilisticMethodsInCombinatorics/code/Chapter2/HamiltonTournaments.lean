/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option maxHeartbeats 800000

open Finset Fintype

namespace SzeleTournament

/-- The set of unordered edge positions on $n$ labeled vertices, encoded as ordered
pairs $(i, j)$ with $i < j$. -/
abbrev EdgeSet (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

/-- A tournament on $n$ vertices: an orientation assigning a Boolean direction to each
unordered edge in `EdgeSet n`. -/
abbrev Tournament (n : ℕ) := EdgeSet n → Bool

/-- The directed edge from $i$ to $j$ in tournament $T$: true if $T$ orients the edge
in the direction $i \to j$, false otherwise (including the diagonal). -/
def tournamentEdge {n : ℕ} (T : Tournament n) (i j : Fin n) : Bool :=
  if h : i < j then T ⟨(i, j), h⟩
  else if h2 : j < i then !T ⟨(j, i), h2⟩
  else false

/-- A permutation $\sigma$ of $\mathrm{Fin}\,n$ is a Hamilton path in tournament $T$
if every consecutive pair $(\sigma(i), \sigma(i+1))$ is a directed edge of $T$. -/
def IsHamiltonPath {n : ℕ} (T : Tournament n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, (h : i.val + 1 < n) →
    tournamentEdge T (σ i) (σ ⟨i.val + 1, h⟩) = true

/-- Decidability instance for `IsHamiltonPath`, used for counting. -/
instance instDecIsHP {n : ℕ} (T : Tournament n) (σ : Equiv.Perm (Fin n)) :
    Decidable (IsHamiltonPath T σ) := by
  unfold IsHamiltonPath; exact inferInstance

/-- The number of Hamilton paths in a tournament $T$, defined as the cardinality of the
set of permutations $\sigma$ for which `IsHamiltonPath T σ` holds. -/
noncomputable def numHamiltonPaths {n : ℕ} (T : Tournament n) : ℕ :=
  (Finset.univ.filter (IsHamiltonPath T)).card


/-- For $n \geq 1$, the edge count of `EdgeSet n` is at least $n - 1$,
exhibited by the path $(0,1), (1,2), \dots, (n-2, n-1)$. -/
lemma n_sub_one_le_card_edgeset (n : ℕ) (hn : n ≥ 1) :
    n - 1 ≤ Fintype.card (EdgeSet n) := by
  have hinj : Function.Injective (fun k : Fin (n - 1) =>
    (⟨(⟨k.val, by omega⟩, ⟨k.val + 1, by omega⟩), by
      exact Fin.mk_lt_mk.mpr (by omega)⟩ : EdgeSet n)) := by
    intro a b hab
    have h := congrArg (fun x => (x : EdgeSet n).val.1.val) hab
    exact Fin.ext h
  have := Fintype.card_le_of_injective _ hinj
  rwa [Fintype.card_fin] at this



end SzeleTournament
