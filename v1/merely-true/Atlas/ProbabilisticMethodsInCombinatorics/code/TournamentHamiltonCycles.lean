/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.Permanent

open Finset Real

noncomputable section

namespace TournamentHamiltonCycles

/-- A tournament on $n$ vertices: an irreflexive Boolean edge relation such that exactly one
of $\mathrm{edge}(i, j)$ or $\mathrm{edge}(j, i)$ is true for $i \ne j$. -/
structure Tournament (n : ℕ) where
  edge : Fin n → Fin n → Bool
  irrefl : ∀ i, edge i i = false
  tournament : ∀ i j, i ≠ j → (edge i j = true ↔ edge j i = false)

/-- A permutation $\sigma$ encodes a Hamilton cycle of $T$ iff every directed edge
$i \to \sigma(i)$ exists in $T$ and $\sigma$ is a single $n$-cycle. -/
def IsHamiltonCycle {n : ℕ} (T : Tournament n) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i : Fin n, T.edge i (σ i) = true) ∧ σ.IsCycle ∧ σ.support = Finset.univ

/-- The number of Hamilton cycles of $T$, counted as cycle-permutations on $\mathrm{Fin}\, n$. -/
noncomputable def Tournament.numHamiltonCycles {n : ℕ} (T : Tournament n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (∀ i : Fin n, T.edge i (σ i) = true) ∧ σ.IsCycle ∧ σ.support = Finset.univ)).card

/-- Out-degree of vertex $i$ in $T$: the number of $j$ with $T.\mathrm{edge}(i, j)$ true. -/
def Tournament.outDeg {n : ℕ} (T : Tournament n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => T.edge i j = true)).card










/-- If $T$ contains at least one Hamilton cycle, then every vertex has positive out-degree
(it has at least one outgoing edge along the cycle). -/
theorem outDeg_pos_of_numHamiltonCycles_pos
    {n : ℕ} (T : Tournament n) (h : T.numHamiltonCycles > 0) (i : Fin n) :
    T.outDeg i > 0 := by
  classical
  unfold Tournament.numHamiltonCycles at h
  have hne : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (∀ i : Fin n, T.edge i (σ i) = true) ∧ σ.IsCycle ∧ σ.support = Finset.univ)).Nonempty :=
    Finset.card_pos.mp h
  obtain ⟨σ, hσ⟩ := hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  obtain ⟨hedge, _, _⟩ := hσ
  unfold Tournament.outDeg
  exact Finset.card_pos.mpr ⟨σ i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge i⟩⟩


end TournamentHamiltonCycles
