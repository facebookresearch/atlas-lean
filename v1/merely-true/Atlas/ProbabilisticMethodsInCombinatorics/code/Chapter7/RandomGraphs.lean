/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

noncomputable section

open Finset BigOperators

namespace RandomGraphs

/-- An (unordered) edge of $K_n$ encoded as an ordered pair $\text{src} < \text{dst}$
of vertices in $\text{Fin } n$. -/
structure Edge (n : ℕ) where
  src : Fin n
  dst : Fin n
  hlt : src < dst
  deriving DecidableEq

/-- A configuration of $G(n, p)$: a Boolean assignment to each edge indicating
whether it is present. -/
abbrev Config (n : ℕ) := Edge n → Bool

/-- An ordered triple of vertices $i < j < k$ in $\text{Fin } n$, used to index
potential triangles in $K_n$. -/
structure Triple (n : ℕ) where
  i : Fin n
  j : Fin n
  k : Fin n
  hij : i < j
  hjk : j < k
  deriving DecidableEq

/-- The edge $\{i, j\}$ of the triple $\{i, j, k\}$. -/
def Triple.eij {n : ℕ} (t : Triple n) : Edge n := ⟨t.i, t.j, t.hij⟩
/-- The edge $\{i, k\}$ of the triple $\{i, j, k\}$. -/
def Triple.eik {n : ℕ} (t : Triple n) : Edge n := ⟨t.i, t.k, lt_trans t.hij t.hjk⟩
/-- The edge $\{j, k\}$ of the triple $\{i, j, k\}$. -/
def Triple.ejk {n : ℕ} (t : Triple n) : Edge n := ⟨t.j, t.k, t.hjk⟩

/-- Pointwise containment of edge configurations: $G \leq H$ iff every edge of $G$ is in $H$. -/
def ConfigLE {n : ℕ} (G H : Config n) : Prop :=
  ∀ e : Edge n, G e = true → H e = true

/-- An event $A$ on configurations is decreasing (monotone-down) if removing edges
preserves membership: $G \in A$ and $H \leq G$ implies $H \in A$. -/
def IsDecreasing {n : ℕ} (A : Set (Config n)) : Prop :=
  ∀ G H : Config n, G ∈ A → ConfigLE H G → H ∈ A

/-- The event that the triangle on the triple $t = \{i, j, k\}$ is absent in $G$. -/
def notTriangleEvent {n : ℕ} (t : Triple n) : Set (Config n) :=
  { G | ¬ (G t.eij = true ∧ G t.eik = true ∧ G t.ejk = true) }

/-- The event that $G$ is triangle-free: no triple $\{i, j, k\}$ spans a triangle. -/
def triangleFreeEvent (n : ℕ) : Set (Config n) :=
  { G | ∀ t : Triple n, G ∈ notTriangleEvent t }

/-- The event "the triangle on $t$ is absent" is decreasing in $G$. -/
theorem notTriangleEvent_isDecreasing {n : ℕ} (t : Triple n) :
    IsDecreasing (notTriangleEvent t) := by
  intro G H hG hHG
  simp only [notTriangleEvent, Set.mem_setOf_eq] at *
  intro ⟨h1, h2, h3⟩
  exact hG ⟨hHG _ h1, hHG _ h2, hHG _ h3⟩

/-- Weight assigned to a configuration $G$ under $G(n, p)$:
$\prod_{e} p^{G_e} (1 - p)^{1 - G_e}$. -/
def bernoulliWeight {n : ℕ} [Fintype (Edge n)] (p : ℝ) (G : Config n) : ℝ :=
  ∏ e : Edge n, if G e = true then p else (1 - p)

/-- Probability of an event $A$ under the $G(n, p)$ Bernoulli product measure:
$\mathbb{P}_p(A) = \sum_{G \in A} \text{bernoulliWeight}(p, G)$. -/
def BProb {n : ℕ} [Fintype (Edge n)] [Fintype (Config n)] (p : ℝ)
    (A : Set (Config n)) [DecidablePred (· ∈ A)] : ℝ :=
  ∑ G ∈ (Finset.univ : Finset (Config n)).filter (· ∈ A), bernoulliWeight p G








end RandomGraphs
