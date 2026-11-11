/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

open Topology

/-- A CW-complex structure on a topological space `X`, identified with a CW-complex
structure on the universe set `Set.univ : Set X` from mathlib's `Topology.CWComplex`. -/
abbrev CWComplex (X : Type*) [TopologicalSpace X] : Type _ :=
  Topology.CWComplex (Set.univ : Set X)

namespace CWComplex

variable {X : Type*} [TopologicalSpace X]

/-- The indexing type of `n`-cells in a CW-complex `X`. These are the cells $A_n$
appearing in the attaching pushout for $\mathrm{Sk}_n X$. -/
abbrev cells (X : Type*) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]
    (n : ℕ) : Type _ :=
  Topology.CWComplex.cell (Set.univ : Set X) n

/-- The `n`-skeleton $\mathrm{Sk}_n X$ of a CW-complex, defined for `n : ℕ∞`. This is
the subspace obtained by attaching all cells of dimension at most `n`, as in
Definition 14.5. -/
noncomputable abbrev skeleton (X : Type*) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ∞) :=
  Topology.CWComplex.skeleton (Set.univ : Set X) n

/-- A CW-complex is finite-dimensional (Definition 14.7) if there is some `n` beyond
which there are no cells, i.e., $\mathrm{Sk}_n X = X$ for some `n`. -/
def IsFiniteDimensional (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] : Prop :=
  ∃ n : ℕ, ∀ m : ℕ, n ≤ m → IsEmpty (cells X m)

/-- A CW-complex is of finite type (Definition 14.7) if each set of `n`-cells $A_n$
is finite. -/
def IsFiniteType (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] : Prop :=
  ∀ n : ℕ, Finite (cells X n)

/-- A CW-complex is finite (Definition 14.7) if it is both finite-dimensional and of
finite type. Equivalently, it has only finitely many cells in total. -/
def IsFinite (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] : Prop :=
  IsFiniteDimensional X ∧ IsFiniteType X

/-- A bundle of the three properties of CW-complexes stated in Theorem 14.8:
every CW-complex is Hausdorff, compactness is equivalent to finiteness, and every
compact smooth manifold admits a CW-structure. -/
structure CWComplexProperties where
  hausdorff :
    ∀ (X : Type*) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)], T2Space X
  compact_iff_finite :
    ∀ (X : Type*) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)],
      CompactSpace X ↔ IsFinite X
  manifold_admits_cw :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {H : Type*} [TopologicalSpace H]
      (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
      [ChartedSpace H M] [IsManifold I ⊤ M] [CompactSpace M],
      Topology.CWComplex (Set.univ : Set M)





end CWComplex
