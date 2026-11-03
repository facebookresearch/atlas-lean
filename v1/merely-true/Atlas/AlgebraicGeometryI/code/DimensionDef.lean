/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace

open TopologicalSpace Order Topology

/-- The dimension of a topological space `X` (Definition 11): the length of the longest
chain of irreducible closed subsets, modeled here via the topological Krull dimension. -/
noncomputable abbrev dimension (X : Type*) [TopologicalSpace X] : WithBot ℕ∞ :=
  topologicalKrullDim X

/-- The dimension of `X` equals the Krull dimension of its poset of irreducible closed
subsets, by definition. -/
theorem dimension_eq_krullDim_irreducibleCloseds (X : Type*) [TopologicalSpace X] :
    dimension X = krullDim (IrreducibleCloseds X) :=
  rfl

/-- Dimension is monotone under topological inducing maps. -/
theorem dimension_le_of_isInducing {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → X} (hf : IsInducing f) :
    dimension Y ≤ dimension X :=
  IsInducing.topologicalKrullDim_le hf

/-- A subspace has dimension at most that of the ambient space. -/
theorem dimension_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set X) :
    dimension Y ≤ dimension X :=
  topologicalKrullDim_subspace_le X Y

/-- A discrete topological space has dimension at most zero. -/
theorem dimension_le_zero_of_discreteTopology
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    dimension X ≤ 0 :=
  topologicalKrullDim_zero_of_discreteTopology X
