/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace

open TopologicalSpace

/-- Lecture 4, Definition 11: the dimension of a Noetherian topological space, defined as the
topological Krull dimension (the supremum of lengths of chains of irreducible closed subsets). -/
noncomputable def noetherianTopologicalDim (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] : WithBot ℕ∞ :=
  topologicalKrullDim X

/-- The Noetherian topological dimension equals the Krull dimension of the poset of irreducible
closed subsets. -/
theorem noetherianTopologicalDim_eq_krullDim (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] :
    noetherianTopologicalDim X = Order.krullDim (IrreducibleCloseds X) :=
  rfl

/-- The Noetherian topological dimension is, by definition, the topological Krull dimension. -/
theorem noetherianTopologicalDim_eq_topologicalKrullDim (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] :
    noetherianTopologicalDim X = topologicalKrullDim X :=
  rfl
