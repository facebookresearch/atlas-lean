/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Over
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Normalization

open AlgebraicGeometry CategoryTheory

universe u

/-- A morphism between two proper `k`-schemes that is itself compatible with the
structure maps is proper. -/
theorem prop27_isProper
    (k : Type u) [Field k]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsProper (Y ↘ Spec (.of k))]
    (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] :
    IsProper f := by
  have h : f ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k) := HomIsOver.comp_over
  haveI : IsProper (f ≫ (Y ↘ Spec (.of k))) := h ▸ inferInstance
  exact IsProper.of_comp f (Y ↘ Spec (.of k))



