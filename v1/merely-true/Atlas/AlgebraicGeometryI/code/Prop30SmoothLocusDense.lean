/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Basic
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

/-- The smooth locus of a scheme: points where the local ring is regular. -/
def Scheme.smoothLocus' (X : Scheme.{u}) [IsLocallyNoetherian X] : Set X :=
  {x : X | IsRegularLocalRing (X.presheaf.stalk x)}

/-- Membership in the smooth locus is equivalent to the stalk being a regular local ring. -/
theorem Scheme.mem_smoothLocus'_iff (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    x ∈ Scheme.smoothLocus' X ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
  Iff.rfl



end
