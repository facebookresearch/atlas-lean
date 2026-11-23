/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Over

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Definition 19 (Lec 8): a scheme `X` over `S` is *complete* if its structural morphism is
proper (i.e. separated, universally closed, and locally of finite type). -/
def IsComplete (X S : Scheme.{u}) [X.Over S] : Prop :=
  IsProper (X ↘ S)

/-- Unfolds `IsComplete` to the conjunction `separated ∧ universally closed ∧ locally of finite
type`. -/
theorem isComplete_iff (X S : Scheme.{u}) [X.Over S] :
    IsComplete X S ↔
      IsSeparated (X ↘ S) ∧ UniversallyClosed (X ↘ S) ∧ LocallyOfFiniteType (X ↘ S) := by
  simp only [IsComplete, isProper_iff]

/-- Constructor for `IsComplete` from instance arguments. -/
theorem IsComplete.mk' {X S : Scheme.{u}} [X.Over S]
    [IsSeparated (X ↘ S)] [UniversallyClosed (X ↘ S)] [LocallyOfFiniteType (X ↘ S)] :
    IsComplete X S :=
  ⟨⟩

/-- A complete scheme is separated. -/
theorem IsComplete.isSeparated {X S : Scheme.{u}} [X.Over S] (h : IsComplete X S) :
    IsSeparated (X ↘ S) :=
  h.toIsSeparated

/-- A complete scheme is universally closed. -/
theorem IsComplete.universallyClosed {X S : Scheme.{u}} [X.Over S] (h : IsComplete X S) :
    UniversallyClosed (X ↘ S) :=
  h.toUniversallyClosed

/-- A complete scheme is locally of finite type. -/
theorem IsComplete.locallyOfFiniteType {X S : Scheme.{u}} [X.Over S] (h : IsComplete X S) :
    LocallyOfFiniteType (X ↘ S) :=
  h.toLocallyOfFiniteType

end AlgebraicGeometry
