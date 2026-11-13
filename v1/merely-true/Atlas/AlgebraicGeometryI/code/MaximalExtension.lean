/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.RationalMap

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- For `X` irreducible reduced and `Y` separated, every partial map `f : U → Y`
extends to a maximal partial map `g : V → Y` with `U ⊆ V`, i.e. any partial map
in the same equivalence class is dominated by `g` (Cor 14, Lec 7). -/
theorem exists_maximal_extension_of_irreducible_separated
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IsReduced X] [Y.IsSeparated]
    (f : X.PartialMap Y) :
    ∃ (g : X.PartialMap Y),
      g.equiv f ∧
      (∀ (h : X.PartialMap Y), h.equiv f → h.domain ≤ g.domain) := by
  refine ⟨f.toRationalMap.toPartialMap, ?_, ?_⟩
  · rw [← Scheme.PartialMap.toRationalMap_eq_iff]
    simp [Scheme.RationalMap.toRationalMap_toPartialMap]
  · intro h hequiv
    have htoRational : h.toRationalMap = f.toRationalMap :=
      Scheme.PartialMap.toRationalMap_eq_iff.mpr hequiv
    calc h.domain ≤ h.toRationalMap.domain := h.le_domain_toRationalMap
      _ = f.toRationalMap.domain := by rw [htoRational]
      _ = f.toRationalMap.toPartialMap.domain := rfl

end AlgebraicGeometry
