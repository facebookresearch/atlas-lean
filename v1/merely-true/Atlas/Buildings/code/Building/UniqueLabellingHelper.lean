/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.AptIsCoxeterProof
import Atlas.Buildings.code.ChamberComplex.CoxeterComplex

open scoped Classical

variable {V : Type} [DecidableEq V]

/-- In a thin chamber complex, each facet $F$ of a chamber $C$ lies in
exactly one other chamber $D \ne C$. -/
theorem thin_unique_other_chamber
    (cc : ChamberComplex V)
    (hthin : cc.IsThin)
    (F C : Finset V)
    (hFC : cc.toSimplicialComplex.IsFacet F C)
    (hC : cc.toSimplicialComplex.IsMaximal C) :
    ∃! D, D ≠ C ∧ cc.toSimplicialComplex.IsFacet F D ∧
      cc.toSimplicialComplex.IsMaximal D :=
  hthin F C hFC hC














