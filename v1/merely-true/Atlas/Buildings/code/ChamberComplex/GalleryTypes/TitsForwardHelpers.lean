/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.ChamberComplex.UniquenessBook
import Atlas.Buildings.code.Building.CoxeterComplexFoldings
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterFolding
import Atlas.Buildings.code.CoxeterGroup.DeletionInjectivity

open scoped Classical

namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]


/-- The `mulEquiv` of a `CoxeterSystem` sends its abstract simple reflection to the simple
reflection of the canonical Coxeter system associated to the matrix $M$. -/
lemma mulEquiv_simple_eq_toCoxeterSystem_simple
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (s : B) :
    cs.mulEquiv (cs.simple s) = M.toCoxeterSystem.simple s := by


  simp [CoxeterSystem.simple, CoxeterMatrix.toCoxeterSystem]


end CoxeterSystemFromDeletion

variable {V : Type*} [DecidableEq V]

namespace ChamberComplex


end ChamberComplex
