/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Infinity.AffineFunc
import Atlas.Buildings.code.Building.Infinity.ChamberSectorConfig

set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]

/-- A gallery is *minimal* between $C$ and $D$ if it connects them with length
equal to the gallery distance. -/
def Gallery.IsMinimal {K : SimplicialComplex V} (g : Gallery K) (C D : Finset V) : Prop :=
  g.Connects C D ∧ g.length = galleryDist K C D

namespace AffineBuilding










end AffineBuilding
