/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Filtered.Basic
import Atlas.AlgebraicGeometryI.code.NoetherianColimit

open CategoryTheory CategoryTheory.Limits TopCat Opposite TopologicalSpace

noncomputable section

universe u w

namespace TopCat.Sheaf

variable {C : Type (u+1)} [Category.{u} C]
         {J : Type w} [SmallCategory J]
         {X : TopCat.{u}}

/-- If the target category `C` has `J`-shaped colimits and weak sheafification, then the
category of `C`-valued sheaves on `X` also has `J`-shaped colimits. -/
instance hasColimitsOfShape_of_hasWeakSheafify
    [HasColimitsOfShape J C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    HasColimitsOfShape J (TopCat.Sheaf C X) :=
  inferInstanceAs (HasColimitsOfShape J
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C))

end TopCat.Sheaf


