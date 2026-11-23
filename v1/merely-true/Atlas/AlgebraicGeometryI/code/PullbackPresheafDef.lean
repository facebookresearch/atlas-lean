/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.Presheaf

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace TopCat.Presheaf

/-- The pullback presheaf of a presheaf `𝒢` on `Y` along a continuous map `f : X ⟶ Y`,
defined via the pullback functor `pullback C f`. -/
def pullbackPresheaf (C : Type u) [Category.{v} C] [Limits.HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (𝒢 : Y.Presheaf C) : X.Presheaf C :=
  (pullback C f).obj 𝒢

/-- Unfolds `pullbackPresheaf` to the application of the `pullback` functor. -/
theorem pullbackPresheaf_eq (C : Type u) [Category.{v} C] [Limits.HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (𝒢 : Y.Presheaf C) :
    pullbackPresheaf C f 𝒢 = (pullback C f).obj 𝒢 :=
  rfl

/-- The pullback–pushforward adjunction `f⁻¹ ⊣ f_*` on presheaves with values in `C`. -/
def pullbackAdj (C : Type u) [Category.{v} C] [Limits.HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    pullback C f ⊣ pushforward C f :=
  pullbackPushforwardAdjunction C f

end TopCat.Presheaf

end
