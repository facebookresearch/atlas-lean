/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.BeilinsonBernstein

open CategoryTheory

namespace BeilinsonBernstein

noncomputable section

universe u

structure EquivariantBBData extends BBDataTwisted where
  AlgGroupK : Type u
  instGroupK : Group AlgGroupK
  KEquivDModOfWeight : (mu : WeightSpace) → AbCat.{u}
  GKModOfWeight : (mu : WeightSpace) → AbCat.{u}
  inclKEquivDMod : (mu : WeightSpace) →
    (KEquivDModOfWeight mu).Obj ⥤ (DModOfWeight mu).Obj
  inclGKMod : (mu : WeightSpace) →
    (GKModOfWeight mu).Obj ⥤ (UModOfWeight mu).Obj
  inclKEquivDMod_faithful : ∀ mu, (inclKEquivDMod mu).Faithful
  inclGKMod_faithful : ∀ mu, (inclGKMod mu).Faithful
  GammaKEquivOfWeight : (mu : WeightSpace) →
    (KEquivDModOfWeight mu).Obj ⥤ (GKModOfWeight mu).Obj
  LocKEquivOfWeight : (mu : WeightSpace) →
    (GKModOfWeight mu).Obj ⥤ (KEquivDModOfWeight mu).Obj
  gammaKEquiv_compat : ∀ mu,
    GammaKEquivOfWeight mu ⋙ inclGKMod mu = inclKEquivDMod mu ⋙ GammaOfWeight mu
  locKEquiv_compat : ∀ mu,
    LocKEquivOfWeight mu ⋙ inclKEquivDMod mu = inclGKMod mu ⋙ LocOfWeight mu

attribute [instance] EquivariantBBData.instGroupK




end

end BeilinsonBernstein
