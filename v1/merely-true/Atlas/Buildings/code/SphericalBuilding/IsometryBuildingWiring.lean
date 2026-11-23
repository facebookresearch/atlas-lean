/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.IsometryCommonApartment
import Atlas.Buildings.code.SphericalBuilding.IsometryApartmentExchange

namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Concrete wiring: produces the isometry building from a hyperbolic frame, by plugging in
the common-apartment and apartment-exchange instances. -/
noncomputable def isometryIsBuilding_wired
    (B : LinearMap.BilinForm k V) (n : ℕ)
    (frame : HyperbolicFrame B n) :
    IsBuilding B n :=
  isometryIsBuilding B n
    (commonIsotropicApartmentHyp B n frame)
    (apartmentExchangeHypInstance B n)

end IsometryBuilding
