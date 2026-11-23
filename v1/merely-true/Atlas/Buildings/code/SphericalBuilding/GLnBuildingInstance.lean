/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnInstance
import Atlas.Buildings.code.SphericalBuilding.GLnThinApartmentUnconditional
import Atlas.Buildings.code.SphericalBuilding.GLnApartmentIsoUnconditional
import Atlas.Buildings.code.SphericalBuilding.GLnCommonApartmentUnconditional

namespace GLnBuilding

/-- Main theorem: the flag complex of $\mathrm{GL}_n(k)$ over any field $k$ is a building,
constructed unconditionally by combining the thinness, common-apartment, and apartment-iso
proofs. -/
noncomputable def glnIsBuilding_unconditional (k : Type*) [Field k] (n : ℕ) : IsBuilding k n :=
  glnIsBuilding k n
    (thinApartmentHypUnconditional k n)
    (commonApartmentHypUnconditional k n)
    (apartmentIsoHypUnconditional k n)

end GLnBuilding
