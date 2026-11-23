/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace LocalRings

abbrev IsLocalRingDef (A : Type*) [CommRing A] : Prop := IsLocalRing A

abbrev residueFieldOfLocal (A : Type*) [CommRing A] [IsLocalRing A] :=
  IsLocalRing.ResidueField A

end LocalRings
