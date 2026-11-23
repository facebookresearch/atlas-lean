/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.QCohEquivalenceProof
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Exactness

set_option maxHeartbeats 800000

set_option maxHeartbeats 4000000

namespace SerreAffineCriterion

universe u v

section LocalizationFlat

/-- Localization at a submonoid `S ⊆ R` produces a flat `R`-module,
a key input for Serre's affineness criterion (exactness of global
sections on affine opens). -/
theorem serre_localization_flat (R : Type*) [CommRing R] (S : Submonoid R) :
    Module.Flat R (Localization S) :=
  IsLocalization.flat _ S

end LocalizationFlat

section LocalizationExact

end LocalizationExact

section GammaExact

end GammaExact

end SerreAffineCriterion
