/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.StrongExchangeProof

set_option linter.unusedSectionVars false

namespace CoxeterReflectionId

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Hypothesis bridge for identifying reflections from inversion-set differences:
if $vt = w$ with $\ell(v) + 1 = \ell(w)$ and a generator $i$ flips its descent status,
then $t$ equals the simple reflection $s_i$. -/
structure InversionDifferenceBridgeHyp {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) where
  identify_from_inversions : ∀ (v w : W) (t : W),
    t ∈ CoxeterBruhat.reflections M cs → v * t = w →
    cs.length v + 1 = cs.length w →
    ∀ (i : B), ¬cs.IsRightDescent v i → cs.IsRightDescent w i →
    t = cs.simple i

/-- Bridge: an inversion-difference identification hypothesis upgrades to the
genuine reflection identification hypothesis used by the strong exchange machinery. -/
theorem reflection_identification_genuine {W : Type*} [Group W]
    {M : CoxeterMatrix B} {cs : CoxeterSystem M W}
    (bridge : InversionDifferenceBridgeHyp cs) :
    CoxeterBruhat.ReflectionIdentificationHyp cs where
  identify := bridge.identify_from_inversions

/-- Converse bridge: an existing reflection-identification hypothesis yields the
inversion-difference bridge hypothesis. -/
def bridge_from_reflection_id {W : Type*} [Group W]
    {M : CoxeterMatrix B} {cs : CoxeterSystem M W}
    (hid : CoxeterBruhat.ReflectionIdentificationHyp cs) :
    InversionDifferenceBridgeHyp cs where
  identify_from_inversions := hid.identify

/-- The Strong Exchange Property holds whenever the inversion-difference bridge holds. -/
theorem strong_exchange_from_bridge {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (bridge : InversionDifferenceBridgeHyp cs) :
    CoxeterBruhat.StrongExchangeForBruhat cs :=
  CoxeterBruhat.strong_exchange_of_reflection_id cs
    (reflection_identification_genuine bridge)

end CoxeterReflectionId
