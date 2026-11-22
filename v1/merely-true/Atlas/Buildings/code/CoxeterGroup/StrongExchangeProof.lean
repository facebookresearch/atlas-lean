/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.ExchangeDeletion
import Atlas.Buildings.code.CoxeterGroup.BruhatOrder

namespace CoxeterBruhat

variable {B : Type*}

/-- In a Bruhat cover $v \lessdot w$ with $i$ a descent of $w$ but not of $v$:
$\ell(ws_i) = \ell(v)$ and $\ell(vs_i) = \ell(w)$. -/
theorem exchange_length_analysis {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (v w : W) (i : B)
    (hcover : cs.length v + 1 = cs.length w)
    (hv_not_desc : ¬cs.IsRightDescent v i)
    (hw_desc : cs.IsRightDescent w i) :
    cs.length (w * cs.simple i) = cs.length v ∧
    cs.length (v * cs.simple i) = cs.length w := by
  constructor
  · rcases cs.length_mul_simple w i with h | h
    · exfalso; exact not_lt.mpr (by omega) hw_desc
    · omega
  · rcases cs.length_mul_simple v i with h | h
    · omega
    · exfalso; exact hv_not_desc (by unfold CoxeterSystem.IsRightDescent; omega)

/-- Abstract hypothesis that the reflection $t$ realizing a Bruhat cover $v \lessdot w = vt$
must equal a simple reflection $s_i$ when $i$ is a descent of $w$ but not of $v$. -/
structure ReflectionIdentificationHyp {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) where
  identify : ∀ (v w : W) (t : W),
    t ∈ reflections M cs → v * t = w →
    cs.length v + 1 = cs.length w →
    ∀ (i : B), ¬cs.IsRightDescent v i → cs.IsRightDescent w i →
    t = cs.simple i

/-- The reflection identification hypothesis implies the strong exchange condition for the
Bruhat order. -/
theorem strong_exchange_of_reflection_id {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (hid : ReflectionIdentificationHyp cs) :
    StrongExchangeForBruhat cs := by
  intro v w t ht hvt hcover i hv_not_desc hw_desc
  have := hid.identify v w t ht hvt hcover i hv_not_desc hw_desc
  rw [this] at hvt
  exact hvt

end CoxeterBruhat
