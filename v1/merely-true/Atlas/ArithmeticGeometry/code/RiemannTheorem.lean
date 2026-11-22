/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.RiemannRoch

namespace RiemannRochSpace

variable {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]

open CurveWithOrd CurveDivisor


/-- Membership in the Riemann–Roch space: if a unit $f \in F^\times$ lies in $L(D)$, then the
divisor $(f) + D$ is effective. -/
lemma effective_of_mem_riemannRochSpace (D : CurveDivisor C) (f : Fˣ)
    (hf : (f : F) ∈ riemannRochSpace (k := k) D) :
    (principalDivisor f + D).IsEffective := by
  rw [mem_riemannRochSpace_iff] at hf
  obtain (h0 | ⟨hne, heff⟩) := hf
  · exact absurd h0 f.ne_zero
  · convert heff using 2
    congr 1
    exact Units.ext rfl





end RiemannRochSpace
