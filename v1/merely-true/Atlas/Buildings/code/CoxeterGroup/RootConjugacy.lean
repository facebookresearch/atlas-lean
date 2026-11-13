/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.ReflectionLengthDecrease
import Atlas.Buildings.code.CoxeterGroup.Reflections

open Finset BigOperators

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Section 1.6 conjugacy identity: with $\alpha = u \cdot \alpha_s$, $s_\alpha = u s_s u^{-1}$,
and $\beta = w \cdot \alpha$, one has $w s_\alpha w^{-1} = s_\beta$ as operators on
$\mathbb{R}^B$. -/
theorem conjugation_reflection_identity {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (w u : W) (s : B) (v : B → ℝ) :
    let α := (coxeterRepresentation M cs u) (e s)
    let s_α := u * cs.simple s * u⁻¹
    let β := (coxeterRepresentation M cs w) α
    (coxeterRepresentation M cs (w * s_α * w⁻¹)) v =
    generalizedReflection M β v := by
  simp only []
  have hconj : w * (u * cs.simple s * u⁻¹) * w⁻¹ =
      (w * u) * cs.simple s * (w * u)⁻¹ := by group
  rw [hconj]
  have hβ : (coxeterRepresentation M cs w) ((coxeterRepresentation M cs u) (e s)) =
      (coxeterRepresentation M cs (w * u)) (e s) := by
    rw [map_mul (coxeterRepresentation M cs) w u, LinearEquiv.mul_apply]
  rw [hβ]
  exact conj_simpleReflection_eq_generalizedReflection M cs (w * u) s v

end CoxeterGroup
