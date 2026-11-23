/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.EllipticCurves

universe u

noncomputable section

variable (k : Type u) [Field k] [IsAlgClosed k]

namespace AlgebraicGeometry.CompletenessValuationCriterion

/-- The one-point algebraic variety: $\mathrm{Spec}(k)$ as an `AlgVariety`, with function field $k$ and the trivial topology. -/
def pointAlgVariety : AlgVariety k where
  carrier := PUnit.{u + 1}
  topInst := ⊥
  functionField := k
  ffField := inferInstance
  baseEmbed := RingHom.id k
  baseEmbed_inj := Function.injective_id
  localRingAt := fun _ => ⊤
  base_le_localRing := fun _ _ => Subring.mem_top _
  noethProduct := fun Y _ _ => by


    apply TopologicalSpace.noetherianSpace_of_surjective (fun y : Y => (PUnit.unit, y))
    · exact continuous_const.prodMk continuous_id
    · intro ⟨u, y⟩
      exact ⟨y, Prod.ext (Subsingleton.elim _ _) rfl⟩

/-- The point is a projective variety: $\mathrm{Spec}(k) = \mathbb{P}^0$, with the unique homogeneous coordinate $1 \neq 0$. -/
def pointIsProjectiveVariety : IsProjectiveVariety (pointAlgVariety k) where
  n := 0
  homogCoords := fun _ _ => 1
  homogCoords_ne_zero := fun _ _ => one_ne_zero

end AlgebraicGeometry.CompletenessValuationCriterion
open AlgebraicGeometry.CompletenessValuationCriterion in
/-- $\mathrm{PUnit}$ (the one-point space) is a projective variety over any algebraically closed field $k$. -/
def IsProjectiveVariety.punit : IsProjectiveVariety k PUnit.{u + 1} where
  exists_algVariety_projective :=
    ⟨‹IsAlgClosed k›, pointAlgVariety k, rfl, ⟨rfl, ⟨pointIsProjectiveVariety k⟩⟩⟩

end
