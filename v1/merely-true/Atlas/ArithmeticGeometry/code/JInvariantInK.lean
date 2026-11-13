/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.JInvariant

noncomputable section

universe u

open WeierstrassCurve

variable {k : Type u} [Field k]


theorem GenusOneCurve.jInvariant_in_k (C : GenusOneCurve k)
    (O : C.PointOverAlgClosure) :
    (C.ellipticCurveAtBasePoint O).jInvariant ∈
      Set.range (algebraMap k (AlgebraicClosure k)) :=
  ⟨C.jInvariant, by


    unfold ellipticCurveAtBasePoint EllipticCurveOver.jInvariant GenusOneCurve.jInvariant
    rw [variableChange_j]
    exact (C.Jacobian.curve.map_j (algebraMap k (AlgebraicClosure k))).symm⟩

end
