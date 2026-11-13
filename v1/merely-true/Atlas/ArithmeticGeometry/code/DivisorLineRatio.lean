/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Divisors

noncomputable section

open CurveDivisor

structure EllipticCurveP2Data (C : Type*) (F : Type*) [Field F] where
  curveInst : FunctionFieldCurve C F
  Line : Type*
  lineIntersectionDivisor : Line → CurveDivisor C
  linearFormRatio : Line → Line → Fˣ
  restrictLinearForm : Line → Fˣ
  ratio_eq_mul_inv : ∀ (L₁ L₂ : Line),
    linearFormRatio L₁ L₂ = restrictLinearForm L₁ * (restrictLinearForm L₂)⁻¹

namespace EllipticCurveP2Data

variable {C : Type*} {F : Type*} [Field F]

noncomputable def pdiv (E : EllipticCurveP2Data C F) (f : Fˣ) : CurveDivisor C :=
  @CurveWithOrd.principalDivisor C F _ E.curveInst f

end EllipticCurveP2Data



namespace EllipticCurveP2Data

variable {C : Type*} {F : Type*} [Field F] (E : EllipticCurveP2Data C F)




theorem pdiv_mul (f g : Fˣ) :
    E.pdiv (f * g) = E.pdiv f + E.pdiv g := by
  simp only [pdiv]
  exact @CurveWithOrd.principalDivisor_mul C F _ E.curveInst f g

theorem pdiv_inv (f : Fˣ) :
    E.pdiv f⁻¹ = -E.pdiv f := by
  simp only [pdiv]
  exact @CurveWithOrd.principalDivisor_inv C F _ E.curveInst f



end EllipticCurveP2Data

end
