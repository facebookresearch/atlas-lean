/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.TorsionEndomorphism
import Atlas.EllipticCurves.code.DivisionPolynomials

open WeierstrassCurve.Affine

namespace DualIsogeny

variable {F : Type*} [Field F] [DecidableEq F]
variable {E₁ E₂ : WeierstrassCurve.Affine F}








end DualIsogeny

namespace DualIsogenyExt

variable {F : Type*} [Field F] [DecidableEq F]
variable {E₁ E₂ : WeierstrassCurve.Affine F}

open WeierstrassCurve.Affine

/-- An isogeny `E₁ → E₂` or the zero map (which is not an isogeny, but is needed to make
the set of "isogenies-or-zero" into a monoid). -/
inductive IsogenyOrZero (E₁ E₂ : WeierstrassCurve.Affine F) where
  | zero : IsogenyOrZero E₁ E₂
  | ofIsogeny (α : Isogeny E₁ E₂) : IsogenyOrZero E₁ E₂

/-- Converts an `IsogenyOrZero` to the underlying additive group homomorphism. -/
def IsogenyOrZero.toAddMonoidHom : IsogenyOrZero E₁ E₂ → (E₁.Point →+ E₂.Point)
  | .zero => 0
  | .ofIsogeny α => α.toAddMonoidHom

/-- The degree of an `IsogenyOrZero` (zero for the zero map, the degree of the isogeny otherwise). -/
def IsogenyOrZero.deg : IsogenyOrZero E₁ E₂ → ℕ
  | .zero => 0
  | .ofIsogeny α => α.degree



/-- The degree of the zero map is `0`. -/
@[simp]
theorem IsogenyOrZero.deg_zero :
    (IsogenyOrZero.zero : IsogenyOrZero E₁ E₂).deg = 0 :=
  rfl


/-- The degree of `ofIsogeny α` equals the degree of `α`. -/
@[simp]
theorem IsogenyOrZero.deg_ofIsogeny (α : Isogeny E₁ E₂) :
    (IsogenyOrZero.ofIsogeny α).deg = α.degree :=
  rfl

end DualIsogenyExt

namespace IsogenyDecomposition

variable {F : Type*} [Field F] [DecidableEq F]



end IsogenyDecomposition
