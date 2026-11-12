/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal

noncomputable section

open MvPolynomial Classical Module

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- Dehomogenization with respect to the 0th coordinate: substitutes `x₀ = 1` in a
homogeneous polynomial in three variables to land in the affine chart `k[x₁, x₂]`. -/
def dehomogenize₀ : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval (fun i : Fin 3 =>
    if h : i = 0 then C 1
    else X (⟨i.val - 1, by omega⟩ : Fin 2))

/-- The affine coordinates of a projective point `p` in the 0th affine chart `x₀ ≠ 0`,
obtained by dividing by the 0th homogeneous coordinate. -/
def affinePoint₀ (p : P2 k) (h₀ : Projectivization.rep p 0 ≠ 0) : Fin 2 → k :=
  fun i => Projectivization.rep p (⟨i.val + 1, by omega⟩ : Fin 3) / Projectivization.rep p 0

/-- A plane curve `X` is singular at a projective point `p` (with `p` in the chart
`x₀ ≠ 0`) if the multiplicity of its dehomogenization at the corresponding affine point
is at least two. -/
def PlaneCurve.IsSingularAt (X : PlaneCurve k) (p : P2 k)
    (h₀ : Projectivization.rep p 0 ≠ 0)
    (hf : dehomogenize₀ k X.poly ≠ 0) : Prop :=
  hypersurfaceMultiplicity k (dehomogenize₀ k X.poly) (affinePoint₀ k p h₀) hf ≥ 2

/-- Projective intersection multiplicity of two plane curves at a point `p` (in the
`x₀ ≠ 0` chart), defined as the affine intersection multiplicity of their
dehomogenizations. -/
def projIntersectionMultiplicity (X Y : PlaneCurve k) (p : P2 k)
    (h₀ : Projectivization.rep p 0 ≠ 0)
    [Module.Finite k (CurveQuotient k (dehomogenize₀ k X.poly) (dehomogenize₀ k Y.poly))] :
    ℕ :=
  intersectionMultiplicity k
    (dehomogenize₀ k X.poly) (dehomogenize₀ k Y.poly) (affinePoint₀ k p h₀)






end Lec5BezoutPascal

end
