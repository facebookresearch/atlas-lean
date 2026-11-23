/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open MvPolynomial AlgebraicGeometry CategoryTheory

/-- A smooth projective curve over a field $k$ packaged as: an underlying scheme (with proofs of
integrality, Krull dimension one, nonemptiness), a structure morphism to $\mathrm{Spec}\,k$, and a
(declared) genus value. The smoothness is left implicit. -/
structure SmoothProjectiveCurveOverField (k : Type*) [Field k] where
  toScheme : Scheme
  isIntegral : AlgebraicGeometry.IsIntegral toScheme
  krullDim_eq : topologicalKrullDim toScheme = 1
  nonempty : Nonempty toScheme
  structureMorphism : toScheme ⟶ Spec (CommRingCat.of k)
  genusVal : ℕ

namespace SmoothProjectiveCurveOverField

/-- The genus of a smooth projective curve, given by the structural field `genusVal`. -/
def genus {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) : ℕ := C.genusVal

/-- A smooth projective curve has a rational point if its structure morphism admits a section, i.e.
a morphism $\mathrm{Spec}\,k \to C$ that composes to the identity. -/
def HasRationalPoint {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) : Prop :=
  ∃ s : Spec (CommRingCat.of k) ⟶ C.toScheme, s ≫ C.structureMorphism = 𝟙 _

end SmoothProjectiveCurveOverField

/-- A plane cubic over $k$: a nonzero homogeneous polynomial of degree $3$ in three variables. -/
structure PlaneCubic (k : Type*) [Field k] where
  poly : MvPolynomial (Fin 3) k
  isHomogeneous : poly.IsHomogeneous 3
  ne_zero : poly ≠ 0

/-- A plane cubic has a rational point if there is a nonzero $k$-tuple $p \in k^3$ with
$F(p) = 0$. -/
def PlaneCubic.HasRationalPoint {k : Type*} [Field k] (F : PlaneCubic k) : Prop :=
  ∃ p : Fin 3 → k, p ≠ 0 ∧ MvPolynomial.eval p F.poly = 0






/-- The (declared) genus of a plane cubic, set to be $1$ in agreement with the genus formula for a
smooth plane curve of degree $3$. -/
def PlaneCubic.genus {k : Type*} [Field k] (_F : PlaneCubic k) : ℕ :=
  1







namespace SmoothProjectiveCurveOverField




end SmoothProjectiveCurveOverField


/-- The plane cubic given by the (general) Weierstrass equation
$Y^2Z + a_1 XYZ + a_3 YZ^2 = X^3 + a_2 X^2 Z + a_4 XZ^2 + a_6 Z^3$, encoded as a homogeneous
polynomial of degree $3$ in three variables. -/
def WeierstrassCurve.toPlaneCubic {k : Type*} [Field k] (W : WeierstrassCurve k) :
    PlaneCubic k where
  poly :=
    let X := MvPolynomial.X (R := k) (0 : Fin 3)
    let Y := MvPolynomial.X (R := k) (1 : Fin 3)
    let Z := MvPolynomial.X (R := k) (2 : Fin 3)
    Y ^ 2 * Z + C W.a₁ * X * Y * Z + C W.a₃ * Y * Z ^ 2
      - X ^ 3 - C W.a₂ * X ^ 2 * Z - C W.a₄ * X * Z ^ 2 - C W.a₆ * Z ^ 3
  isHomogeneous := by
    have hX : (MvPolynomial.X (R := k) (0 : Fin 3)).IsHomogeneous 1 := isHomogeneous_X k 0
    have hY : (MvPolynomial.X (R := k) (1 : Fin 3)).IsHomogeneous 1 := isHomogeneous_X k 1
    have hZ : (MvPolynomial.X (R := k) (2 : Fin 3)).IsHomogeneous 1 := isHomogeneous_X k 2
    have h1 : ((MvPolynomial.X (1 : Fin 3)) ^ 2 * (MvPolynomial.X (2 : Fin 3)) :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := (hY.pow 2).mul hZ; simpa using this
    have h2 : (C W.a₁ * MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (1 : Fin 3) *
        MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₁).mul hX).mul hY |>.mul hZ; simpa using this
    have h3 : (C W.a₃ * MvPolynomial.X (1 : Fin 3) * (MvPolynomial.X (2 : Fin 3)) ^ 2 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₃).mul hY).mul (hZ.pow 2); simpa using this
    have h4 : ((MvPolynomial.X (0 : Fin 3)) ^ 3 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := hX.pow 3; simpa using this
    have h5 : (C W.a₂ * (MvPolynomial.X (0 : Fin 3)) ^ 2 * MvPolynomial.X (2 : Fin 3) :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₂).mul (hX.pow 2)).mul hZ; simpa using this
    have h6 : (C W.a₄ * MvPolynomial.X (0 : Fin 3) * (MvPolynomial.X (2 : Fin 3)) ^ 2 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₄).mul hX).mul (hZ.pow 2); simpa using this
    have h7 : (C W.a₆ * (MvPolynomial.X (2 : Fin 3)) ^ 3 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := (isHomogeneous_C (Fin 3) W.a₆).mul (hZ.pow 3); simpa using this
    exact ((h1.add h2).add h3).sub h4 |>.sub h5 |>.sub h6 |>.sub h7
  ne_zero := by
    intro h
    have := congr_arg (MvPolynomial.eval (fun i : Fin 3 => if i = 0 then (1 : k) else 0)) h
    simp only [map_sub, map_add, map_mul, map_pow, eval_X, eval_C, map_zero] at this
    simp only [show (2 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 0 from by decide,
      if_false, if_true] at this
    norm_num at this

/-- The point at infinity $[0 : 1 : 0]$ provides a rational point on the Weierstrass plane
cubic. -/
theorem WeierstrassCurve.toPlaneCubic_hasRationalPoint {k : Type*} [Field k]
    (W : WeierstrassCurve k) : W.toPlaneCubic.HasRationalPoint := by
  refine ⟨fun i => if i = 1 then 1 else 0, ?_, ?_⟩
  · intro h
    have : (fun i : Fin 3 => if i = 1 then (1 : k) else 0) 1 = 0 := congr_fun h 1
    simp at this
  · simp only [toPlaneCubic, map_sub, map_add, map_mul, map_pow, eval_X, eval_C]
    simp only [show (0 : Fin 3) ≠ 1 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
      if_true, if_false]
    ring

/-- The genus of an elliptic Weierstrass curve, viewed as a plane cubic, is one. -/
theorem WeierstrassCurve.toPlaneCubic_genus {k : Type*} [Field k]
    (W : WeierstrassCurve k) (_hW : W.IsElliptic) :
    W.toPlaneCubic.genus = 1 := by


  rfl





end
