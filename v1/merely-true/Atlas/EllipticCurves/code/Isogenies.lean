/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Squarefree.Basic

open Polynomial

open scoped Polynomial.Bivariate

universe u v

namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- The (affine) coordinate ring of a plane curve cut out by a bivariate polynomial
`f₀ ∈ k[X][Y]`, defined as the quotient `k[X][Y]/(f₀)` via `AdjoinRoot`. -/
noncomputable abbrev CoordinateRing (f₀ : k[X][Y]) : Type u :=
  AdjoinRoot f₀

/-- The function field of a plane curve, defined as the field of fractions of its
coordinate ring `k[X][Y]/(f₀)`. -/
noncomputable abbrev FunctionField (f₀ : k[X][Y]) : Type u :=
  FractionRing (CoordinateRing f₀)

/-- If the defining polynomial `f₀` of the curve is prime, then the coordinate ring
`k[X][Y]/(f₀)` is an integral domain. -/
noncomputable instance CoordinateRing.isDomain (f₀ : k[X][Y]) (hf : Prime f₀) :
    IsDomain (CoordinateRing f₀) :=
  AdjoinRoot.isDomain_of_prime hf

/-- When `f₀` is prime, the function field of the curve is a genuine field, obtained
as the fraction field of the integral coordinate ring. -/
noncomputable instance FunctionField.instField (f₀ : k[X][Y]) [h : Fact (Prime f₀)] :
    Field (FunctionField f₀) := by
  letI : IsDomain (CoordinateRing f₀) := CoordinateRing.isDomain f₀ h.out
  exact inferInstance

/-- The ring homomorphism that dehomogenizes a polynomial in three projective
variables by setting the third coordinate to `1`, sending `X₀ ↦ X`, `X₁ ↦ Y`,
`X₂ ↦ 1`. -/
noncomputable def dehomogenizeHom (k : Type u) [CommRing k] :
    MvPolynomial (Fin 3) k →+* k[X][Y] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C : k →+* k[X][Y])
    (![Polynomial.C Polynomial.X, Polynomial.X, 1])

/-- Dehomogenize a homogeneous polynomial in `MvPolynomial (Fin 3) k` to a bivariate
polynomial in `k[X][Y]` by substituting `Z = 1`. -/
noncomputable def dehomogenize (f : MvPolynomial (Fin 3) k) : k[X][Y] :=
  dehomogenizeHom k f

/-- Dehomogenization sends the projective coordinate `X₀` to the bivariate
polynomial `X`. -/
@[simp]
lemma dehomogenize_X_zero : dehomogenize (MvPolynomial.X (R := k) (0 : Fin 3)) =
    Polynomial.C Polynomial.X := by
  simp [dehomogenize, dehomogenizeHom, MvPolynomial.eval₂Hom_X']

/-- Dehomogenization sends the projective coordinate `X₁` to the bivariate
polynomial `Y`. -/
@[simp]
lemma dehomogenize_X_one : dehomogenize (MvPolynomial.X (R := k) (1 : Fin 3)) =
    (Polynomial.X : k[X][Y]) := by
  simp [dehomogenize, dehomogenizeHom, MvPolynomial.eval₂Hom_X']

/-- Dehomogenization sends the projective coordinate `X₂` (the homogenizing
variable) to `1`. -/
@[simp]
lemma dehomogenize_X_two : dehomogenize (MvPolynomial.X (R := k) (2 : Fin 3)) =
    (1 : k[X][Y]) := by
  simp [dehomogenize, dehomogenizeHom, MvPolynomial.eval₂Hom_X']

/-- Dehomogenization sends the constant `a ∈ k` to itself viewed as a constant in
`k[X][Y]`. -/
@[simp]
lemma dehomogenize_C (a : k) : dehomogenize (MvPolynomial.C a : MvPolynomial (Fin 3) k) =
    Polynomial.C (Polynomial.C a) := by
  simp [dehomogenize, dehomogenizeHom]

/-- The coordinate ring of the affine chart `{Z = 1}` of a projective plane curve
defined by a homogeneous polynomial `f ∈ k[X₀, X₁, X₂]`. -/
noncomputable abbrev CoordinateRingOfHomog (f : MvPolynomial (Fin 3) k) : Type u :=
  CoordinateRing (dehomogenize f)

/-- The function field of a projective plane curve obtained as the fraction field
of the affine coordinate ring of its `{Z = 1}` chart. -/
noncomputable abbrev FunctionFieldOfHomog (f : MvPolynomial (Fin 3) k) : Type u :=
  FunctionField (dehomogenize f)

/-- An affine point of the curve `f₀ = 0` over an extension algebra `L` of `k`,
consisting of coordinates `x, y ∈ L` satisfying the defining equation. -/
structure AffinePointOver (f₀ : k[X][Y]) (L : Type v) [CommRing L] [Algebra k L] where
  x : L
  y : L
  on_curve : Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k L) x) y f₀ = 0

/-- Evaluation ring homomorphism from the coordinate ring `k[X][Y]/(f₀)` to `L`
induced by a point `P = (x, y)` of the curve over `L`. -/
noncomputable def AffinePointOver.evalRingHom {f₀ : k[X][Y]} {L : Type v}
    [CommRing L] [Algebra k L]
    (P : AffinePointOver f₀ L) : CoordinateRing f₀ →+* L :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap k L) P.x) P.y P.on_curve

/-- Evaluating a class `[p] ∈ k[X][Y]/(f₀)` at a point `P` of the curve agrees with
substituting `P.x, P.y` into the representative `p`. -/
@[simp]
lemma AffinePointOver.evalRingHom_mk {f₀ : k[X][Y]} {L : Type v}
    [CommRing L] [Algebra k L]
    (P : AffinePointOver f₀ L) (p : k[X][Y]) :
    P.evalRingHom (AdjoinRoot.mk f₀ p) =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k L) P.x) P.y p :=
  AdjoinRoot.lift_mk P.on_curve p

/-- An affine point of `f₀ = 0` with coordinates in the base ring `k`. -/
structure AffinePoint (f₀ : k[X][Y]) where
  x : k
  y : k
  on_curve : Polynomial.eval₂ (Polynomial.evalRingHom x) y f₀ = 0

/-- Evaluation ring homomorphism from the coordinate ring `k[X][Y]/(f₀)` to the
base ring `k` induced by an affine point `P`. -/
noncomputable def AffinePoint.evalRingHom {f₀ : k[X][Y]} (P : AffinePoint f₀) :
    CoordinateRing f₀ →+* k :=
  AdjoinRoot.lift (Polynomial.evalRingHom P.x) P.y P.on_curve

/-- Evaluating a class `[p] ∈ k[X][Y]/(f₀)` at an affine `k`-point `P` agrees with
substituting `P.x, P.y` into the representative `p`. -/
@[simp]
lemma AffinePoint.evalRingHom_mk {f₀ : k[X][Y]} (P : AffinePoint f₀) (p : k[X][Y]) :
    P.evalRingHom (AdjoinRoot.mk f₀ p) =
      Polynomial.eval₂ (Polynomial.evalRingHom P.x) P.y p :=
  AdjoinRoot.lift_mk P.on_curve p

/-- The two-variable evaluation map `eval₂RingHom (algebraMap k k) a` coincides
with `Polynomial.evalRingHom a`, since `algebraMap k k = id`. -/
lemma eval₂RingHom_algebraMap_self (a : k) :
    Polynomial.eval₂RingHom (algebraMap k k) a = Polynomial.evalRingHom a := by
  ext p
  · simp [eval₂_C]
  · simp [eval₂_X]

/-- Coerce a `k`-rational affine point into an affine point over `k` viewed as a
`k`-algebra. -/
def AffinePoint.toOver {f₀ : k[X][Y]} (P : AffinePoint f₀) : AffinePointOver f₀ k where
  x := P.x
  y := P.y
  on_curve := by rw [eval₂RingHom_algebraMap_self]; exact P.on_curve

/-- A function `φ` on the curve is regular at an `L`-point `P` if it can be written
as `g/h` with `h` not vanishing at `P`. -/
def FunctionField.IsRegularAtOver {f₀ : k[X][Y]} {L : Type v} [CommRing L] [Algebra k L]
    (φ : FunctionField f₀) (P : AffinePointOver f₀ L) : Prop :=
  ∃ (g : CoordinateRing f₀) (h : ↥(nonZeroDivisors (CoordinateRing f₀))),
    φ = IsLocalization.mk' (FunctionField f₀) g h ∧
    P.evalRingHom (h : CoordinateRing f₀) ≠ 0

/-- A function on the curve is regular at a `k`-rational affine point `P` if it
admits a representation `g/h` with `h(P) ≠ 0`. -/
def FunctionField.IsRegularAt {f₀ : k[X][Y]}
    (φ : FunctionField f₀) (P : AffinePoint f₀) : Prop :=
  ∃ (g : CoordinateRing f₀) (h : ↥(nonZeroDivisors (CoordinateRing f₀))),
    φ = IsLocalization.mk' (FunctionField f₀) g h ∧
    P.evalRingHom (h : CoordinateRing f₀) ≠ 0

/-- A function `φ` is regular and nonzero at a `k`-rational affine point `P` if it
has a representation `g/h` with `h(P) ≠ 0` and `g(P) ≠ 0`. -/
def FunctionField.IsRegularNonzeroAt {f₀ : k[X][Y]}
    (φ : FunctionField f₀) (P : AffinePoint f₀) : Prop :=
  ∃ (g : CoordinateRing f₀) (h : ↑(nonZeroDivisors (CoordinateRing f₀))),
    φ = IsLocalization.mk' (FunctionField f₀) g h ∧
    P.evalRingHom (h : CoordinateRing f₀) ≠ 0 ∧
    P.evalRingHom g ≠ 0

set_option synthInstance.maxHeartbeats 40000 in
/-- Bivariate evaluation: evaluate `f ∈ k[X][Y]` at scalars `(a, b) ∈ R × R` for a
`k`-algebra `R`, by mapping coefficients via `algebraMap k R`. -/
noncomputable def evalBivariate {R : Type u} [CommRing R] [Algebra k R]
    (f : k[X][Y]) (a b : R) : R :=
  Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k R) a) b f

set_option synthInstance.maxHeartbeats 40000 in
/-- A rational map from the curve `f₁ = 0` to the curve `f₂ = 0`, represented by a
triple of elements `(φ₁ : φ₂ : φ₃)` in the function field of `f₁`, not all zero,
such that whenever `(φ₁ : φ₂ : φ₃)` is defined at a point with `φ₃ ≠ 0`, the image
lies on `f₂`. -/
structure RationalMap (f₁ f₂ : k[X][Y]) [IsDomain (CoordinateRing f₁)] where
  φ₁ : FunctionField f₁
  φ₂ : FunctionField f₁
  φ₃ : FunctionField f₁
  not_all_zero : φ₁ ≠ 0 ∨ φ₂ ≠ 0 ∨ φ₃ ≠ 0
  image_on_curve :
    ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
    ∀ (P : AffinePointOver f₁ K),
    ∀ (g₁ g₂ g₃ : CoordinateRing f₁)
      (h : ↥(nonZeroDivisors (CoordinateRing f₁))),
    φ₁ = IsLocalization.mk' (FunctionField f₁) g₁ h →
    φ₂ = IsLocalization.mk' (FunctionField f₁) g₂ h →
    φ₃ = IsLocalization.mk' (FunctionField f₁) g₃ h →
    P.evalRingHom (h : CoordinateRing f₁) ≠ 0 →
    (P.evalRingHom g₁ ≠ 0 ∨ P.evalRingHom g₂ ≠ 0 ∨ P.evalRingHom g₃ ≠ 0) →
    P.evalRingHom g₃ ≠ 0 →
    evalBivariate f₂ (P.evalRingHom g₁ / P.evalRingHom g₃)
      (P.evalRingHom g₂ / P.evalRingHom g₃) = 0

/-- A rational map `φ` is regular at an affine `k`-point `P` if there is a
nonzero scalar `μ` in the function field such that all three coordinates `μ·φᵢ`
are regular at `P` and at least one is regular and nonzero there. -/
def RationalMap.IsRegularAt {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]
    (φ : RationalMap f₁ f₂) (P : AffinePoint f₁) : Prop :=
  ∃ (μ : FunctionField f₁), μ ≠ 0 ∧
    (μ * φ.φ₁).IsRegularAt P ∧
    (μ * φ.φ₂).IsRegularAt P ∧
    (μ * φ.φ₃).IsRegularAt P ∧
    ((μ * φ.φ₁).IsRegularNonzeroAt P ∨
     (μ * φ.φ₂).IsRegularNonzeroAt P ∨
     (μ * φ.φ₃).IsRegularNonzeroAt P)

/-- Field-valued version of `IsRegularNonzeroAt`: a function is regular and nonzero
at an `L`-point `P` if it equals `g/h` for `h(P) ≠ 0` and `g(P) ≠ 0`. -/
def FunctionField.IsRegularNonzeroAtOver {f₀ : k[X][Y]} {K : Type u}
    [Field K] [Algebra k K]
    (φ : FunctionField f₀) (P : AffinePointOver f₀ K) : Prop :=
  ∃ (g : CoordinateRing f₀) (h : ↥(nonZeroDivisors (CoordinateRing f₀))),
    φ = IsLocalization.mk' (FunctionField f₀) g h ∧
    P.evalRingHom (h : CoordinateRing f₀) ≠ 0 ∧
    P.evalRingHom g ≠ 0

/-- Field-valued regularity for rational maps: there exists a rescaling `μ` so that
each coordinate is regular at `P` and at least one is regular and nonzero. -/
def RationalMap.IsRegularAtOver {f₁ f₂ : k[X][Y]}
    [IsDomain (CoordinateRing f₁)]
    (φ : RationalMap f₁ f₂) {K : Type u} [Field K] [Algebra k K]
    (P : AffinePointOver f₁ K) : Prop :=
  ∃ (μ : FunctionField f₁), μ ≠ 0 ∧
    (μ * φ.φ₁).IsRegularAtOver P ∧
    (μ * φ.φ₂).IsRegularAtOver P ∧
    (μ * φ.φ₃).IsRegularAtOver P ∧
    ((μ * φ.φ₁).IsRegularNonzeroAtOver P ∨
     (μ * φ.φ₂).IsRegularNonzeroAtOver P ∨
     (μ * φ.φ₃).IsRegularNonzeroAtOver P)

/-- A projective point on the curve `f₀ = 0` over an extension field `K`, either an
affine point or a point at infinity given by a nonzero direction `(a, b)`. -/
inductive ProjectiveCurvePointOver (f₀ : k[X][Y]) (K : Type u) [Field K] [Algebra k K]
  |     affine : AffinePointOver f₀ K → ProjectiveCurvePointOver f₀ K
  |     atInfinity : (a : K) → (b : K) → (a ≠ 0 ∨ b ≠ 0) →
      ProjectiveCurvePointOver f₀ K

/-- Regularity of a rational map at a projective point: in the affine case use
`IsRegularAtOver`; at infinity, require that some scaling makes all coordinates
into a common ratio whose numerators are not all zero. -/
def RationalMap.IsRegularAtProjectivePoint {f₁ f₂ : k[X][Y]}
    [IsDomain (CoordinateRing f₁)]
    (φ : RationalMap f₁ f₂) {K : Type u} [Field K] [Algebra k K]
    (P : ProjectiveCurvePointOver f₁ K) : Prop :=
  match P with
  | .affine Q => φ.IsRegularAtOver Q
  | .atInfinity _a _b _hab =>
    ∃ (g₁ g₂ g₃ : CoordinateRing f₁)
      (h : ↥(nonZeroDivisors (CoordinateRing f₁))),
      (∃ (μ : FunctionField f₁), μ ≠ 0 ∧
        μ * φ.φ₁ = IsLocalization.mk' (FunctionField f₁) g₁ h ∧
        μ * φ.φ₂ = IsLocalization.mk' (FunctionField f₁) g₂ h ∧
        μ * φ.φ₃ = IsLocalization.mk' (FunctionField f₁) g₃ h) ∧
      (g₁ ≠ 0 ∨ g₂ ≠ 0 ∨ g₃ ≠ 0)

/-- A rational map is a *morphism* if it is regular at every projective point of
the source curve over every algebraically closed extension. -/
def RationalMap.IsMorphism {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]
    (φ : RationalMap f₁ f₂) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
    ∀ P : ProjectiveCurvePointOver f₁ K,
      φ.IsRegularAtProjectivePoint P

/-- A morphism of plane curves is a rational map together with a proof that it is
regular everywhere. -/
structure Morphism (f₁ f₂ : k[X][Y]) [IsDomain (CoordinateRing f₁)]
    extends RationalMap f₁ f₂ where
  regular_everywhere : toRationalMap.IsMorphism

/-- The underlying rational map of a `Morphism` is, by construction, a morphism. -/
theorem Morphism.isMorphism {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]
    (φ : Morphism f₁ f₂) : φ.toRationalMap.IsMorphism :=
  φ.regular_everywhere

/-- Partial derivative with respect to `Y` of a bivariate polynomial in `k[X][Y]`,
implemented as the formal derivative in the outer (Y) variable. -/
noncomputable def partialDerivY (f₀ : k[X][Y]) : k[X][Y] :=
  Polynomial.derivative f₀

/-- Partial derivative with respect to `X` of a bivariate polynomial in `k[X][Y]`,
obtained by differentiating each coefficient. -/
noncomputable def partialDerivX (f₀ : k[X][Y]) : k[X][Y] :=
  f₀.sum fun n c => Polynomial.C (Polynomial.derivative c) * Polynomial.X ^ n

/-- A plane curve `f₀ = 0` is *smooth* if at every affine `k`-point at least one
of the two partial derivatives is nonzero. -/
def IsSmooth (f₀ : k[X][Y]) : Prop :=
  ∀ P : AffinePoint f₀,
    Polynomial.eval₂ (Polynomial.evalRingHom P.x) P.y (partialDerivX f₀) ≠ 0 ∨
    Polynomial.eval₂ (Polynomial.evalRingHom P.x) P.y (partialDerivY f₀) ≠ 0


section MorphismSurjectiveOrConstant

variable {k : Type u} [Field k] {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]

/-- A morphism `φ` maps an affine point `P` of the source to an affine point `Q`
of the target if the three coordinate ratios can be rescaled to send `P` to `Q`. -/
def Morphism.MapsTo (φ : Morphism f₁ f₂) (P : AffinePoint f₁) (Q : AffinePoint f₂) : Prop :=
  ∃ (μ : FunctionField f₁) (_ : μ ≠ 0)
    (g₁ : CoordinateRing f₁) (h₁ : ↥(nonZeroDivisors (CoordinateRing f₁)))
    (g₂ : CoordinateRing f₁) (h₂ : ↥(nonZeroDivisors (CoordinateRing f₁)))
    (g₃ : CoordinateRing f₁) (h₃ : ↥(nonZeroDivisors (CoordinateRing f₁))),
    μ * φ.φ₁ = IsLocalization.mk' (FunctionField f₁) g₁ h₁ ∧
    μ * φ.φ₂ = IsLocalization.mk' (FunctionField f₁) g₂ h₂ ∧
    μ * φ.φ₃ = IsLocalization.mk' (FunctionField f₁) g₃ h₃ ∧
    P.evalRingHom (h₁ : CoordinateRing f₁) ≠ 0 ∧
    P.evalRingHom (h₂ : CoordinateRing f₁) ≠ 0 ∧
    P.evalRingHom (h₃ : CoordinateRing f₁) ≠ 0 ∧
    P.evalRingHom g₃ ≠ 0 ∧
    Q.x * (P.evalRingHom (h₁ : CoordinateRing f₁) * P.evalRingHom g₃) =
      P.evalRingHom g₁ * P.evalRingHom (h₃ : CoordinateRing f₁) ∧
    Q.y * (P.evalRingHom (h₂ : CoordinateRing f₁) * P.evalRingHom g₃) =
      P.evalRingHom g₂ * P.evalRingHom (h₃ : CoordinateRing f₁)

/-- A morphism is surjective on affine `k`-points if every target affine point has
at least one preimage. -/
def Morphism.IsSurjective (φ : Morphism f₁ f₂) : Prop :=
  ∀ Q : AffinePoint f₂, ∃ P : AffinePoint f₁, φ.MapsTo P Q

/-- A morphism is constant if there is a single target point that every source
point is mapped to. -/
def Morphism.IsConstant (φ : Morphism f₁ f₂) : Prop :=
  ∃ Q₀ : AffinePoint f₂, ∀ P : AffinePoint f₁, φ.MapsTo P Q₀

end MorphismSurjectiveOrConstant


section RationalMapNonConstant

variable {k : Type u} [Field k] {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]

/-- A rational map `φ` is non-constant if the affine ratios `φ₁/φ₃` and `φ₂/φ₃` do
not both lie in the image of the constant map `k → k(f₁)`. -/
def RationalMap.IsNonConstant (φ : RationalMap f₁ f₂) : Prop :=
  ¬ ∃ (a b : k), φ.φ₁ / φ.φ₃ = algebraMap k (FunctionField f₁) a ∧
                  φ.φ₂ / φ.φ₃ = algebraMap k (FunctionField f₁) b

end RationalMapNonConstant

/-- The projective plane `ℙ²(L)` over a field `L`, modeled as the projectivization
of `Fin 3 → L`. -/
abbrev ProjectivePlane (L : Type*) [Field L] : Type _ :=
  Projectivization L (Fin 3 → L)

/-- A point `P` of the projective plane `ℙ²(L)` lies on the projective curve cut
out by a homogeneous polynomial `f ∈ k[X₀, X₁, X₂]` if `f` vanishes on any
representative of `P`. -/
def ProjectivePointOnCurve (f : MvPolynomial (Fin 3) k) (L : Type*) [Field L] [Algebra k L]
    (P : ProjectivePlane L) : Prop :=
  MvPolynomial.aeval P.rep f = 0

/-- The set of `L`-points of the projective curve `f = 0`. -/
def ProjectiveCurvePoints (f : MvPolynomial (Fin 3) k)
    (L : Type*) [Field L] [Algebra k L] : Set (ProjectivePlane L) :=
  {P | ProjectivePointOnCurve f L P}

section FieldExtensions₃
variable {k : Type u} [Field k]

/-- Points of the projective curve `f = 0` over the algebraic closure of `k`. -/
noncomputable def AlgClosurePoints (f : MvPolynomial (Fin 3) k) :
    Set (ProjectivePlane (AlgebraicClosure k)) :=
  ProjectiveCurvePoints f (AlgebraicClosure k)

end FieldExtensions₃

/-- Unfolding lemma for membership in `ProjectiveCurvePoints`: a projective point
`P` lies on `f = 0` iff `f` evaluates to zero on its representative. -/
@[simp]
lemma mem_projectiveCurvePoints_iff {f : MvPolynomial (Fin 3) k} {L : Type*}
    [Field L] [Algebra k L] {P : ProjectivePlane L} :
    P ∈ ProjectiveCurvePoints f L ↔ MvPolynomial.aeval P.rep f = 0 :=
  Iff.rfl

/-- An element of the function field of the projective curve `f = 0` is regular
at a projective point `P` if it can be expressed as a ratio `g/h` of homogeneous
polynomials of equal degree with `h` not vanishing on `P`. -/
def FunctionFieldOfHomog.IsRegularAt
    {f : MvPolynomial (Fin 3) k} {L : Type v} [Field L] [Algebra k L]
    (α : FunctionFieldOfHomog f) (P : ProjectivePlane L)
    (_hP : P ∈ ProjectiveCurvePoints f L) : Prop :=
  ∃ (g h : MvPolynomial (Fin 3) k) (d : ℕ),
    g.IsHomogeneous d ∧
    h.IsHomogeneous d ∧
    MvPolynomial.aeval P.rep h ≠ 0 ∧
    ∃ (hh : AdjoinRoot.mk (dehomogenize f) (dehomogenizeHom k h) ∈
        nonZeroDivisors (CoordinateRingOfHomog f)),
      α = IsLocalization.mk'
        (FunctionFieldOfHomog f)
        (AdjoinRoot.mk (dehomogenize f) (dehomogenizeHom k g))
        ⟨AdjoinRoot.mk (dehomogenize f) (dehomogenizeHom k h), hh⟩

/-- Embed an affine point `(a, b) ∈ L²` into the projective plane `ℙ²(L)` as the
point `[a : b : 1]`. -/
noncomputable def affineToProjective {L : Type*} [Field L]
    (a b : L) : ProjectivePlane L :=
  Projectivization.mk L (![a, b, 1] : Fin 3 → L) (by
    intro h
    have : (![a, b, (1 : L)] : Fin 3 → L) 2 = (0 : Fin 3 → L) 2 := congr_fun h 2
    simp [Matrix.cons_val_two, Matrix.head_cons] at this)

section FieldExtensions₄
variable {k : Type u} [Field k]

/-- The projective plane over the function field of a plane curve `f₁`. -/
noncomputable abbrev ProjectivePlaneOfFunctionField (f₁ : k[X][Y])
    [IsDomain (CoordinateRing f₁)] [Fact (Prime f₁)] : Type u :=
  ProjectivePlane (FunctionField f₁)

end FieldExtensions₄

end ProjectiveCurve

/-- Data for an isogeny `α : E₁ → E₂` in *standard form*: rational functions
`u, v, s, t ∈ F[X]` such that the `x`-coordinate transforms as `u/v` and the
`y`-coordinate transforms as `(s/t)·y`, with the coprimality and nonvanishing
conditions required for this to be in lowest terms. -/
structure IsogenyStandardForm (F : Type u) [Field F] where
  u : F[X]
  v : F[X]
  s : F[X]
  t : F[X]
  v_ne_zero : v ≠ 0
  t_ne_zero : t ≠ 0
  coprime_uv : IsCoprime u v
  coprime_st : IsCoprime s t

namespace IsogenyStandardForm

variable {F : Type u} [Field F]

/-- The degree of an isogeny in standard form: `deg α := max (deg u) (deg v)`
(see Definition for Theorem 5.22 / standard-form degree). -/
noncomputable def degree (α : IsogenyStandardForm F) : ℕ :=
  max α.u.natDegree α.v.natDegree

/-- An isogeny in standard form is *separable* if `u'v - uv' ≠ 0`. -/
def IsSeparable (α : IsogenyStandardForm F) : Prop :=
  Polynomial.derivative α.u * α.v - α.u * Polynomial.derivative α.v ≠ 0

/-- An isogeny is *inseparable* if it is not separable. -/
def IsInseparable (α : IsogenyStandardForm F) : Prop :=
  ¬ α.IsSeparable

end IsogenyStandardForm

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)

/-- The coordinate ring of a Weierstrass curve `W` (in the sense of Mathlib's
`WeierstrassCurve.Affine.CoordinateRing`) agrees definitionally with the
`ProjectiveCurve.CoordinateRing` of its defining bivariate polynomial. -/
lemma coordinateRing_eq :
    W.CoordinateRing = ProjectiveCurve.CoordinateRing W.polynomial := rfl

/-- The function field of a Weierstrass curve is a field. -/
noncomputable instance : Field W.FunctionField := inferInstance

/-- The function field of a Weierstrass curve is the fraction field of its
coordinate ring. -/
noncomputable instance : IsFractionRing W.CoordinateRing W.FunctionField := inferInstance

end WeierstrassCurve.Affine

/-- The transcendence degree of a field extension `L/K`, as a cardinal. -/
noncomputable abbrev Field.transcendenceDegree
    (K : Type u) (L : Type*) [Field K] [Field L] [Algebra K L] : Cardinal :=
  Algebra.trdeg K L

/-- An isogeny `E₁ → E₂` between Weierstrass curves: a surjective group
homomorphism between their group-of-points along with a positive integer
"degree" attribute. (See Sutherland, definitions surrounding §5.1 — an isogeny
is a surjective morphism of elliptic curves that sends the identity to the
identity.) -/
structure Isogeny {F : Type u} [Field F] [DecidableEq F]
    (E₁ E₂ : WeierstrassCurve.Affine F) where
  toAddMonoidHom : E₁.Point →+ E₂.Point
  surjective : Function.Surjective toAddMonoidHom
  degree : ℕ
  degree_pos : 0 < degree

namespace Isogeny

variable {F : Type u} [Field F] [DecidableEq F]
variable {E₁ E₂ E₃ : WeierstrassCurve.Affine F}

/-- An isogeny may be applied to points like a function. -/
instance : CoeFun (Isogeny E₁ E₂) (fun _ => E₁.Point → E₂.Point) where
  coe φ := φ.toAddMonoidHom

/-- Isogenies are group homomorphisms: `φ (P + Q) = φ P + φ Q`. -/
theorem map_add (φ : Isogeny E₁ E₂) (P Q : E₁.Point) : φ (P + Q) = φ P + φ Q :=
  φ.toAddMonoidHom.map_add P Q

/-- Isogenies send the identity to the identity. -/
@[simp]
theorem map_zero (φ : Isogeny E₁ E₂) : φ (0 : E₁.Point) = 0 :=
  φ.toAddMonoidHom.map_zero

/-- Isogenies commute with negation. -/
@[simp]
theorem map_neg (φ : Isogeny E₁ E₂) (P : E₁.Point) : φ (-P) = -φ P :=
  φ.toAddMonoidHom.map_neg P

/-- Two elliptic curves are *isogenous* if there is at least one isogeny from the
first to the second. -/
def IsIsogenous (E₁ E₂ : WeierstrassCurve.Affine F) : Prop :=
  Nonempty (Isogeny E₁ E₂)

/-- Composition of isogenies: `comp ψ φ` applies `φ` then `ψ` and multiplies the
recorded degrees. -/
def comp (ψ : Isogeny E₂ E₃) (φ : Isogeny E₁ E₂) : Isogeny E₁ E₃ where
  toAddMonoidHom := ψ.toAddMonoidHom.comp φ.toAddMonoidHom
  surjective := ψ.surjective.comp φ.surjective
  degree := ψ.degree * φ.degree
  degree_pos := Nat.mul_pos ψ.degree_pos φ.degree_pos

/-- The composition of isogenies acts pointwise as the composition of functions. -/
@[simp]
lemma comp_apply (ψ : Isogeny E₂ E₃) (φ : Isogeny E₁ E₂) (P : E₁.Point) :
    (comp ψ φ) P = ψ (φ P) := rfl

/-- The identity isogeny on a Weierstrass curve, of degree 1. -/
def id (E : WeierstrassCurve.Affine F) : Isogeny E E where
  toAddMonoidHom := AddMonoidHom.id E.Point
  surjective := Function.surjective_id
  degree := 1
  degree_pos := Nat.one_pos

/-- The identity isogeny acts as the identity function on points. -/
@[simp]
lemma id_apply (E : WeierstrassCurve.Affine F) (P : E.Point) : (Isogeny.id E) P = P := rfl

/-- An isogeny is an *isomorphism* if it admits a two-sided inverse isogeny. -/
def IsIsomorphism (φ : Isogeny E₁ E₂) : Prop :=
  ∃ (ψ : Isogeny E₂ E₁), (∀ P, ψ (φ P) = P) ∧ (∀ Q, φ (ψ Q) = Q)

/-- Two elliptic curves are *isomorphic* if there is a pair of mutually-inverse
isogenies between them. -/
def IsIsomorphic (E₁ E₂ : WeierstrassCurve.Affine F) : Prop :=
  ∃ (φ : Isogeny E₁ E₂) (ψ : Isogeny E₂ E₁),
    (∀ P, ψ (φ P) = P) ∧ (∀ Q, φ (ψ Q) = Q)

/-- The extension degree `[k(E₁) : k(E₂)]` of function fields associated to an
isogeny `φ : E₁ → E₂`, computed via `Module.finrank`. -/
noncomputable def extensionDegree
    (_φ : Isogeny E₁ E₂)
    [Algebra E₂.FunctionField E₁.FunctionField] : ℕ :=
  Module.finrank E₂.FunctionField E₁.FunctionField

end Isogeny

/-- A rational map between the Weierstrass curves underlying `E₁` and `E₂` sends
the base point (the point at infinity) of `E₁` to the base point of `E₂` if the
second coordinate `φ₂` is nonzero and the ratios `φ₁/φ₂`, `φ₃/φ₂` come from the
coordinate ring (so the rational map is regular at infinity, where the third
coordinate vanishes). -/
def ProjectiveCurve.RationalMap.SendsBasePointToBasePoint
    {F : Type u} [Field F] {E₁ E₂ : WeierstrassCurve.Affine F}
    [IsDomain (ProjectiveCurve.CoordinateRing E₁.polynomial)]
    (φ : ProjectiveCurve.RationalMap E₁.polynomial E₂.polynomial) : Prop :=
  φ.φ₂ ≠ 0 ∧
    φ.φ₁ * φ.φ₂⁻¹ ∈ Set.range
      (algebraMap (ProjectiveCurve.CoordinateRing E₁.polynomial)
        (ProjectiveCurve.FunctionField E₁.polynomial)) ∧
    φ.φ₃ * φ.φ₂⁻¹ ∈ Set.range
      (algebraMap (ProjectiveCurve.CoordinateRing E₁.polynomial)
        (ProjectiveCurve.FunctionField E₁.polynomial))

/-- Alternative geometric definition of an isogeny: a non-constant rational map
between Weierstrass curves which sends the base point to the base point. -/
structure IsogenyAlt {F : Type u} [Field F] [DecidableEq F]
    (E₁ E₂ : WeierstrassCurve.Affine F) where
  toRationalMap : ProjectiveCurve.RationalMap E₁.polynomial E₂.polynomial
  nonConstant : toRationalMap.IsNonConstant
  sendsBasePointToBasePoint : toRationalMap.SendsBasePointToBasePoint


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

/-- An isogeny in standard form together with curve data: the polynomial `f₁ = x³
+ ax + b` of the source curve, an auxiliary polynomial `w`, and the identity
`v³ · (s²f₁) = t² · w` (along with `IsCoprime v w` and `Squarefree f₁`). This
packages the algebraic conditions needed to prove the divisibility lemma
`v³ ∣ t²`. -/
structure WithCurveData (F : Type u) [Field F] extends IsogenyStandardForm F where
  f₁ : F[X]
  w : F[X]
  identity : v ^ 3 * (s ^ 2 * f₁) = t ^ 2 * w
  coprime_vw : IsCoprime v w
  squarefree_f₁ : Squarefree f₁

namespace WithCurveData

variable (α : WithCurveData F)

/-- From the identity `v³(s²f₁) = t²w` with `gcd(v, w) = 1` we deduce `v³ ∣ t²`. -/
theorem v_cube_dvd_t_sq : α.v ^ 3 ∣ α.t ^ 2 := by
  have hvw : IsCoprime (α.v ^ 3) α.w := α.coprime_vw.pow_left
  have hdvd : α.v ^ 3 ∣ α.t ^ 2 * α.w := ⟨α.s ^ 2 * α.f₁, α.identity.symm⟩
  exact hvw.dvd_of_dvd_mul_right hdvd

/-- Dually, from the same identity together with `gcd(s, t) = 1` we deduce
`t² ∣ v³·f₁`. -/
theorem t_sq_dvd_v_cube_f₁ : α.t ^ 2 ∣ α.v ^ 3 * α.f₁ := by
  have hst : IsCoprime (α.t ^ 2) (α.s ^ 2) := α.coprime_st.symm.pow
  have h1 : α.t ^ 2 ∣ α.v ^ 3 * α.f₁ * α.s ^ 2 := by
    rw [show α.v ^ 3 * α.f₁ * α.s ^ 2 = α.v ^ 3 * (α.s ^ 2 * α.f₁) from by ring]
    exact ⟨α.w, α.identity⟩
  exact hst.dvd_of_dvd_mul_right h1

/-- Every root of `v` is a root of `t`. -/
theorem isRoot_t_of_isRoot_v {x₀ : F} (hv : Polynomial.IsRoot α.v x₀) :
    Polynomial.IsRoot α.t x₀ := by
  rw [← Polynomial.dvd_iff_isRoot] at hv ⊢
  have hprime : Prime (Polynomial.X - Polynomial.C x₀) :=
    Polynomial.prime_X_sub_C x₀
  have h1 : (Polynomial.X - Polynomial.C x₀) ^ 3 ∣ α.t ^ 2 :=
    dvd_trans (pow_dvd_pow_of_dvd hv 3) α.v_cube_dvd_t_sq
  have h2 : (Polynomial.X - Polynomial.C x₀) ∣ α.t ^ 2 :=
    dvd_trans (dvd_pow_self _ (by norm_num : 3 ≠ 0)) h1
  exact hprime.dvd_of_dvd_pow h2

/-- Every root of `t` is a root of `v` (using that `f₁` is squarefree). -/
theorem isRoot_v_of_isRoot_t {x₀ : F} (ht : Polynomial.IsRoot α.t x₀) :
    Polynomial.IsRoot α.v x₀ := by
  rw [← Polynomial.dvd_iff_isRoot] at ht ⊢
  set p := Polynomial.X - Polynomial.C x₀ with hp_def
  have hprime : Prime p := Polynomial.prime_X_sub_C x₀
  have hpne : p ≠ 0 := Polynomial.X_sub_C_ne_zero x₀

  have h1 : p ^ 2 ∣ α.v ^ 3 * α.f₁ :=
    dvd_trans (pow_dvd_pow_of_dvd ht 2) α.t_sq_dvd_v_cube_f₁

  have h2 : p ∣ α.v ^ 3 * α.f₁ :=
    dvd_trans (dvd_pow_self _ (by norm_num : 2 ≠ 0)) h1

  rcases hprime.dvd_or_dvd h2 with h3 | h3
  ·
    exact hprime.dvd_of_dvd_pow h3
  ·
    obtain ⟨g, hg⟩ := h3

    have h1' : p ^ 2 ∣ α.v ^ 3 * (p * g) := hg ▸ h1
    have h1'' : p ^ 2 ∣ p * (α.v ^ 3 * g) := by rwa [show α.v ^ 3 * (p * g) = p * (α.v ^ 3 * g) from by ring] at h1'

    have h4 : p ∣ α.v ^ 3 * g := by
      rw [pow_succ, pow_one] at h1''
      exact (mul_dvd_mul_iff_left hpne).mp h1''

    rcases hprime.dvd_or_dvd h4 with h5 | h5
    · exact hprime.dvd_of_dvd_pow h5
    · exfalso

      have hsq : p * p ∣ α.f₁ := hg ▸ mul_dvd_mul_left _ h5
      exact Polynomial.not_isUnit_X_sub_C x₀ (α.squarefree_f₁ _ hsq)

/-- `v` and `t` share exactly the same roots. -/
theorem isRoot_v_iff_isRoot_t {x₀ : F} :
    Polynomial.IsRoot α.v x₀ ↔ Polynomial.IsRoot α.t x₀ :=
  ⟨α.isRoot_t_of_isRoot_v, α.isRoot_v_of_isRoot_t⟩

end WithCurveData

end IsogenyStandardForm

namespace ProjectiveCurve

open MvPolynomial

/-- A triple of homogeneous polynomials of common degree `deg` in three variables,
used to represent a candidate rational map between projective plane curves. -/
structure HomogeneousTriple (k : Type u) [CommRing k] where
  ψ_x : MvPolynomial (Fin 3) k
  ψ_y : MvPolynomial (Fin 3) k
  ψ_z : MvPolynomial (Fin 3) k
  deg : ℕ
  hom_x : ψ_x.IsHomogeneous deg
  hom_y : ψ_y.IsHomogeneous deg
  hom_z : ψ_z.IsHomogeneous deg

/-- Convert a `HomogeneousTriple` into the `Fin 3 → MvPolynomial _ k` function
suitable for `MvPolynomial.bind₁`. -/
def HomogeneousTriple.toFun {k : Type u} [CommRing k]
    (t : HomogeneousTriple k) : Fin 3 → MvPolynomial (Fin 3) k :=
  ![t.ψ_x, t.ψ_y, t.ψ_z]

/-- Substitute the components of a homogeneous triple into a polynomial `f`,
i.e. compute `f(ψ_x, ψ_y, ψ_z)`. -/
noncomputable def HomogeneousTriple.substIn {k : Type u} [CommRing k]
    (t : HomogeneousTriple k) (f : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  MvPolynomial.bind₁ t.toFun f

/-- A rational map from the projective curve `f₁ = 0` to `f₂ = 0`, represented by
a homogeneous triple whose components are not all in the ideal `(f₁)`, and which
satisfies `f₂(ψ_x, ψ_y, ψ_z) ∈ (f₁)` (so the image lies on `f₂`). -/
structure RationalMapTriple {k : Type u} [CommRing k]
    (f₁ f₂ : MvPolynomial (Fin 3) k) extends HomogeneousTriple k where
  not_all_in_ideal :
    ψ_x ∉ Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k)) ∨
    ψ_y ∉ Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k)) ∨
    ψ_z ∉ Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))
  image_in_ideal :
    toHomogeneousTriple.substIn f₂ ∈ Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))

/-- Two rational-map triples are equivalent if all pairwise cross-products
`ψ_i^(1) ψ_j^(2) - ψ_j^(1) ψ_i^(2)` lie in the ideal `(f₁)`. -/
def RationalMapTriple.IsEquiv {k : Type u} [CommRing k]
    {f₁ f₂ : MvPolynomial (Fin 3) k}
    (t₁ t₂ : RationalMapTriple f₁ f₂) : Prop :=
  let I := Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))
  t₁.ψ_x * t₂.ψ_y - t₂.ψ_x * t₁.ψ_y ∈ I ∧
  t₁.ψ_x * t₂.ψ_z - t₂.ψ_x * t₁.ψ_z ∈ I ∧
  t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z ∈ I

/-- Reflexivity of triple equivalence: every rational map triple is equivalent to
itself. -/
lemma RationalMapTriple.isEquiv_refl {k : Type u} [CommRing k]
    {f₁ f₂ : MvPolynomial (Fin 3) k}
    (t : RationalMapTriple f₁ f₂) : t.IsEquiv t := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [sub_self]

/-- Symmetry of triple equivalence. -/
lemma RationalMapTriple.isEquiv_symm {k : Type u} [CommRing k]
    {f₁ f₂ : MvPolynomial (Fin 3) k}
    {t₁ t₂ : RationalMapTriple f₁ f₂} (h : t₁.IsEquiv t₂) : t₂.IsEquiv t₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  set I := Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))
  refine ⟨?_, ?_, ?_⟩
  · have : t₂.ψ_x * t₁.ψ_y - t₁.ψ_x * t₂.ψ_y =
      -(t₁.ψ_x * t₂.ψ_y - t₂.ψ_x * t₁.ψ_y) := by ring
    rw [this]; exact I.neg_mem h1
  · have : t₂.ψ_x * t₁.ψ_z - t₁.ψ_x * t₂.ψ_z =
      -(t₁.ψ_x * t₂.ψ_z - t₂.ψ_x * t₁.ψ_z) := by ring
    rw [this]; exact I.neg_mem h2
  · have : t₂.ψ_y * t₁.ψ_z - t₁.ψ_y * t₂.ψ_z =
      -(t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z) := by ring
    rw [this]; exact I.neg_mem h3

/-- Transitivity of triple equivalence, assuming the ideal `(f₁)` is prime so we
can cancel a non-vanishing component of the middle triple. -/
lemma RationalMapTriple.isEquiv_trans_of_prime {k : Type u} [CommRing k]
    {f₁ f₂ : MvPolynomial (Fin 3) k}
    (hprime : (Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))).IsPrime)
    {t₁ t₂ t₃ : RationalMapTriple f₁ f₂}
    (h12 : t₁.IsEquiv t₂) (h23 : t₂.IsEquiv t₃) : t₁.IsEquiv t₃ := by
  obtain ⟨h12_xy, h12_xz, h12_yz⟩ := h12
  obtain ⟨h23_xy, h23_xz, h23_yz⟩ := h23
  set I := Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k)) with hI
  obtain (hx | hy | hz) := t₂.not_all_in_ideal
  · have h13_xy : t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y ∈ I := by
      have key : t₂.ψ_x * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) =
        t₁.ψ_x * (t₂.ψ_x * t₃.ψ_y - t₃.ψ_x * t₂.ψ_y) +
        t₃.ψ_x * (t₁.ψ_x * t₂.ψ_y - t₂.ψ_x * t₁.ψ_y) := by ring
      have mem : t₂.ψ_x * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_left _ h23_xy) (I.mul_mem_left _ h12_xy)
      exact (hprime.mem_or_mem mem).resolve_left hx
    have h13_xz : t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_x * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) =
        t₁.ψ_x * (t₂.ψ_x * t₃.ψ_z - t₃.ψ_x * t₂.ψ_z) +
        t₃.ψ_x * (t₁.ψ_x * t₂.ψ_z - t₂.ψ_x * t₁.ψ_z) := by ring
      have mem : t₂.ψ_x * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_left _ h23_xz) (I.mul_mem_left _ h12_xz)
      exact (hprime.mem_or_mem mem).resolve_left hx
    have h13_yz : t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_x * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) =
        t₁.ψ_y * (t₂.ψ_x * t₃.ψ_z - t₃.ψ_x * t₂.ψ_z) +
        t₃.ψ_y * (t₁.ψ_x * t₂.ψ_z - t₂.ψ_x * t₁.ψ_z) -
        t₂.ψ_z * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) := by ring
      have mem : t₂.ψ_x * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) ∈ I := by
        rw [key]
        exact I.sub_mem (I.add_mem (I.mul_mem_left _ h23_xz) (I.mul_mem_left _ h12_xz))
          (I.mul_mem_left _ h13_xy)
      exact (hprime.mem_or_mem mem).resolve_left hx
    exact ⟨h13_xy, h13_xz, h13_yz⟩
  · have h13_xy : t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y ∈ I := by
      have key : t₂.ψ_y * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) =
        (t₁.ψ_x * t₂.ψ_y - t₂.ψ_x * t₁.ψ_y) * t₃.ψ_y +
        t₁.ψ_y * (t₂.ψ_x * t₃.ψ_y - t₃.ψ_x * t₂.ψ_y) := by ring
      have mem : t₂.ψ_y * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_right _ h12_xy) (I.mul_mem_left _ h23_xy)
      exact (hprime.mem_or_mem mem).resolve_left hy
    have h13_yz : t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_y * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) =
        t₁.ψ_y * (t₂.ψ_y * t₃.ψ_z - t₃.ψ_y * t₂.ψ_z) +
        t₃.ψ_y * (t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z) := by ring
      have mem : t₂.ψ_y * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_left _ h23_yz) (I.mul_mem_left _ h12_yz)
      exact (hprime.mem_or_mem mem).resolve_left hy
    have h13_xz : t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_y * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) =
        t₁.ψ_x * (t₂.ψ_y * t₃.ψ_z - t₃.ψ_y * t₂.ψ_z) +
        t₃.ψ_x * (t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z) +
        t₂.ψ_z * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) := by ring
      have mem : t₂.ψ_y * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) ∈ I := by
        rw [key]
        exact I.add_mem (I.add_mem (I.mul_mem_left _ h23_yz) (I.mul_mem_left _ h12_yz))
          (I.mul_mem_left _ h13_xy)
      exact (hprime.mem_or_mem mem).resolve_left hy
    exact ⟨h13_xy, h13_xz, h13_yz⟩
  · have h13_xz : t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_z * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) =
        (t₁.ψ_x * t₂.ψ_z - t₂.ψ_x * t₁.ψ_z) * t₃.ψ_z +
        t₁.ψ_z * (t₂.ψ_x * t₃.ψ_z - t₃.ψ_x * t₂.ψ_z) := by ring
      have mem : t₂.ψ_z * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_right _ h12_xz) (I.mul_mem_left _ h23_xz)
      exact (hprime.mem_or_mem mem).resolve_left hz
    have h13_yz : t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_z * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) =
        (t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z) * t₃.ψ_z +
        t₁.ψ_z * (t₂.ψ_y * t₃.ψ_z - t₃.ψ_y * t₂.ψ_z) := by ring
      have mem : t₂.ψ_z * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_right _ h12_yz) (I.mul_mem_left _ h23_yz)
      exact (hprime.mem_or_mem mem).resolve_left hz
    have h13_xy : t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y ∈ I := by
      have key : t₂.ψ_z * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) =
        t₁.ψ_x * (t₂.ψ_z * t₃.ψ_y - t₃.ψ_z * t₂.ψ_y) -
        t₃.ψ_x * (t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z) +
        t₂.ψ_y * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) := by ring
      have mem : t₂.ψ_z * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) ∈ I := by
        rw [key]
        have h23_zy : t₂.ψ_z * t₃.ψ_y - t₃.ψ_z * t₂.ψ_y ∈ I := by
          have : t₂.ψ_z * t₃.ψ_y - t₃.ψ_z * t₂.ψ_y =
            -(t₂.ψ_y * t₃.ψ_z - t₃.ψ_y * t₂.ψ_z) := by ring
          rw [this]; exact I.neg_mem h23_yz
        exact I.add_mem (I.sub_mem (I.mul_mem_left _ h23_zy) (I.mul_mem_left _ h12_yz))
          (I.mul_mem_left _ h13_xz)
      exact (hprime.mem_or_mem mem).resolve_left hz
    exact ⟨h13_xy, h13_xz, h13_yz⟩

/-- `RationalMapTriple` modulo equivalence is a `Setoid`, provided `(f₁)` is
prime so that transitivity holds. -/
instance RationalMapTriple.setoid {k : Type u} [CommRing k]
    (f₁ f₂ : MvPolynomial (Fin 3) k)
    [hprime : Fact ((Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))).IsPrime)] :
    Setoid (RationalMapTriple f₁ f₂) where
  r := RationalMapTriple.IsEquiv
  iseqv :=
    ⟨fun t => RationalMapTriple.isEquiv_refl t,
     fun h => RationalMapTriple.isEquiv_symm h,
     fun h1 h2 => RationalMapTriple.isEquiv_trans_of_prime hprime.out h1 h2⟩

/-- Alternative definition of a rational map from `f₁ = 0` to `f₂ = 0`, as a
quotient of the type of `RationalMapTriple`s by the equivalence relation. -/
def RationalMapAlt {k : Type u} [CommRing k]
    (f₁ f₂ : MvPolynomial (Fin 3) k)
    [Fact ((Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))).IsPrime)] : Type u :=
  Quotient (RationalMapTriple.setoid f₁ f₂)

/-- A rational-map triple `t` is *defined at* a point `P` if at least one of its
homogeneous components is nonzero on `P`. -/
def RationalMapTriple.IsDefinedAt {k : Type u} [CommRing k]
    {f₁ f₂ : MvPolynomial (Fin 3) k}
    (t : RationalMapTriple f₁ f₂) (P : Fin 3 → k) : Prop :=
  MvPolynomial.eval P t.ψ_x ≠ 0 ∨
  MvPolynomial.eval P t.ψ_y ≠ 0 ∨
  MvPolynomial.eval P t.ψ_z ≠ 0

end ProjectiveCurve

namespace EllipticCurve

variable {F : Type u} [Field F] [DecidableEq F]
variable (E : WeierstrassCurve.Affine F)

/-- An additive group endomorphism of `E(F)` is *algebraic* if it is either the
zero map or comes from some `Isogeny E E`. -/
def IsAlgebraicEndomorphism (φ : AddMonoid.End E.Point) : Prop :=
  φ = 0 ∨ ∃ (ι : Isogeny E E), ι.toAddMonoidHom = φ

/-- The endomorphism ring `End(E)` of `E`, defined as the subtype of additive
endomorphisms of `E.Point` which are algebraic. -/
def EndomorphismRing : Type u :=
  { φ : AddMonoid.End E.Point // IsAlgebraicEndomorphism E φ }

/-- An additive automorphism of `E.Point` is *algebraic* if it comes from a pair
of mutually-inverse isogenies. -/
def IsAlgebraicAutomorphism (f : AddAut E.Point) : Prop :=
  ∃ (φ : Isogeny E E) (ψ : Isogeny E E),
    (∀ P, ψ (φ P) = P) ∧ (∀ Q, φ (ψ Q) = Q) ∧ f.toAddMonoidHom = φ.toAddMonoidHom

/-- The automorphism group `Aut(E)` of `E`, the subtype of additive automorphisms
of `E.Point` arising from isogenies. -/
def AutomorphismGroup : Type u :=
  { f : AddAut E.Point // IsAlgebraicAutomorphism E f }

/-- Extract the underlying additive endomorphism from an element of
`EndomorphismRing E`. -/
def EndomorphismRing.val (φ : EndomorphismRing E) : AddMonoid.End E.Point := φ.1

variable {E}

/-- Every isogeny `E → E` is an algebraic endomorphism of `E.Point`. -/
def Isogeny.toEndomorphism (φ : Isogeny E E) : EndomorphismRing E :=
  ⟨φ.toAddMonoidHom, Or.inr ⟨φ, rfl⟩⟩

/-- The zero endomorphism in `EndomorphismRing E`. -/
def EndomorphismRing.zero : EndomorphismRing E :=
  ⟨0, Or.inl rfl⟩

/-- The identity endomorphism in `EndomorphismRing E`. -/
def EndomorphismRing.one : EndomorphismRing E :=
  Isogeny.toEndomorphism (Isogeny.id E)

/-- Apply an algebraic endomorphism to a point of `E`. -/
def EndomorphismRing.apply (α : EndomorphismRing E) (P : E.Point) : E.Point :=
  α.1 P



end EllipticCurve

namespace WeierstrassCurve.Affine

/-- A Weierstrass curve is in *short Weierstrass form* if `a₁ = a₂ = a₃ = 0`,
i.e. its equation is `y² = x³ + a₄ x + a₆`. -/
def IsShortWeierstrass {R : Type u} [CommRing R] (W : WeierstrassCurve.Affine R) : Prop :=
  W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0

end WeierstrassCurve.Affine

namespace Isogeny

variable {F : Type u} [Field F] [DecidableEq F]
variable {E₁ E₂ : WeierstrassCurve.Affine F}

open Polynomial

/-- A *representation* of an isogeny `α : E₁ → E₂` in standard form: it records
`(u, v, s, t) ∈ F[X]` and the fact that on a nonsingular point `(x₀, y₀)` with
`v(x₀) ≠ 0`, `α` sends `(x₀, y₀) ↦ (u(x₀)/v(x₀), (s(x₀)/t(x₀))·y₀)`; in the
"pole" case `v(x₀) = 0` and `u(x₀) ≠ 0`, the image is the identity. -/
structure IsogenyRepresentation (E₁ E₂ : WeierstrassCurve.Affine F)
    (α : Isogeny E₁ E₂) extends IsogenyStandardForm F where
  represents : ∀ (x₀ y₀ : F) (h₁ : E₁.Nonsingular x₀ y₀)
    (_hv : eval x₀ v ≠ 0),
    ∃ (h₂ : E₂.Nonsingular (eval x₀ u / eval x₀ v)
                             (eval x₀ s / eval x₀ t * y₀)),
    α.toAddMonoidHom (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) =
      WeierstrassCurve.Affine.Point.some
        (eval x₀ u / eval x₀ v)
        (eval x₀ s / eval x₀ t * y₀) h₂
  maps_poles_to_zero : ∀ (x₀ y₀ : F) (h₁ : E₁.Nonsingular x₀ y₀)
    (_hv : eval x₀ v = 0) (_hu : eval x₀ u ≠ 0),
    α.toAddMonoidHom (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) = 0


/-- If the denominator polynomial `v` of the standard form does not vanish at
`x₀`, then the point `(x₀, y₀)` is not in the kernel of `α`. -/
theorem not_in_kernel_of_v_ne_zero
    (_hE₁ : E₁.IsShortWeierstrass) (_hE₂ : E₂.IsShortWeierstrass)
    (α : Isogeny E₁ E₂) (rep : IsogenyRepresentation E₁ E₂ α)
    (x₀ y₀ : F) (h₁ : E₁.Nonsingular x₀ y₀)
    (hv : eval x₀ rep.v ≠ 0) :
    α (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) ≠ 0 := by
  obtain ⟨h₂, hrep⟩ := rep.represents x₀ y₀ h₁ hv
  show α.toAddMonoidHom (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) ≠ 0
  rw [hrep]
  exact WeierstrassCurve.Affine.Point.some_ne_zero h₂

/-- Conversely, if `v(x₀) = 0` then `u(x₀) ≠ 0` (using `IsCoprime u v`), so the
"pole" case of the representation forces `(x₀, y₀)` to be in the kernel. -/
theorem in_kernel_of_v_eq_zero
    {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (_hE₁ : E₁.IsShortWeierstrass) (_hE₂ : E₂.IsShortWeierstrass)
    (α : Isogeny E₁ E₂) (rep : IsogenyRepresentation E₁ E₂ α)
    (x₀ y₀ : F) (h₁ : E₁.Nonsingular x₀ y₀)
    (hv : eval x₀ rep.v = 0) :
    α (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) = 0 := by

  have hu : eval x₀ rep.u ≠ 0 := by
    intro hu_eq
    have hdvd_u : (Polynomial.X - Polynomial.C x₀) ∣ rep.u :=
      Polynomial.dvd_iff_isRoot.mpr hu_eq
    have hdvd_v : (Polynomial.X - Polynomial.C x₀) ∣ rep.v :=
      Polynomial.dvd_iff_isRoot.mpr hv
    exact (Polynomial.irreducible_X_sub_C x₀).not_isUnit
      (rep.coprime_uv.isUnit_of_dvd' hdvd_u hdvd_v)
  exact rep.maps_poles_to_zero x₀ y₀ h₁ hv hu

/-- Combining the previous two: `(x₀, y₀)` lies in the kernel of `α` iff
`v(x₀) = 0`. This characterizes affine points of the kernel via the standard
form. -/
theorem kernel_iff_v_eq_zero
    (hE₁ : E₁.IsShortWeierstrass) (hE₂ : E₂.IsShortWeierstrass)
    (α : Isogeny E₁ E₂) (rep : IsogenyRepresentation E₁ E₂ α)
    (x₀ y₀ : F) (h₁ : E₁.Nonsingular x₀ y₀) :
    α (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) = 0 ↔ eval x₀ rep.v = 0 := by
  constructor
  ·
    intro hker
    by_contra hv
    exact not_in_kernel_of_v_ne_zero hE₁ hE₂ α rep x₀ y₀ h₁ hv hker
  ·
    exact in_kernel_of_v_eq_zero hE₁ hE₂ α rep x₀ y₀ h₁

omit [DecidableEq F] in
/-- For a fixed `x₀ ∈ F`, only finitely many `y₀` make `(x₀, y₀)` a nonsingular
point of `E₁`, because such `y₀` are roots of the (nonzero) specialization of the
Weierstrass polynomial at `x₀`. -/
lemma finite_nonsingular_fibers (x₀ : F) :
    Set.Finite {y : F | E₁.Nonsingular x₀ y} := by
  have hmonic : (Polynomial.map (evalRingHom x₀) E₁.polynomial).Monic :=
    WeierstrassCurve.Affine.monic_polynomial.map _
  have hne : Polynomial.map (evalRingHom x₀) E₁.polynomial ≠ 0 := hmonic.ne_zero
  have hsub : {y : F | E₁.Nonsingular x₀ y} ⊆
      {y : F | (Polynomial.map (evalRingHom x₀) E₁.polynomial).IsRoot y} := by
    intro y hy
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot] at hy ⊢
    rw [Polynomial.map_evalRingHom_eval]
    exact hy.1
  exact (Polynomial.finite_setOf_isRoot hne).subset hsub

/-- Extract the affine coordinates `(x, y)` of a point of `E₁`, mapping the
identity to `none`. -/
noncomputable def pointToCoords : E₁.Point → Option (F × F)
  | .zero => none
  | .some x y _ => some (x, y)

omit [DecidableEq F] in
/-- The coordinate-extraction function is injective. -/
lemma pointToCoords_injective : Function.Injective (pointToCoords (E₁ := E₁)) := by
  intro P Q h
  cases P with
  | zero => cases Q with
    | zero => rfl
    | some x y hxy => simp [pointToCoords] at h
  | some x y hxy => cases Q with
    | zero => simp [pointToCoords] at h
    | some x' y' hxy' =>
      simp [pointToCoords] at h
      obtain ⟨hx, hy⟩ := h
      subst hx; subst hy; rfl

/-- Given a standard-form representation of `α`, the kernel of `α` is finite:
its image under `pointToCoords` is contained in `{none} ∪ {(x₀,y₀) : v(x₀) = 0
∧ E₁.Nonsingular x₀ y₀}`, which is finite by the previous lemmas. -/
theorem isogeny_kernel_finite_of_rep
    (hE₁ : E₁.IsShortWeierstrass) (hE₂ : E₂.IsShortWeierstrass)
    (α : Isogeny E₁ E₂) (rep : IsogenyRepresentation E₁ E₂ α) :
    Set.Finite {P : E₁.Point | α P = 0} := by

  apply Set.Finite.of_finite_image (f := pointToCoords)
  ·
    apply Set.Finite.subset (s := {none} ∪
      Option.some '' (⋃ x₀ ∈ {x | rep.v.IsRoot x}, {x₀} ×ˢ {y | E₁.Nonsingular x₀ y}))
    ·
      apply Set.Finite.union
      · exact Set.finite_singleton none
      · apply Set.Finite.image
        exact (Polynomial.finite_setOf_isRoot rep.v_ne_zero).biUnion
          (fun x₀ _ => Set.Finite.prod (Set.finite_singleton x₀)
            (finite_nonsingular_fibers x₀))
    ·
      intro z hz
      obtain ⟨P, hP, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hP
      cases P with
      | zero => exact Set.mem_union_left _ (Set.mem_singleton _)
      | some x₀ y₀ h₁ =>
        apply Set.mem_union_right
        refine ⟨(x₀, y₀), ?_, rfl⟩
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_prod, Set.mem_singleton_iff]
        exact ⟨x₀, (kernel_iff_v_eq_zero hE₁ hE₂ α rep x₀ y₀ h₁).mp hP, rfl, h₁⟩
  ·
    exact pointToCoords_injective.injOn



end Isogeny
