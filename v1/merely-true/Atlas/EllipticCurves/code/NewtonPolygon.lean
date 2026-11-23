/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Set.Card

noncomputable section

open scoped Classical

namespace NewtonPolygon

variable {k : Type*} [CommSemiring k]

/-- Coerces a finitely-supported exponent vector `m : Fin 2 →₀ ℕ` into a real-valued
function `Fin 2 → ℝ`, used to place exponents in `ℝ²` for the Newton polygon. -/
def exponentToReal (m : Fin 2 →₀ ℕ) : Fin 2 → ℝ :=
  fun i => (m i : ℝ)

/-- The Newton support of a bivariate polynomial `f`: the image of its monomial
exponents in `ℝ²` (cf. Definition 1.1 of "Elliptic Curves"). -/
def newtonSupport (f : MvPolynomial (Fin 2) k) : Set (Fin 2 → ℝ) :=
  exponentToReal '' (f.support : Set (Fin 2 →₀ ℕ))

/-- The Newton polygon `Δ(f)` of a bivariate polynomial `f`: the convex hull in `ℝ²`
of the exponents `(i, j)` with `aᵢⱼ ≠ 0` (Definition 1.1). -/
def newtonPolygon (f : MvPolynomial (Fin 2) k) : Set (Fin 2 → ℝ) :=
  (convexHull ℝ) (newtonSupport f)

/-- The topological interior `Δ°(f)` of the Newton polygon of `f` (Definition 1.1). -/
def newtonPolygonInterior (f : MvPolynomial (Fin 2) k) : Set (Fin 2 → ℝ) :=
  interior (newtonPolygon f)

/-- The topological boundary `∂Δ(f)` of the Newton polygon of `f` (Definition 1.1). -/
def newtonPolygonBoundary (f : MvPolynomial (Fin 2) k) : Set (Fin 2 → ℝ) :=
  frontier (newtonPolygon f)

/-- The edge restriction `f_γ` of a polynomial `f` to a subset `γ ⊆ ℝ²`: the sum of
the monomials of `f` whose exponents lie on `γ` (Definition 1.1). -/
def edgeRestriction (f : MvPolynomial (Fin 2) k)
    (γ : Set (Fin 2 → ℝ)) : MvPolynomial (Fin 2) k :=
  f.support.sum fun m =>
    if exponentToReal m ∈ γ then MvPolynomial.monomial m (MvPolynomial.coeff m f) else 0

/-- The integer lattice `ℤ² ⊆ ℝ²` viewed as a subset of `Fin 2 → ℝ`. -/
def integerLattice : Set (Fin 2 → ℝ) :=
  {p | ∀ i, ∃ n : ℤ, p i = ↑n}

/-- The set of integer lattice points lying strictly inside the Newton polygon of `f`,
i.e. `Δ°(f) ∩ ℤ²`, appearing on the right-hand side of Baker's theorem. -/
def interiorLatticePoints (f : MvPolynomial (Fin 2) k) : Set (Fin 2 → ℝ) :=
  newtonPolygonInterior f ∩ integerLattice

/-- The standard inner product on `Fin 2 → ℝ`, used to define supporting hyperplanes
for edges of the Newton polygon. -/
def innerProduct2 (n p : Fin 2 → ℝ) : ℝ := dotProduct n p

/-- The collection of boundary edges of the Newton polygon of `f`: faces cut out by a
supporting hyperplane with nonzero normal vector that contain at least two points. -/
def boundaryEdges (f : MvPolynomial (Fin 2) k) : Set (Set (Fin 2 → ℝ)) :=
  { γ | ∃ (n : Fin 2 → ℝ) (c : ℝ),
      n ≠ 0 ∧
      (∀ p ∈ newtonPolygon f, innerProduct2 n p ≤ c) ∧
      γ = { p ∈ newtonPolygon f | innerProduct2 n p = c } ∧
      ∃ p q, p ∈ γ ∧ q ∈ γ ∧ p ≠ q }

end NewtonPolygon

namespace NewtonPolygon

variable {k : Type*} [Field k]

/-- The edge restriction `f_γ` viewed over the algebraic closure of `k`, used to test
nondegeneracy in the algebraically closed setting. -/
def edgeRestrictionAlgClosure (f : MvPolynomial (Fin 2) k)
    (γ : Set (Fin 2 → ℝ)) : MvPolynomial (Fin 2) (AlgebraicClosure k) :=
  MvPolynomial.map (algebraMap k (AlgebraicClosure k)) (edgeRestriction f γ)

/-- A polynomial `f` is nondegenerate with respect to an edge `γ` if the polynomials
`f_γ`, `x · ∂f_γ/∂x`, and `y · ∂f_γ/∂y` have no common zero in `(k̄ˣ)²`
(Definition 1.3). -/
def IsNondegenerateWrtEdge (f : MvPolynomial (Fin 2) k) (γ : Set (Fin 2 → ℝ)) : Prop :=
  ∀ (p : Fin 2 → AlgebraicClosure k),
    p 0 ≠ 0 → p 1 ≠ 0 →
      ¬(MvPolynomial.eval p (edgeRestrictionAlgClosure f γ) = 0 ∧
        MvPolynomial.eval p
          (MvPolynomial.X 0 * MvPolynomial.pderiv 0 (edgeRestrictionAlgClosure f γ)) = 0 ∧
        MvPolynomial.eval p
          (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (edgeRestrictionAlgClosure f γ)) = 0)

/-- `f` is nondegenerate with respect to `Δ(f)` if it is nondegenerate with respect to
every boundary edge and is not divisible by `x` or `y` (Definition 1.3). -/
def IsNondegenerate (f : MvPolynomial (Fin 2) k) : Prop :=
  (∀ γ ∈ boundaryEdges f, IsNondegenerateWrtEdge f γ) ∧
  ¬(MvPolynomial.X (0 : Fin 2) ∣ f) ∧
  ¬(MvPolynomial.X (1 : Fin 2) ∣ f)

/-- Lift an exponent `m ∈ ℕ²` to a homogenizing exponent in `ℕ³`, padding the third
component with `d − (m₀ + m₁)` so the resulting monomial has total degree `d`. -/
def liftExponent (m : Fin 2 →₀ ℕ) (d : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i =>
    match i with
    | 0 => m 0
    | 1 => m 1
    | 2 => d - (m 0 + m 1))

/-- Homogenize a bivariate polynomial `f` to a trivariate polynomial `f*` of the same
total degree by inserting an auxiliary variable in the third coordinate. -/
def homogenize (f : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 3) k :=
  let d := f.totalDegree
  f.support.sum fun m =>
    MvPolynomial.monomial (liftExponent m d) (MvPolynomial.coeff m f)

/-- A point `p ∈ k̄³` is a singular point of a homogeneous polynomial `F` if it lies on
the variety `{F = 0}` and all partial derivatives of `F` vanish at `p`. -/
def IsSingularPoint (F : MvPolynomial (Fin 3) (AlgebraicClosure k))
    (p : Fin 3 → AlgebraicClosure k) : Prop :=
  MvPolynomial.eval p F = 0 ∧
  ∀ i : Fin 3, MvPolynomial.eval p ((MvPolynomial.pderiv i) F) = 0

/-- A point `p ∈ k̄³` is a "coordinate point" if all but one of its coordinates vanish,
i.e. it is one of the three points `(1:0:0)`, `(0:1:0)`, `(0:0:1)`. -/
def IsCoordinatePoint (p : Fin 3 → AlgebraicClosure k) : Prop :=
  ∃ i : Fin 3, ∀ j : Fin 3, j ≠ i → p j = 0

/-- A homogenized polynomial `f*` has no singularities outside the three coordinate
points; this is the smoothness condition appearing in Proposition 1.5. -/
def HasNoSingularitiesOutsideCoordinatePoints
    (fStar : MvPolynomial (Fin 3) (AlgebraicClosure k)) : Prop :=
  ∀ p : Fin 3 → AlgebraicClosure k,
    (∃ i, p i ≠ 0) →
    IsSingularPoint fStar p →
    IsCoordinatePoint (k := k) p

end NewtonPolygon

/-- A bundle of data witnessing the existence of a "genus" function on bivariate
polynomials over `k`, packaging invariance under nonzero scaling, the arithmetic
genus upper bound, and the equality case for smooth curves. -/
class FunctionField.GenusData (k : Type*) [Field k] where
  genusVal : MvPolynomial (Fin 2) k → ℕ
  genus_invariant_val : ∀ (f : MvPolynomial (Fin 2) k) (c : k), c ≠ 0 →
    genusVal (MvPolynomial.C c * f) = genusVal f
  genus_le_arithmetic_genus_val : ∀ (f : MvPolynomial (Fin 2) k),
    Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f) →
    genusVal f ≤ (f.totalDegree - 1) * (f.totalDegree - 2) / 2
  genus_eq_arithmetic_genus_of_smooth_val : ∀ (f : MvPolynomial (Fin 2) k),
    Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f) →
    (∀ p : Fin 3 → AlgebraicClosure k,
      (∃ i, p i ≠ 0) →
      ¬NewtonPolygon.IsSingularPoint
        (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) (NewtonPolygon.homogenize f)) p) →
    genusVal f = (f.totalDegree - 1) * (f.totalDegree - 2) / 2





namespace NewtonPolygon


end NewtonPolygon

end
