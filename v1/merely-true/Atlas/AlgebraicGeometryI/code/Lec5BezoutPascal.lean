/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum

open MvPolynomial Classical

noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- The projective plane `P^2` over `k`, identified with the projectivization of `k^3`. -/
abbrev P2 := Projectivization k (Fin 3 → k)

/-- A point `p ∈ P^2` lies on the curve defined by a polynomial `f` if `f` vanishes on a (any)
representative of `p`. -/
def P2.liesOn (p : P2 k) (f : MvPolynomial (Fin 3) k) : Prop :=
  MvPolynomial.eval (Projectivization.rep p) f = 0

/-- Translate of a polynomial `g` by a point `p`: the polynomial obtained by substituting
`x_i ↦ x_i + p_i`. -/
def translatePoly {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k) :
    MvPolynomial (Fin n) k :=
  MvPolynomial.aeval (fun i => X i + C (p i)) g

/-- Translation of polynomials by a fixed point is an injective operation, since translating by
`-p` is a left inverse. -/
lemma translatePoly_injective {n : ℕ} (p : Fin n → k) :
    Function.Injective (fun g => translatePoly k g p) := by
  suffices h : ∀ g : MvPolynomial (Fin n) k,
      translatePoly k (translatePoly k g p) (fun i => -p i) = g by
    exact Function.HasLeftInverse.injective
      ⟨fun g => translatePoly k g (fun i => -p i), h⟩
  intro g
  simp only [translatePoly]
  conv_rhs => rw [← AlgHom.id_apply (R := k) g]
  rw [← AlgHom.comp_apply]
  congr 1; ext i; simp [map_add, map_neg]

/-- Translating a nonzero polynomial yields a nonzero polynomial. -/
lemma translatePoly_ne_zero {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k)
    (hg : g ≠ 0) : translatePoly k g p ≠ 0 := by
  intro heq; apply hg
  have hinj := translatePoly_injective k p
  have h0 : translatePoly k (0 : MvPolynomial (Fin n) k) p = 0 := by
    simp [translatePoly, map_zero]
  have : (fun g => translatePoly k g p) g = (fun g => translatePoly k g p) 0 := by
    simp only; rw [heq, h0]
  exact hinj this

/-- A nonzero polynomial has a nonzero homogeneous component of some degree. -/
lemma exists_homogeneousComponent_ne_zero {n : ℕ}
    (φ : MvPolynomial (Fin n) k) (h : φ ≠ 0) :
    ∃ m : ℕ, MvPolynomial.homogeneousComponent m φ ≠ 0 := by
  by_contra hall; push Not at hall; apply h
  have := MvPolynomial.sum_homogeneousComponent φ
  simp only [hall, Finset.sum_const_zero] at this; exact this.symm

/-- Multiplicity of a hypersurface `V(g)` at a point `p`: the smallest degree at which the
translate `g(x + p)` has a nonzero homogeneous component. -/
def hypersurfaceMultiplicity {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k)
    (hg : g ≠ 0) : ℕ :=
  Nat.find (exists_homogeneousComponent_ne_zero k (translatePoly k g p)
    (translatePoly_ne_zero k g p hg))

/-- At the multiplicity, the corresponding homogeneous component of `g(x + p)` is nonzero. -/
lemma hypersurfaceMultiplicity_spec {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k)
    (hg : g ≠ 0) :
    MvPolynomial.homogeneousComponent (hypersurfaceMultiplicity k g p hg)
      (translatePoly k g p) ≠ 0 :=
  Nat.find_spec (exists_homogeneousComponent_ne_zero k (translatePoly k g p)
    (translatePoly_ne_zero k g p hg))

/-- Below the multiplicity, every homogeneous component of the translated polynomial vanishes. -/
lemma hypersurfaceMultiplicity_min {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k)
    (hg : g ≠ 0) (m : ℕ) (hm : m < hypersurfaceMultiplicity k g p hg) :
    MvPolynomial.homogeneousComponent m (translatePoly k g p) = 0 := by
  by_contra h
  exact Nat.lt_irrefl _ (lt_of_lt_of_le hm (Nat.find_min' _ h))

/-- The coordinate ring of the intersection scheme of two affine plane curves `V(f)` and `V(g)`:
the quotient `k[x, y] / (f, g)`. -/
abbrev CurveQuotient (f g : MvPolynomial (Fin 2) k) :=
  MvPolynomial (Fin 2) k ⧸ (Ideal.span {f, g})

/-- Multiplication-by-`x_i` operator on the curve quotient `k[x, y]/(f, g)`, viewed as a
`k`-linear endomorphism. -/
def mulByVarOperator (f g : MvPolynomial (Fin 2) k) (i : Fin 2) :
    Module.End k (CurveQuotient k f g) :=
  Algebra.lmul k _ (Ideal.Quotient.mk _ (X i))

/-- Intersection multiplicity of two affine plane curves at a point `p`: the dimension of the
joint generalized eigenspace of the multiplication-by-coordinate operators at the eigenvalue `p`. -/
def intersectionMultiplicity (f g : MvPolynomial (Fin 2) k) (p : Fin 2 → k)
    [Module.Finite k (CurveQuotient k f g)] : ℕ :=
  Module.finrank k ↥(
    (mulByVarOperator k f g 0).genEigenspace (p 0) ⊤ ⊓
    (mulByVarOperator k f g 1).genEigenspace (p 1) ⊤
      : Submodule k (CurveQuotient k f g))

/-- A plane projective curve in `P^2`: a nonzero homogeneous polynomial in three variables of a
given degree. -/
structure PlaneCurve where
  poly : MvPolynomial (Fin 3) k
  poly_ne_zero : poly ≠ 0
  deg : ℕ
  poly_homogeneous : poly.IsHomogeneous deg

/-- The vanishing locus of a plane curve `C` as a subset of `P^2`. -/
def PlaneCurve.vanishingLocus (C : PlaneCurve k) : Set (P2 k) :=
  {p | P2.liesOn k p C.poly}

/-- Two plane curves have no common irreducible component iff their defining polynomials are
coprime. -/
def PlaneCurve.noCommonComponent (C₁ C₂ : PlaneCurve k) : Prop :=
  IsCoprime C₁.poly C₂.poly

/-- The set of intersection points of two plane curves: the intersection of their vanishing loci
in `P^2`. -/
def PlaneCurve.intersectionPoints (C₁ C₂ : PlaneCurve k) : Set (P2 k) :=
  C₁.vanishingLocus k ∩ C₂.vanishingLocus k





/-- Three points in `P^2` are *collinear* if some nonzero linear form vanishes at all of them. -/
def P2Collinear (p q r : P2 k) : Prop :=
  ∃ (L : MvPolynomial (Fin 3) k),
    L ≠ 0 ∧ L.IsHomogeneous 1 ∧
    P2.liesOn k p L ∧ P2.liesOn k q L ∧ P2.liesOn k r L

/-- A plane curve is a *conic* if its degree is `2`. -/
def IsConic (C : PlaneCurve k) : Prop := C.deg = 2

/-- Defining linear form of the line through two points of `P^2`, given by the cross product of
their representatives. -/
def lineThroughPoints (p q : P2 k) : MvPolynomial (Fin 3) k :=
  let pv := Projectivization.rep p
  let qv := Projectivization.rep q
  C (pv 1 * qv 2 - pv 2 * qv 1) * X 0 +
  C (pv 2 * qv 0 - pv 0 * qv 2) * X 1 +
  C (pv 0 * qv 1 - pv 1 * qv 0) * X 2

/-- Data of a hexagon inscribed in a conic: the conic, six distinct vertices on it, indexed
cyclically by `Fin 6`. -/
structure PascalInscribedHexagon where
  conic : PlaneCurve k
  is_conic : IsConic k conic
  vertex : Fin 6 → P2 k
  vertices_on_conic : ∀ i, P2.liesOn k (vertex i) conic.poly
  vertices_distinct : Function.Injective vertex

/-- Cyclic successor on `Fin 6`, used to index the sides of an inscribed hexagon. -/
def hexNext (i : Fin 6) : Fin 6 := ⟨(i.val + 1) % 6, Nat.mod_lt _ (by omega)⟩

/-- Opposite vertex map on `Fin 6` (shift by 3), used to pair opposite sides of an inscribed
hexagon. -/
def hexOpposite (i : Fin 6) : Fin 6 := ⟨(i.val + 3) % 6, Nat.mod_lt _ (by omega)⟩

/-- The `i`-th side of an inscribed hexagon: the line through the `i`-th and `(i + 1)`-th
vertices. -/
def PascalInscribedHexagon.side (H : PascalInscribedHexagon k) (i : Fin 6) :
    MvPolynomial (Fin 3) k :=
  lineThroughPoints k (H.vertex i) (H.vertex (hexNext i))





end Lec5BezoutPascal
