/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Frobenius

open Polynomial

universe u

namespace FrobeniusEndomorphism

variable {F : Type u} [Field F]

/-- A ring homomorphism $\varphi : F \to F$ *fixes the coefficients* of a Weierstrass
curve $W$ if it acts as the identity on the five defining coefficients $a_1, a_2, a_3,
a_4, a_6$. This is the condition needed for $\varphi$ to descend to a map of curves. -/
structure FixesCoeffs (W : WeierstrassCurve.Affine F) (φ : F →+* F) : Prop where
  fix_a₁ : φ W.a₁ = W.a₁
  fix_a₂ : φ W.a₂ = W.a₂
  fix_a₃ : φ W.a₃ = W.a₃
  fix_a₄ : φ W.a₄ = W.a₄
  fix_a₆ : φ W.a₆ = W.a₆

variable {W : WeierstrassCurve.Affine F} {φ : F →+* F}

/-- A coefficient-fixing ring homomorphism commutes with two-variable evaluation of the
defining polynomial of $W$: $f_W(\varphi x, \varphi y) = \varphi(f_W(x, y))$. -/
lemma evalEval_polynomial_map (hφ : FixesCoeffs W φ) (x y : F) :
    Polynomial.evalEval (φ x) (φ y) W.polynomial =
    φ (Polynomial.evalEval x y W.polynomial) := by
  simp only [WeierstrassCurve.Affine.polynomial, Polynomial.evalEval,
    map_sub, map_add, map_mul, map_pow, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    hφ.fix_a₁, hφ.fix_a₂, hφ.fix_a₃, hφ.fix_a₄, hφ.fix_a₆]

/-- A coefficient-fixing endomorphism sends solutions of the Weierstrass equation to
solutions: if $W(x, y) = 0$ then $W(\varphi x, \varphi y) = 0$. -/
lemma equation_preserved (hφ : FixesCoeffs W φ) {x y : F}
    (h : W.Equation x y) : W.Equation (φ x) (φ y) := by
  show Polynomial.evalEval (φ x) (φ y) W.polynomial = 0
  rw [evalEval_polynomial_map hφ, h, map_zero]

/-- A coefficient-fixing endomorphism commutes with two-variable evaluation of the
$x$-partial derivative $\partial_x W$ of the defining polynomial. -/
lemma evalEval_polynomialX_map (hφ : FixesCoeffs W φ) (x y : F) :
    Polynomial.evalEval (φ x) (φ y) W.polynomialX =
    φ (Polynomial.evalEval x y W.polynomialX) := by
  simp only [WeierstrassCurve.Affine.polynomialX, Polynomial.evalEval,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_ofNat, map_sub, map_add, map_mul, map_pow,
    hφ.fix_a₁, hφ.fix_a₂, hφ.fix_a₄, map_ofNat]

/-- A coefficient-fixing endomorphism commutes with two-variable evaluation of the
$y$-partial derivative $\partial_y W$ of the defining polynomial. -/
lemma evalEval_polynomialY_map (hφ : FixesCoeffs W φ) (x y : F) :
    Polynomial.evalEval (φ x) (φ y) W.polynomialY =
    φ (Polynomial.evalEval x y W.polynomialY) := by
  simp only [WeierstrassCurve.Affine.polynomialY, Polynomial.evalEval,
    Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_ofNat, map_add, map_mul,
    hφ.fix_a₁, hφ.fix_a₃, map_ofNat]

/-- An injective coefficient-fixing endomorphism preserves nonsingularity: if
$(x, y)$ is a nonsingular point on $W$, so is $(\varphi x, \varphi y)$. -/
lemma nonsingular_preserved (hφ : FixesCoeffs W φ) (hφ_inj : Function.Injective φ)
    {x y : F} (h : W.Nonsingular x y) :
    W.Nonsingular (φ x) (φ y) := by
  obtain ⟨heq, hor⟩ := h
  refine ⟨equation_preserved hφ heq, ?_⟩
  cases hor with
  | inl hX =>
    left
    rw [evalEval_polynomialX_map hφ]
    exact fun h => hX (hφ_inj (by rw [h, map_zero]))
  | inr hY =>
    right
    rw [evalEval_polynomialY_map hφ]
    exact fun h => hY (hφ_inj (by rw [h, map_zero]))

variable [DecidableEq F]

/-- The induced self-map on the affine points $W(\overline{F})$ of a Weierstrass curve
given by an injective coefficient-fixing endomorphism: it fixes the point at infinity
and applies $\varphi$ coordinatewise to affine points. -/
noncomputable def pointMap (hφ : FixesCoeffs W φ)
    (hφ_inj : Function.Injective φ) : W.Point → W.Point
  | .zero => .zero
  | .some x y h => .some (φ x) (φ y) (nonsingular_preserved hφ hφ_inj h)

omit [DecidableEq F] in
/-- The induced map sends the point at infinity to itself. -/
@[simp]
lemma pointMap_zero (hφ : FixesCoeffs W φ) (hφ_inj : Function.Injective φ) :
    pointMap hφ hφ_inj .zero = .zero := rfl

omit [DecidableEq F] in
/-- The induced map sends an affine point $(x, y)$ to $(\varphi x, \varphi y)$. -/
@[simp]
lemma pointMap_some (hφ : FixesCoeffs W φ) (hφ_inj : Function.Injective φ)
    {x y : F} (h : W.Nonsingular x y) :
    pointMap hφ hφ_inj (.some x y h) =
      .some (φ x) (φ y) (nonsingular_preserved hφ hφ_inj h) := rfl

section FiniteField

variable {p n : ℕ} [Fintype F] [Fact (Nat.Prime p)] [CharP F p]
variable {L : Type u} [Field L] [DecidableEq L] [Algebra F L] [CharP L p]

omit [DecidableEq F] [CharP F p] [DecidableEq L] in
/-- The $n$-th iterate of Frobenius on an $F$-algebra $L$ fixes the image of any element
of $F = \mathbb{F}_{p^n}$, because by Fermat's little theorem $a^{p^n} = a$ for $a \in F$. -/
lemma iterateFrobenius_algebraMap (hcard : Fintype.card F = p ^ n) (a : F) :
    iterateFrobenius L p n (algebraMap F L a) = algebraMap F L a := by
  change (algebraMap F L a) ^ (p ^ n) = algebraMap F L a
  rw [← map_pow]
  congr 1
  rw [← hcard]
  exact FiniteField.pow_card a

/-- The base change of a Weierstrass curve $W/F$ along an algebra inclusion $F \hookrightarrow L$:
the same equation viewed over the larger field $L$. -/
noncomputable abbrev baseChange (W : WeierstrassCurve.Affine F) :
    WeierstrassCurve.Affine L :=
  W.map (algebraMap F L)

omit [DecidableEq F] [CharP F p] [DecidableEq L] in
/-- The $n$-th Frobenius iterate $x \mapsto x^{p^n}$ on $L$ fixes the coefficients of the
base change to $L$ of any curve defined over $\mathbb{F}_{p^n}$, since those coefficients
lie in the prime-field-fixed subfield. -/
lemma fixesCoeffs_iterateFrobenius (hcard : Fintype.card F = p ^ n)
    (W : WeierstrassCurve.Affine F) :
    FixesCoeffs (baseChange W (L := L)) (iterateFrobenius L p n) where
  fix_a₁ := iterateFrobenius_algebraMap hcard W.a₁
  fix_a₂ := iterateFrobenius_algebraMap hcard W.a₂
  fix_a₃ := iterateFrobenius_algebraMap hcard W.a₃
  fix_a₄ := iterateFrobenius_algebraMap hcard W.a₄
  fix_a₆ := iterateFrobenius_algebraMap hcard W.a₆

/-- The Frobenius endomorphism on points of $W_L$ for $W/\mathbb{F}_{p^n}$
(Definition 4.24): the self-map of points sending $(x, y) \mapsto (x^{p^n}, y^{p^n})$.
This is the geometric Frobenius whose fixed points are the $\mathbb{F}_{p^n}$-rational points. -/
noncomputable def frobeniusPointMap (hcard : Fintype.card F = p ^ n)
    (W : WeierstrassCurve.Affine F) :
    (baseChange W (L := L)).Point → (baseChange W (L := L)).Point :=
  pointMap (fixesCoeffs_iterateFrobenius hcard W) (iterateFrobenius L p n).injective

omit [DecidableEq F] [CharP F p] [DecidableEq L] in
/-- Frobenius fixes the point at infinity. -/
@[simp]
lemma frobeniusPointMap_zero (hcard : Fintype.card F = p ^ n)
    (W : WeierstrassCurve.Affine F) :
    frobeniusPointMap (L := L) hcard W .zero = .zero := rfl

omit [DecidableEq F] [CharP F p] [DecidableEq L] in
/-- Frobenius sends an affine point $(x, y)$ on the base change of $W$ to
$(x^{p^n}, y^{p^n})$. -/
@[simp]
lemma frobeniusPointMap_some (hcard : Fintype.card F = p ^ n)
    (W : WeierstrassCurve.Affine F)
    {x y : L} (h : (baseChange W (L := L)).Nonsingular x y) :
    frobeniusPointMap hcard W (.some x y h) =
      .some (x ^ (p ^ n)) (y ^ (p ^ n))
        (nonsingular_preserved (fixesCoeffs_iterateFrobenius hcard W)
          (iterateFrobenius L p n).injective h) := by
  simp [frobeniusPointMap, pointMap, iterateFrobenius]

end FiniteField

end FrobeniusEndomorphism
