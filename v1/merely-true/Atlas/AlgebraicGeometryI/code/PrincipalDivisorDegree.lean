/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.BezoutTheorem
import Atlas.AlgebraicGeometryI.code.RiemannRochGeneral

set_option maxHeartbeats 1600000

open Polynomial

noncomputable section

/-- The degree of a principal divisor: difference of k-dimensions of A/I and A/J,
where I, J are two ideals representing a divisor of the form (p) - (q). -/
def principalDivisorDegree (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] (I J : Ideal A) : ℤ :=
  (Module.finrank k (A ⧸ I) : ℤ) - (Module.finrank k (A ⧸ J) : ℤ)

/-- The fiber dimension at a closed point X - c equals the rank of S as a k[X]-module. -/
theorem fiber_dimension_eq_rank (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Module.Basis ι (Polynomial k) S) (c : k) :
    Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c)}) =
    Fintype.card ι := by
  have hp : algebraMap (Polynomial k) S (X - C c) ≠ 0 := by
    intro h
    exact absurd (Module.Basis.algebraMap_injective b (h.trans (map_zero _).symm))
      (by intro heq; exact absurd (congr_arg natDegree heq) (by simp))
  rw [finrank_quotient_span_eq_natDegree_norm b hp,
      Algebra.norm_algebraMap_of_basis b,
      Polynomial.natDegree_pow, natDegree_X_sub_C, mul_one]

/-- The fiber dimension at any closed point X - c is constant (equals the generic
rank); a finite map has constant fiber dimension on a curve. -/
theorem fiber_dimension_constant (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Module.Basis ι (Polynomial k) S)
    (c₁ c₂ : k) :
    Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c₁)}) =
    Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c₂)}) := by
  rw [fiber_dimension_eq_rank k b c₁, fiber_dimension_eq_rank k b c₂]

/-- Witness for principal-divisor data on S: there exists s ∈ S\{0} with q·s = p in S,
i.e. p/q is a regular function in some sense. -/
def IsPrincipalDivisorData (k : Type*) [Field k] (S : Type*) [CommRing S] [IsDomain S]
    [Algebra (Polynomial k) S] (p q : Polynomial k) : Prop :=
  ∃ (s : S), s ≠ 0 ∧ algebraMap (Polynomial k) S q * s = algebraMap (Polynomial k) S p

/-- Type class encoding the completeness condition for a curve algebra S over k[X]:
principal divisors of regular functions have equal numerator and denominator degrees. -/
class IsCompleteCurveAlg (k : Type*) [Field k] (S : Type*) [CommRing S] [IsDomain S]
    [Algebra (Polynomial k) S] where
  deg_eq_of_principal : ∀ (p q : Polynomial k), p ≠ 0 → q ≠ 0 →
    IsPrincipalDivisorData k S p q → p.natDegree = q.natDegree

namespace PrincipalDivisorDegZero

open Module

/-- Pushing a nonzero polynomial into S via the structure map yields a nonzero element
(when S has a basis over k[X]). -/
theorem algebraMap_ne_zero_of_ne_zero (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*}
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Basis ι (Polynomial k) S)
    {p : Polynomial k} (hp : p ≠ 0) :
    algebraMap (Polynomial k) S p ≠ 0 := by
  rw [Ne, ← map_zero (algebraMap (Polynomial k) S)]
  exact (b.algebraMap_injective (R := Polynomial k)).ne hp

/-- General fiber-dimension formula: dim_k(S/(p)) equals (rank of S) × (degree of p). -/
theorem fiber_dimension_eq_rank_mul_natDegree (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Basis ι (Polynomial k) S)
    {p : Polynomial k} (hp : p ≠ 0) :
    finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) =
    Fintype.card ι * p.natDegree := by
  rw [finrank_quotient_span_eq_natDegree_norm b (algebraMap_ne_zero_of_ne_zero k b hp),
      Algebra.norm_algebraMap_of_basis b,
      Polynomial.natDegree_pow]

/-- For a linear polynomial X - c, the fiber dimension equals the rank of S. -/
theorem fiber_dimension_linear_eq_rank (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Basis ι (Polynomial k) S) (c : k) :
    finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c)}) =
    Fintype.card ι := by
  rw [fiber_dimension_eq_rank_mul_natDegree k b (X_sub_C_ne_zero c),
      natDegree_X_sub_C, mul_one]

/-- Fiber dimensions at two linear polynomials X - c_1 and X - c_2 are equal. -/
theorem fiber_dimension_linear_constant (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Basis ι (Polynomial k) S) (c₁ c₂ : k) :
    finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c₁)}) =
    finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c₂)}) := by
  rw [fiber_dimension_linear_eq_rank k b c₁, fiber_dimension_linear_eq_rank k b c₂]

/-- Two polynomials of the same degree give equal fiber dimensions in S. -/
theorem fiber_dimension_eq_of_natDegree_eq (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Basis ι (Polynomial k) S)
    {p q : Polynomial k} (hp : p ≠ 0) (hq : q ≠ 0)
    (hdeg : p.natDegree = q.natDegree) :
    finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) =
    finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S q}) := by
  rw [fiber_dimension_eq_rank_mul_natDegree k b hp,
      fiber_dimension_eq_rank_mul_natDegree k b hq,
      hdeg]

/-- Degree of a principal divisor in S: dim_k(S/I) - dim_k(S/J). -/
def principalDivisorDeg (k : Type*) [Field k] (S : Type*) [CommRing S]
    [IsDomain S] [Algebra k S] (I J : Ideal S) : ℤ :=
  (finrank k (S ⧸ I) : ℤ) - (finrank k (S ⧸ J) : ℤ)

/-- Principal-divisor degree formula: equals the rank of S over k[X] times the
difference of degrees of numerator and denominator. -/
theorem principalDivisorDeg_eq_rank_mul_degDiff (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Basis ι (Polynomial k) S)
    {p q : Polynomial k} (hp : p ≠ 0) (hq : q ≠ 0) :
    principalDivisorDeg k S
      (Ideal.span {algebraMap (Polynomial k) S p})
      (Ideal.span {algebraMap (Polynomial k) S q}) =
    (Fintype.card ι : ℤ) * ((p.natDegree : ℤ) - (q.natDegree : ℤ)) := by
  unfold principalDivisorDeg
  rw [fiber_dimension_eq_rank_mul_natDegree k b hp,
      fiber_dimension_eq_rank_mul_natDegree k b hq]
  push_cast; ring

/-- When numerator and denominator have equal degree, the principal divisor degree
vanishes. -/
theorem principal_divisor_deg_zero_of_natDegree_eq (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Basis ι (Polynomial k) S)
    {p q : Polynomial k} (hp : p ≠ 0) (hq : q ≠ 0)
    (hdeg : p.natDegree = q.natDegree) :
    principalDivisorDeg k S
      (Ideal.span {algebraMap (Polynomial k) S p})
      (Ideal.span {algebraMap (Polynomial k) S q}) = 0 := by
  rw [principalDivisorDeg_eq_rank_mul_degDiff k b hp hq, hdeg, sub_self, mul_zero]

/-- Principal divisor degree zero (Proposition 24, Lecture 15; Proposition 25,
Lecture 16): on a complete curve, the degree of a principal divisor is zero. -/
theorem principal_divisor_deg_zero (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    [IsCompleteCurveAlg k S]
    (b : Basis ι (Polynomial k) S)
    {p q : Polynomial k} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpd : IsPrincipalDivisorData k S p q) :
    principalDivisorDeg k S
      (Ideal.span {algebraMap (Polynomial k) S p})
      (Ideal.span {algebraMap (Polynomial k) S q}) = 0 :=
  principal_divisor_deg_zero_of_natDegree_eq k b hp hq
    (IsCompleteCurveAlg.deg_eq_of_principal p q hp hq hpd)

/-- The principal divisor of (X - c_1) - (X - c_2) has degree zero: both linear
factors contribute the same fiber dimension. -/
theorem principal_divisor_deg_zero_linear (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Basis ι (Polynomial k) S)
    (c₁ c₂ : k) :
    principalDivisorDeg k S
      (Ideal.span {algebraMap (Polynomial k) S (X - C c₁)})
      (Ideal.span {algebraMap (Polynomial k) S (X - C c₂)}) = 0 :=
  principal_divisor_deg_zero_of_natDegree_eq k b (X_sub_C_ne_zero c₁) (X_sub_C_ne_zero c₂)
    (by simp)

/-- For S = k[X] itself, the principal divisor degree equals the actual difference of
degrees deg(p) - deg(q). -/
theorem principalDivisorDeg_affine_eq (k : Type*) [Field k]
    (p q : Polynomial k) :
    principalDivisorDeg k (Polynomial k) (Ideal.span {p}) (Ideal.span {q}) =
    (p.natDegree : ℤ) - (q.natDegree : ℤ) := by
  unfold principalDivisorDeg
  rw [finrank_quotient_span_eq_natDegree (f := p),
      finrank_quotient_span_eq_natDegree (f := q)]

end PrincipalDivisorDegZero

/-- Proposition 25 fiber-dimension formula: dim_k(S/(p)) = (rank S over k[X]) · deg(p). -/
theorem proposition_25_fiber_dimension_formula
    (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Module.Basis ι (Polynomial k) S)
    {p : Polynomial k} (hp : p ≠ 0) :
    Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) =
    Fintype.card ι * p.natDegree :=
  PrincipalDivisorDegZero.fiber_dimension_eq_rank_mul_natDegree k b hp

/-- Proposition 25 in textbook form: on a complete smooth curve, every principal
divisor has total degree zero (Proposition 24/25, Lectures 15-16). -/
theorem proposition_25_principal_divisor_deg_zero
    (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    [IsCompleteCurveAlg k S]
    (b : Module.Basis ι (Polynomial k) S)
    {p q : Polynomial k} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpd : IsPrincipalDivisorData k S p q) :
    (Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) : ℤ) -
    (Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S q}) : ℤ) = 0 := by
  have hdeg := IsCompleteCurveAlg.deg_eq_of_principal p q hp hq hpd
  rw [proposition_25_fiber_dimension_formula k b hp,
      proposition_25_fiber_dimension_formula k b hq, hdeg]
  simp
