/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.Polynomial.Quotient

open Polynomial

noncomputable section

namespace Prop24Picard

variable {Y : Type*}

/-- Weil divisors on a curve `Y`: finitely supported integer-valued functions on the
underlying point set. -/
abbrev WeilDiv (Y : Type*) := Y →₀ ℤ

/-- The degree map on Weil divisors: sum of multiplicities. -/
noncomputable def weilDegree : WeilDiv Y →+ ℤ where
  toFun D := D.sum (fun _ n => n)
  map_zero' := by simp [Finsupp.sum]
  map_add' := by
    intro a b
    classical
    exact Finsupp.sum_add_index (by simp) (by intros; rfl)

/-- Fiber-dimension formula: for a free `k[X]`-module `S` of rank `|ι|` and a nonzero
`p ∈ k[X]`, the `k`-dimension of `S / (p)` equals `|ι| · deg p`. -/
theorem fiber_dimension_formula (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Module.Basis ι (Polynomial k) S)
    {p : Polynomial k} (hp : p ≠ 0) :
    Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) =
    Fintype.card ι * p.natDegree := by
  have hpne : algebraMap (Polynomial k) S p ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (Polynomial k) S)]
    exact (b.algebraMap_injective (R := Polynomial k)).ne hp
  rw [finrank_quotient_span_eq_natDegree_norm b hpne,
      Algebra.norm_algebraMap_of_basis b,
      Polynomial.natDegree_pow]

/-- Proposition 24: the degree of a principal divisor `(p) − (q)` of two polynomials of
the same degree is zero. -/
theorem prop24_degree_principal_divisor_eq_zero (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Module.Basis ι (Polynomial k) S)
    {p q : Polynomial k} (hp : p ≠ 0) (hq : q ≠ 0)
    (hdeg : p.natDegree = q.natDegree) :
    (Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) : ℤ) -
    (Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S q}) : ℤ) = 0 := by
  rw [fiber_dimension_formula k b hp, fiber_dimension_formula k b hq, hdeg, sub_self]

/-- Specialisation of the fiber-dimension formula at a linear polynomial `X - c`:
the fiber over a point has dimension equal to the rank of the basis. -/
theorem fiber_dimension_eq_rank (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Module.Basis ι (Polynomial k) S) (c : k) :
    Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c)}) =
    Fintype.card ι := by
  rw [fiber_dimension_formula k b (X_sub_C_ne_zero c), natDegree_X_sub_C, mul_one]

/-- The fiber dimension at two different constants `c₁`, `c₂` coincide. -/
theorem fiber_dimension_constant (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Module.Basis ι (Polynomial k) S) (c₁ c₂ : k) :
    Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c₁)}) =
    Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c₂)}) := by
  rw [fiber_dimension_eq_rank k b c₁, fiber_dimension_eq_rank k b c₂]

/-- The degree homomorphism descends from Weil divisors to `Pic(Y) = WeilDiv / P` when
`P` is a subgroup of degree-zero divisors. -/
noncomputable def degPic (P : AddSubgroup (WeilDiv Y))
    (hP : ∀ D ∈ P, weilDegree D = 0) :
    (WeilDiv Y ⧸ P) →+ ℤ :=
  QuotientAddGroup.lift P weilDegree (fun x hx => hP x hx)

/-- The degree map on the Picard group computes the Weil degree of a chosen lift. -/
theorem degPic_mk (P : AddSubgroup (WeilDiv Y))
    (hP : ∀ D ∈ P, weilDegree D = 0)
    (D : WeilDiv Y) :
    degPic P hP (QuotientAddGroup.mk D) = weilDegree D := by
  simp [degPic, QuotientAddGroup.lift_mk]

end Prop24Picard
