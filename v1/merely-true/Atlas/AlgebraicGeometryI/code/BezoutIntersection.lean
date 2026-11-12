/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.LinearEquivDivisors
import Atlas.AlgebraicGeometryI.code.PrincipalDivisorDegree
import Atlas.AlgebraicGeometryI.code.BezoutTheorem
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option maxHeartbeats 1600000

open Polynomial Module

noncomputable section

namespace BezoutIntersection

set_option synthInstance.maxHeartbeats 200000 in
/-- Multiplication-by-`X` operator on the quotient `k[X][Y]/⟨f, g⟩`, viewed as a `k`-linear
endomorphism. -/
def mulByXOp (k : Type*) [Field k]
    (f g : Polynomial (Polynomial k)) :
    Module.End k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g}) :=
  (Algebra.lmul k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g}))
    (Ideal.Quotient.mk _ X)

set_option synthInstance.maxHeartbeats 200000 in
/-- Multiplication-by-`Y` operator (i.e. by `C X` in `k[X][Y]`) on the quotient
`k[X][Y]/⟨f, g⟩`, viewed as a `k`-linear endomorphism. -/
def mulByYOp (k : Type*) [Field k]
    (f g : Polynomial (Polynomial k)) :
    Module.End k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g}) :=
  (Algebra.lmul k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g}))
    (Ideal.Quotient.mk _ (C X))

set_option synthInstance.maxHeartbeats 200000 in

/-- Local intersection multiplicity of the affine plane curves `f = 0` and `g = 0` at the
point `(a, b)`, defined as the dimension of the simultaneous generalised eigenspace of the
multiplication-by-`X` and multiplication-by-`Y` operators with eigenvalues `a` and `b`. -/
noncomputable def localIntersectionMultiplicity (k : Type*) [Field k]
    (f g : Polynomial (Polynomial k)) (a b : k) : ℕ :=
  finrank k ↥(
    (mulByXOp k f g).genEigenspace a ⊤ ⊓
    (mulByYOp k f g).genEigenspace b ⊤
      : Submodule k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g}))

/-- Total intersection number of `f` and `g`, equal to the `k`-dimension of the quotient
`k[X][Y]/⟨f, g⟩`. Bezout's theorem identifies this with `deg(f) · deg(g)`. -/
def totalIntersectionNumber (k : Type*) [Field k]
    (f g : Polynomial (Polynomial k)) : ℕ :=
  finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g})


/-- The total intersection number can equivalently be computed as the `k`-dimension of the
quotient by the supremum of the principal ideals `⟨f⟩` and `⟨g⟩`. -/
theorem totalIntersectionNumber_eq_sup (k : Type*) [Field k]
    (f g : Polynomial (Polynomial k)) :
    totalIntersectionNumber k f g =
    finrank k (Polynomial (Polynomial k) ⧸ (Ideal.span {f} ⊔ Ideal.span {g})) :=
  LinearEquiv.finrank_eq
    (Ideal.quotientEquivAlgOfEq k (ideal_span_pair_eq_sup f g)).toLinearEquiv

set_option synthInstance.maxHeartbeats 80000 in
/-- Bezout's theorem for an irreducible monic `g` against a polynomial of the form `C p`:
the total intersection number equals `deg(g) · deg(p)`. -/
theorem bezout_irreducible_base (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic) (hirr : Irreducible g)
    (p : Polynomial k)
    (hp : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0) :
    totalIntersectionNumber k g (Polynomial.C p) =
    g.natDegree * p.natDegree := by
  haveI : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hirr.prime
  unfold totalIntersectionNumber
  rw [ideal_span_pair_eq_sup]
  exact bezout_bivariate_base k g hg p hp

/-- Additivity of intersection with a product: the `k`-dimension of the quotient by `f₁ · f₂`
in `AdjoinRoot g` splits as the sum of the dimensions for `f₁` and `f₂`. -/
theorem intersection_additivity (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic)
    [IsDomain (AdjoinRoot g)]
    (f₁ f₂ : Polynomial k) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) :
    finrank k (AdjoinRoot g ⧸
      Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) (f₁ * f₂)}) =
    finrank k (AdjoinRoot g ⧸
      Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) f₁}) +
    finrank k (AdjoinRoot g ⧸
      Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) f₂}) := by
  have b := (AdjoinRoot.powerBasis' hg).basis
  have hinj : Function.Injective (algebraMap (Polynomial k) (AdjoinRoot g)) :=
    b.algebraMap_injective
  have hf₁' : algebraMap (Polynomial k) (AdjoinRoot g) f₁ ≠ 0 :=
    fun h => hf₁ (hinj (h.trans (map_zero _).symm))
  have hf₂' : algebraMap (Polynomial k) (AdjoinRoot g) f₂ ≠ 0 :=
    fun h => hf₂ (hinj (h.trans (map_zero _).symm))
  have hf₁₂ : f₁ * f₂ ≠ 0 := mul_ne_zero hf₁ hf₂
  have hf₁₂' : algebraMap (Polynomial k) (AdjoinRoot g) (f₁ * f₂) ≠ 0 :=
    fun h => hf₁₂ (hinj (h.trans (map_zero _).symm))
  rw [finrank_quotient_span_eq_natDegree_norm b hf₁₂',
      Algebra.norm_algebraMap_of_basis b, Polynomial.natDegree_pow,
      finrank_quotient_span_eq_natDegree_norm b hf₁',
      Algebra.norm_algebraMap_of_basis b, Polynomial.natDegree_pow,
      finrank_quotient_span_eq_natDegree_norm b hf₂',
      Algebra.norm_algebraMap_of_basis b, Polynomial.natDegree_pow,
      Polynomial.natDegree_mul hf₁ hf₂,
      Fintype.card_fin, AdjoinRoot.powerBasis'_dim]
  ring

/-- The `k`-dimension of the quotient `AdjoinRoot g / ⟨p⟩` depends only on the degree of `p`. -/
theorem intersection_depends_only_on_degree (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic)
    [IsDomain (AdjoinRoot g)]
    (p q : Polynomial k) (hp : p ≠ 0) (hq : q ≠ 0)
    (hdeg : p.natDegree = q.natDegree) :
    finrank k (AdjoinRoot g ⧸
      Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) p}) =
    finrank k (AdjoinRoot g ⧸
      Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) q}) := by
  have b := (AdjoinRoot.powerBasis' hg).basis
  have hinj := b.algebraMap_injective (R := Polynomial k)
  have hp' : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0 :=
    fun h => hp (hinj (h.trans (map_zero _).symm))
  have hq' : algebraMap (Polynomial k) (AdjoinRoot g) q ≠ 0 :=
    fun h => hq (hinj (h.trans (map_zero _).symm))
  rw [finrank_quotient_span_eq_natDegree_norm b hp',
      finrank_quotient_span_eq_natDegree_norm b hq',
      Algebra.norm_algebraMap_of_basis b,
      Algebra.norm_algebraMap_of_basis b,
      Polynomial.natDegree_pow,
      Polynomial.natDegree_pow,
      hdeg]

/-- Degree formula: `dim_k (AdjoinRoot g / ⟨p⟩) = deg(g) · deg(p)`. -/
theorem divisor_degree_of_intersection (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic)
    [IsDomain (AdjoinRoot g)]
    (p : Polynomial k) (hp : p ≠ 0) :
    finrank k (AdjoinRoot g ⧸
      Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) p}) =
    g.natDegree * p.natDegree := by
  have b := (AdjoinRoot.powerBasis' hg).basis
  have hinj := b.algebraMap_injective (R := Polynomial k)
  have hp' : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0 :=
    fun h => hp (hinj (h.trans (map_zero _).symm))
  rw [finrank_quotient_algebraMap k b p hp', Fintype.card_fin,
      AdjoinRoot.powerBasis'_dim]

/-- Bezout's theorem (final packaging): for an irreducible monic `g` and `p ∈ k[X]` nonzero
in the quotient, the total intersection number of `g` and `C p` is `deg(g) · deg(p)`. -/
theorem bezout_theorem (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic) (hirr : Irreducible g)
    (p : Polynomial k)
    (hp : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0) :
    totalIntersectionNumber k g (Polynomial.C p) =
    g.natDegree * p.natDegree :=
  bezout_irreducible_base k g hg hirr p hp

end BezoutIntersection
