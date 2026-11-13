/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Algebra.Polynomial.Monic

set_option maxHeartbeats 400000

open Polynomial

/-- The `k`-dimension of `k[X] / ⟨f⟩` equals the degree of `f`. -/
theorem finrank_quotient_polynomial_eq_natDegree (k : Type*) [Field k] (f : Polynomial k) :
    Module.finrank k (Polynomial k ⧸ Ideal.span {f}) = f.natDegree :=
  finrank_quotient_span_eq_natDegree

/-- The quotient `k[X] / ⟨X⟩` has `k`-dimension `1`. -/
theorem finrank_quotient_X (k : Type*) [Field k] :
    Module.finrank k (Polynomial k ⧸ Ideal.span {(X : Polynomial k)}) = 1 := by
  rw [finrank_quotient_span_eq_natDegree, natDegree_X]

/-- The quotient `k[X] / ⟨X - c⟩` has `k`-dimension `1` for any scalar `c`. -/
theorem finrank_quotient_X_sub_C (k : Type*) [Field k] (c : k) :
    Module.finrank k (Polynomial k ⧸ Ideal.span {(X : Polynomial k) - C c}) = 1 := by
  rw [finrank_quotient_span_eq_natDegree, natDegree_X_sub_C]

/-- Two transverse lines `Y = 0` and `X = 0` in the affine plane meet in a single point: the
quotient `k[X][Y] / ⟨C X, X⟩` has `k`-dimension `1`. -/
theorem line_line_intersection_dim (k : Type*) [Field k] :
    Module.finrank k (Polynomial (Polynomial k) ⧸
      Ideal.span {Polynomial.C (X : Polynomial k), (X : Polynomial (Polynomial k))}) = 1 := by

  have hgens : (Ideal.span {Polynomial.C (X : Polynomial k),
      (X : Polynomial (Polynomial k))} : Ideal (Polynomial (Polynomial k))) =
    Ideal.span {Polynomial.C (X - C (0 : k)),
      (X : Polynomial (Polynomial k)) - C (0 : Polynomial k)} := by simp

  have e := @Polynomial.quotientSpanCXSubCXSubCAlgEquiv k _ (0 : k) (0 : Polynomial k)
  rw [show (1 : ℕ) = Module.finrank k k from (Module.finrank_self k).symm]
  exact LinearEquiv.finrank_eq ((Ideal.quotientEquivAlgOfEq k hgens).trans e).toLinearEquiv

/-- Algebra isomorphism relating the bivariate quotient `k[X][Y] / ⟨C(X² + 1), Y⟩` to the
univariate quotient `k[X] / ⟨X² + 1⟩`, used to compute the line/conic intersection dimension. -/
noncomputable def lineConicQuotientEquiv (k : Type*) [Field k] :
    (Polynomial (Polynomial k) ⧸ Ideal.span
      {Polynomial.C ((X : Polynomial k)^2 + 1), (X : Polynomial (Polynomial k))})
      ≃ₐ[Polynomial k]
    (Polynomial k ⧸ Ideal.span {(X : Polynomial k)^2 + 1}) := by
  have h : (Ideal.span {Polynomial.C ((X : Polynomial k)^2 + 1),
      (X : Polynomial (Polynomial k))} : Ideal (Polynomial (Polynomial k))) =
    Ideal.span {Polynomial.C ((X : Polynomial k)^2 + 1),
      (X : Polynomial (Polynomial k)) - C 0} := by simp
  exact (Ideal.quotientEquivAlgOfEq (Polynomial k) h).trans
    (quotientSpanCXSubCAlgEquiv ((X : Polynomial k)^2 + 1) (0 : Polynomial k))

/-- A line meets a conic (the conic `X² + 1 = 0`) in `2` points: the corresponding bivariate
quotient has `k`-dimension `2`. -/
theorem line_conic_intersection_dim (k : Type*) [Field k] :
    Module.finrank k (Polynomial (Polynomial k) ⧸
      Ideal.span {Polynomial.C ((X : Polynomial k)^2 + 1),
        (X : Polynomial (Polynomial k))}) = 2 := by
  have e := lineConicQuotientEquiv k
  rw [LinearEquiv.finrank_eq ((e.restrictScalars k).toLinearEquiv)]
  rw [finrank_quotient_span_eq_natDegree]
  compute_degree!

/-- The `k`-dimension of `k[X] / ⟨f · g⟩` is the sum of the degrees of `f` and `g`. -/
theorem finrank_quotient_coprime_product (k : Type*) [Field k]
    (f g : Polynomial k) (hf : f ≠ 0) (hg : g ≠ 0) :
    Module.finrank k (Polynomial k ⧸ Ideal.span {f * g}) =
    f.natDegree + g.natDegree := by
  rw [finrank_quotient_span_eq_natDegree, Polynomial.natDegree_mul hf hg]

/-- Chinese remainder theorem for coprime polynomials: `k[X] / ⟨f g⟩ ≅ k[X]/⟨f⟩ × k[X]/⟨g⟩`. -/
noncomputable def coprime_polynomial_CRT (k : Type*) [Field k]
    (f g : Polynomial k) (hfg : IsCoprime f g) :
    (Polynomial k ⧸ Ideal.span {f * g}) ≃+*
    (Polynomial k ⧸ Ideal.span {f}) × (Polynomial k ⧸ Ideal.span {g}) := by
  have hsup : Ideal.span {f} ⊔ Ideal.span {g} = ⊤ :=
    (Ideal.sup_eq_top_iff_isCoprime f g).mpr hfg
  have hinf : Ideal.span {f * g} = Ideal.span {f} ⊓ Ideal.span {g} := by
    rw [← Ideal.span_singleton_mul_span_singleton,
        Ideal.mul_eq_inf_of_coprime hsup]
  exact (Ideal.quotEquivOfEq hinf).trans
    (Ideal.quotientInfEquivQuotientProd _ _
      (Ideal.isCoprime_iff_sup_eq.mpr hsup))

/-- Norm-based degree formula: for a free `k[X]`-algebra `S` with basis indexed by `ι`,
`dim_k (S / ⟨algebraMap p⟩) = |ι| · deg(p)`. -/
theorem finrank_quotient_algebraMap (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Module.Basis ι (Polynomial k) S)
    (p : Polynomial k) (hp : algebraMap (Polynomial k) S p ≠ 0) :
    Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) =
    Fintype.card ι * p.natDegree := by
  rw [finrank_quotient_span_eq_natDegree_norm b hp,
      Algebra.norm_algebraMap_of_basis b,
      Polynomial.natDegree_pow]

/-- A degree-one principal divisor `X - c` cuts out a fibre of length `|ι|` in any free
`k[X]`-algebra `S` with basis indexed by `ι`. -/
theorem principal_divisor_degree_one (k : Type*) [Field k]
    {S : Type*} [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι]
    [Algebra (Polynomial k) S] [Algebra k S] [IsScalarTower k (Polynomial k) S]
    (b : Module.Basis ι (Polynomial k) S)
    (c : k) :
    Module.finrank k
      (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c)}) =
    Fintype.card ι := by
  have hp : algebraMap (Polynomial k) S (X - C c) ≠ 0 := by
    intro h
    have hinj : Function.Injective (algebraMap (Polynomial k) S) :=
      Module.Basis.algebraMap_injective b
    have := hinj (h.trans (map_zero _).symm)
    have : (X - C c : Polynomial k) ≠ 0 := by
      intro heq; have := congr_arg natDegree heq; simp at this
    contradiction
  rw [finrank_quotient_algebraMap k b _ hp, natDegree_X_sub_C, mul_one]

/-- For a monic polynomial `g ∈ R[X]`, the quotient `R[X] / ⟨g⟩` is a finitely generated
`R`-module. -/
theorem quotient_polynomial_module_finite (R : Type*) [CommRing R]
    (g : Polynomial R) (hg : g.Monic) :
    Module.Finite R (Polynomial R ⧸ Ideal.span {g}) :=
  hg.finite_adjoinRoot

/-- The canonical power basis `1, X, X², …, X^{deg g - 1}` of `R[X] / ⟨g⟩` over `R` when `g`
is monic. -/
noncomputable def quotient_polynomial_powerBasis (R : Type*) [CommRing R]
    (g : Polynomial R) (hg : g.Monic) :
    PowerBasis R (AdjoinRoot g) :=
  AdjoinRoot.powerBasis' hg

/-- Algebraic form of Bezout: `dim_k (AdjoinRoot g / ⟨f⟩) = deg(g) · deg(f)` when `g` is
monic and the image of `f` is nonzero. -/
theorem bezout_algebraic (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic)
    [IsDomain (AdjoinRoot g)]
    (f : Polynomial k)
    (hf : algebraMap (Polynomial k) (AdjoinRoot g) f ≠ 0) :
    Module.finrank k (AdjoinRoot g ⧸ Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) f}) =
    g.natDegree * f.natDegree := by
  have b := (AdjoinRoot.powerBasis' hg).basis
  rw [finrank_quotient_span_eq_natDegree_norm b hf,
      Algebra.norm_algebraMap_of_basis b,
      Polynomial.natDegree_pow,
      Fintype.card_fin, AdjoinRoot.powerBasis'_dim]

/-- Algebra isomorphism `k[X][Y] / (⟨g⟩ + ⟨f⟩) ≅ AdjoinRoot g / ⟨[f]⟩` obtained via the
quotient-of-quotients construction. -/
noncomputable def bivariate_quotient_equiv (k : Type*) [Field k]
    (f g : Polynomial (Polynomial k)) :
    (Polynomial (Polynomial k) ⧸ (Ideal.span {g} ⊔ Ideal.span {f})) ≃ₐ[k]
    (AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.mk g f}) := by
  have h : Ideal.map (Ideal.Quotient.mkₐ k (Ideal.span {g})) (Ideal.span {f}) =
      Ideal.span {AdjoinRoot.mk g f} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  exact (DoubleQuot.quotQuotEquivQuotSupₐ k (Ideal.span {g}) (Ideal.span {f})).symm.trans
    (Ideal.quotientEquivAlgOfEq k h)

/-- Norm form of bivariate Bezout: the `k`-dimension of `k[X][Y] / (⟨g⟩ + ⟨f⟩)` equals the
degree of `Norm_{k[X]} ([f])`. -/
theorem bezout_bivariate_norm (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic)
    [IsDomain (AdjoinRoot g)]
    (f : Polynomial (Polynomial k))
    (hf : AdjoinRoot.mk g f ≠ 0) :
    Module.finrank k (Polynomial (Polynomial k) ⧸ (Ideal.span {g} ⊔ Ideal.span {f})) =
    (Algebra.norm (Polynomial k) (AdjoinRoot.mk g f)).natDegree := by
  rw [LinearEquiv.finrank_eq (bivariate_quotient_equiv k f g).toLinearEquiv]
  exact finrank_quotient_span_eq_natDegree_norm (AdjoinRoot.powerBasis' hg).basis hf

/-- Bivariate Bezout for constant `C p`: `dim_k (k[X][Y] / (⟨g⟩ + ⟨C p⟩)) = deg(g) · deg(p)`. -/
theorem bezout_bivariate_base (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic)
    [IsDomain (AdjoinRoot g)]
    (p : Polynomial k)
    (hp : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0) :
    Module.finrank k (Polynomial (Polynomial k) ⧸
      (Ideal.span {g} ⊔ Ideal.span {Polynomial.C p})) =
    g.natDegree * p.natDegree := by
  have hmk : AdjoinRoot.mk g (Polynomial.C p) = algebraMap (Polynomial k) (AdjoinRoot g) p := rfl
  have hf : AdjoinRoot.mk g (Polynomial.C p) ≠ 0 := hmk ▸ hp
  rw [bezout_bivariate_norm k g hg (Polynomial.C p) hf, hmk]
  have b := (AdjoinRoot.powerBasis' hg).basis
  rw [Algebra.norm_algebraMap_of_basis b, Polynomial.natDegree_pow,
      Fintype.card_fin, AdjoinRoot.powerBasis'_dim]

/-- Variant of `bezout_algebraic` that derives the integral-domain hypothesis from irreducibility
of `g`. -/
theorem bezout_algebraic_irreducible (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic) (hirr : Irreducible g)
    (f : Polynomial k)
    (hf : algebraMap (Polynomial k) (AdjoinRoot g) f ≠ 0) :
    Module.finrank k (AdjoinRoot g ⧸
      Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) f}) =
    g.natDegree * f.natDegree := by
  haveI : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hirr.prime
  exact bezout_algebraic k g hg f hf

/-- The ideal spanned by a pair `{a, b}` equals the supremum of the singleton ideals. -/
lemma ideal_span_pair_eq_sup {R : Type*} [Semiring R] (a b : R) :
    (Ideal.span {a, b} : Ideal R) = Ideal.span {a} ⊔ Ideal.span {b} := by
  rw [← Ideal.span_insert]

/-- Bivariate Bezout, span-of-pair form: `dim_k (k[X][Y] / ⟨g, C p⟩) = deg(g) · deg(p)`. -/
theorem bezout_bivariate_product (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic) (hirr : Irreducible g)
    (p : Polynomial k)
    (hp : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0) :
    Module.finrank k (Polynomial (Polynomial k) ⧸
      Ideal.span {g, Polynomial.C p}) =
    g.natDegree * p.natDegree := by
  haveI : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hirr.prime
  rw [ideal_span_pair_eq_sup]
  exact bezout_bivariate_base k g hg p hp

/-- Norm form of bivariate Bezout for an irreducible monic `g`, using the span-of-pair
presentation of the ideal. -/
theorem bezout_bivariate_norm_irreducible (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic) (hirr : Irreducible g)
    (f : Polynomial (Polynomial k))
    (hf : AdjoinRoot.mk g f ≠ 0) :
    Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {g, f}) =
    (Algebra.norm (Polynomial k) (AdjoinRoot.mk g f)).natDegree := by
  haveI : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hirr.prime
  rw [ideal_span_pair_eq_sup]
  exact bezout_bivariate_norm k g hg f hf

/-- Full Bezout statement: given the degree of the norm of `[f]`, the `k`-dimension of
`k[X][Y] / ⟨g, f⟩` is precisely that degree. -/
theorem bezout_full (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic) (hirr : Irreducible g)
    (f : Polynomial (Polynomial k))
    (hf : AdjoinRoot.mk g f ≠ 0)
    {n : ℕ}
    (hnorm : (Algebra.norm (Polynomial k) (AdjoinRoot.mk g f)).natDegree = n) :
    Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {g, f}) = n := by
  haveI : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hirr.prime
  calc Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {g, f})
      = Module.finrank k (Polynomial (Polynomial k) ⧸
          (Ideal.span {g} ⊔ Ideal.span {f})) :=
        LinearEquiv.finrank_eq (Ideal.quotientEquivAlgOfEq k (ideal_span_pair_eq_sup g f)).toLinearEquiv
    _ = Module.finrank k (AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.mk g f}) :=
        LinearEquiv.finrank_eq (bivariate_quotient_equiv k f g).toLinearEquiv
    _ = (Algebra.norm (Polynomial k) (AdjoinRoot.mk g f)).natDegree :=
        finrank_quotient_span_eq_natDegree_norm (AdjoinRoot.powerBasis' hg).basis hf
    _ = n := hnorm

/-- Norm-degree base computation: `deg (Norm_{k[X]} (C p mod g)) = deg(g) · deg(p)`. -/
theorem bezout_norm_degree_base (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic)
    (p : Polynomial k) :
    (Algebra.norm (Polynomial k) (AdjoinRoot.mk g (Polynomial.C p))).natDegree =
    g.natDegree * p.natDegree := by
  have hmk : AdjoinRoot.mk g (Polynomial.C p) = algebraMap (Polynomial k) (AdjoinRoot g) p := rfl
  rw [hmk, Algebra.norm_algebraMap_of_basis (AdjoinRoot.powerBasis' hg).basis,
      Polynomial.natDegree_pow, Fintype.card_fin, AdjoinRoot.powerBasis'_dim]

/-- Two conics defined by `Y² + 1` and `X² + 1` meet in `2 · 2 = 4` points: the bivariate
quotient has `k`-dimension `4`. -/
theorem conic_conic_intersection_dim (k : Type*) [Field k]
    [IsDomain (AdjoinRoot ((X : Polynomial (Polynomial k))^2 + C (1 : Polynomial k)))]
    (hne : algebraMap (Polynomial k)
      (AdjoinRoot ((X : Polynomial (Polynomial k))^2 + C (1 : Polynomial k)))
      ((X : Polynomial k)^2 + 1) ≠ 0) :
    Module.finrank k (Polynomial (Polynomial k) ⧸
      Ideal.span {(X : Polynomial (Polynomial k))^2 + C (1 : Polynomial k),
        C ((X : Polynomial k)^2 + 1)}) = 4 := by
  rw [ideal_span_pair_eq_sup]
  have hg : ((X : Polynomial (Polynomial k))^2 + C (1 : Polynomial k)).Monic :=
    monic_X_pow_add_C _ (by norm_num)
  rw [bezout_bivariate_base k _ hg _ hne]

  have h1 : natDegree ((X : Polynomial (Polynomial k))^2 + C (1 : Polynomial k)) = 2 := by
    compute_degree!
  have h2 : natDegree ((X : Polynomial k)^2 + 1) = 2 := by compute_degree!
  rw [h1, h2]
