/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Smooth.Basic

noncomputable section

open scoped TensorProduct
open Polynomial KaehlerDifferential Module

universe u v

section UniversalProperty

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Universal property of Kähler differentials (Def 34, Lec 18): S-linear maps
`Ω[S⁄R] →ₗ[S] M` are in (S-linear) bijection with R-derivations `Der R S M`. -/
theorem kaehlerDifferential_universalProperty
    {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    Nonempty ((Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] Derivation R S M) :=
  ⟨KaehlerDifferential.linearMapEquivDerivation R S⟩

/-- The explicit S-linear equivalence `(Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] Der R S M` witnessing the
universal property of Kähler differentials. -/
def kaehlerDifferentialEquivDerivation
    {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    (Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] Derivation R S M :=
  KaehlerDifferential.linearMapEquivDerivation R S

/-- Existence half of the universal property: every derivation `D'` factors through
the universal derivation `d : S → Ω[S⁄R]` via `liftKaehlerDifferential`. -/
theorem kaehlerDifferential_lift_comp
    {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (D' : Derivation R S M) :
    D'.liftKaehlerDifferential.compDer (KaehlerDifferential.D R S) = D' :=
  D'.liftKaehlerDifferential_comp

/-- Uniqueness half of the universal property: two S-linear maps out of `Ω[S⁄R]`
that agree on the image of the universal derivation are equal. -/
theorem kaehlerDifferential_lift_unique
    {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (f g : Ω[S⁄R] →ₗ[S] M)
    (hf : f.compDer (KaehlerDifferential.D R S) = g.compDer (KaehlerDifferential.D R S)) :
    f = g :=
  Derivation.liftKaehlerDifferential_unique f g hf

/-- The module of Kähler differentials `Ω[S⁄R]` is generated as an S-module by the
image of the universal derivation `d : S → Ω[S⁄R]`. -/
theorem kaehlerDifferential_span_range :
    Submodule.span S (Set.range (KaehlerDifferential.D R S)) = ⊤ :=
  KaehlerDifferential.span_range_derivation R S

end UniversalProperty

section PolynomialDifferentials

variable (k : Type u) [CommRing k]

/-- For the polynomial algebra `k[X]`, the Kähler differentials are a free rank-one
module: `Ω[k[X]⁄k] ≃ₗ[k[X]] k[X]`, with `dX` corresponding to `1`. -/
def kaehlerDifferential_polynomial_equiv :
    Ω[Polynomial k⁄k] ≃ₗ[Polynomial k] Polynomial k :=
  KaehlerDifferential.polynomialEquiv k

/-- `Ω[k[X]⁄k]` is a free `k[X]`-module (in fact free of rank one). -/
theorem kaehlerDifferential_polynomial_free :
    Module.Free (Polynomial k) (Ω[Polynomial k⁄k]) :=
  Module.Free.of_equiv (KaehlerDifferential.polynomialEquiv k).symm

/-- The rank of `Ω[k[X]⁄k]` over `k[X]` is `1` whenever `k` is nontrivial. -/
theorem kaehlerDifferential_polynomial_rank [Nontrivial k] :
    Module.finrank (Polynomial k) (Ω[Polynomial k⁄k]) = 1 := by
  have := (KaehlerDifferential.polynomialEquiv k).finrank_eq
  rw [this, Module.finrank_self]

/-- Explicit formula for the universal derivation on polynomials: `dP = P' · dX`,
where `P'` is the usual formal derivative. -/
theorem kaehlerDifferential_polynomial_D (P : Polynomial k) :
    KaehlerDifferential.D k (Polynomial k) P =
      Polynomial.derivative P • KaehlerDifferential.D k (Polynomial k) Polynomial.X :=
  KaehlerDifferential.polynomial_D_apply k P

/-- For the polynomial ring `k[Xᵢ : i ∈ σ]`, the module `Ω[k[σ]⁄k]` is free as a
`k[σ]`-module, with basis `{dXᵢ}`. -/
theorem kaehlerDifferential_mvPolynomial_free (σ : Type*) :
    Module.Free (MvPolynomial σ k) (Ω[MvPolynomial σ k⁄k]) :=
  inferInstance

/-- Canonical basis `{dXᵢ}ᵢ` of `Ω[k[σ]⁄k]` as a free `k[σ]`-module indexed by `σ`. -/
def kaehlerDifferential_mvPolynomial_basis (σ : Type*) :
    Basis σ (MvPolynomial σ k) (Ω[MvPolynomial σ k⁄k]) :=
  KaehlerDifferential.mvPolynomialBasis k σ

end PolynomialDifferentials

section CotangentExactSequence

variable (R : Type u) [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Exactness of the relative cotangent sequence: `B ⊗_A Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0`
is exact at the middle term. -/
theorem cotangentSequence_exact :
    Function.Exact
      (KaehlerDifferential.mapBaseChange R A B)
      (KaehlerDifferential.map R A B B) :=
  KaehlerDifferential.exact_mapBaseChange_map R A B

/-- Surjectivity in the relative cotangent sequence: the map `Ω[B⁄R] → Ω[B⁄A]` is surjective. -/
theorem cotangentSequence_surjective :
    Function.Surjective (KaehlerDifferential.map R A B B) :=
  KaehlerDifferential.map_surjective R A B

/-- Conormal/cotangent exactness for a surjection `A → B` with kernel `I`: the sequence
`I/I² → B ⊗_A Ω[A⁄R] → Ω[B⁄R]` is exact at the middle term. -/
theorem cotangentExactSequence_with_kernel
    (h : Function.Surjective (algebraMap A B)) :
    Function.Exact
      (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h

/-- For a surjection `A → B`, the base-change map `B ⊗_A Ω[A⁄R] → Ω[B⁄R]` is itself
surjective. -/
theorem cotangent_mapBaseChange_surjective
    (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.mapBaseChange_surjective R A B h

/-- Proposition 33 (first half): for a surjection `A ↠ B` with kernel `I`, the conormal
sequence `I/I² → B ⊗_A Ω[A⁄R] → Ω[B⁄R] → 0` is exact and the right map is surjective. -/
theorem proposition33_cotangent_exact_sequence
    (h : Function.Surjective (algebraMap A B)) :
    Function.Exact
      (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) ∧
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
  ⟨KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h,
   KaehlerDifferential.mapBaseChange_surjective R A B h⟩

/-- Proposition 33 (second half): if both `R → A` and `R → B` are formally smooth and
`A ↠ B` is surjective, then the conormal sequence
`0 → I/I² → B ⊗_A Ω[A⁄R] → Ω[B⁄R] → 0` is short exact. -/
theorem proposition33_part2_short_exact
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R B]
    (h : Function.Surjective (algebraMap A B)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor R A B) ∧
    Function.Exact
      (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) ∧
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) := by
  refine ⟨?_, KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h,
    KaehlerDifferential.mapBaseChange_surjective R A B h⟩
  rw [Algebra.FormallySmooth.kerCotangentToTensor_injective_iff h]
  infer_instance


end CotangentExactSequence

section CotangentSpace

/-- For a Noetherian ring `R`, the cotangent module `I/I²` of any ideal `I` is finitely
generated over `R`. -/
theorem cotangent_finite_over_R {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : Module.Finite R I.Cotangent :=
  Module.Finite.quotient _ _

/-- For a Noetherian local ring `R` with maximal ideal `𝔪` and residue field `κ`, the
Zariski cotangent space `𝔪/𝔪²` is a finite-dimensional `κ`-vector space. -/
theorem cotangentSpace_finiteDimensional
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    FiniteDimensional (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
  inferInstance

/-- The cotangent space `𝔪/𝔪²` of a Noetherian local ring vanishes if and only if the
ring is a field. -/
theorem cotangentSpace_zero_iff_field
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Subsingleton (IsLocalRing.CotangentSpace R) ↔ IsField R :=
  IsLocalRing.subsingleton_cotangentSpace_iff

/-- Numerical version: `dim_κ (𝔪/𝔪²) = 0` iff `R` is a field. -/
theorem finrank_cotangentSpace_eq_zero_iff
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 0 ↔
      IsField R :=
  IsLocalRing.finrank_cotangentSpace_eq_zero_iff

/-- The cotangent space has dimension at most one iff the maximal ideal is principal
(equivalently, `R` is a DVR or a field). -/
theorem cotangentSpace_dim_le_one_iff_principal
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) ≤ 1 ↔
      (IsLocalRing.maximalIdeal R).IsPrincipal :=
  IsLocalRing.finrank_cotangentSpace_le_one_iff

end CotangentSpace

section Smoothness

/-- Nakayama-type criterion: a set `s ⊂ 𝔪` generates `𝔪` over `R` iff its image in
`𝔪/𝔪²` spans the cotangent space over the residue field. -/
theorem cotangentSpace_generators_iff_ideal_generators
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (s : Set (IsLocalRing.maximalIdeal R)) :
    Submodule.span (IsLocalRing.ResidueField R)
      ((IsLocalRing.maximalIdeal R).toCotangent '' s) = ⊤ ↔
    Submodule.span R s = ⊤ :=
  IsLocalRing.CotangentSpace.span_image_eq_top_iff

/-- Submodule version of Nakayama: a submodule `M ≤ 𝔪` equals all of `𝔪` iff its image
in the cotangent space is the whole space. -/
theorem cotangentSpace_map_eq_top_iff
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Submodule R (IsLocalRing.maximalIdeal R)} :
    M.map (IsLocalRing.maximalIdeal R).toCotangent = ⊤ ↔ M = ⊤ :=
  IsLocalRing.CotangentSpace.map_eq_top_iff

end Smoothness

end
