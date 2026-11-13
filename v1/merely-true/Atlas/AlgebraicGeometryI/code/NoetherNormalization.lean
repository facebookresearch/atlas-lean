/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.DimensionProduct
import Atlas.AlgebraicGeometryI.code.NakayamaApplications
import Atlas.AlgebraicGeometryI.code.Lec2AlgebraicVariety

set_option maxHeartbeats 800000

noncomputable section

open MvPolynomial PrimeSpectrum

section NoetherNormalization

variable (k : Type*) [Field k] (A : Type*) [CommRing A] [Nontrivial A]
  [Algebra k A] [Algebra.FiniteType k A]

/-- Noether normalization (integral form): a finitely generated k-algebra A contains a
polynomial subring k[x_1,...,x_d] over which A is integral (Lemma 1, Lecture 2). -/
theorem noether_normalization_integral :
    ∃ d : ℕ, ∃ g : MvPolynomial (Fin d) k →ₐ[k] A,
      Function.Injective g ∧ g.IsIntegral :=
  exists_integral_inj_algHom_of_fg k A

/-- Noether normalization (module-finite form): A is a finitely generated module over
some polynomial subring k[x_1,...,x_d] (Theorem 3.2, Lecture 3). -/
theorem noether_normalization_finite :
    ∃ d : ℕ, ∃ g : MvPolynomial (Fin d) k →ₐ[k] A,
      Function.Injective g ∧ g.Finite :=
  exists_finite_inj_algHom_of_fg k A

/-- Geometric form of Noether normalization: the induced map on spectra
Spec A → Spec k[x_1,...,x_d] is surjective. -/
theorem noether_normalization_spec_surjective :
    ∃ d : ℕ, ∃ g : MvPolynomial (Fin d) k →ₐ[k] A,
      Function.Injective g ∧ g.Finite ∧
      Function.Surjective (PrimeSpectrum.comap g.toRingHom) := by
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  refine ⟨d, g, hinj, hfin, ?_⟩

  have hfin_rh : g.toRingHom.Finite := hfin
  have hint : g.toRingHom.IsIntegral := RingHom.IsIntegral.of_finite hfin_rh

  exact hint.comap_surjective hinj

end NoetherNormalization

section ZariskiLemma

/-- Zariski's lemma via Noether normalization: any finitely generated k-algebra that
is a field must be algebraic over k. -/
theorem noether_normalization_implies_zariski_lemma
    (k A : Type*) [Field k] [Field A] [Algebra k A]
    [Algebra.FiniteType k A] : Algebra.IsAlgebraic k A :=
  essential_nullstellensatz k A

/-- Strengthened Zariski lemma: a finitely generated k-algebra which is a field is in
fact finite-dimensional as a k-vector space. -/
theorem zariski_lemma_module_finite
    (k A : Type*) [Field k] [Field A] [Algebra k A]
    [Algebra.FiniteType k A] : Module.Finite k A :=
  finite_of_finiteType_field k A

end ZariskiLemma

section Dimension

/-- Noether normalization computes the Krull dimension: the integer d such that A is
module-finite over k[x_1,...,x_d] equals dim A. -/
theorem noether_normalization_dimension
    (k : Type*) [Field k] (A : Type*) [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ d : ℕ, ∃ g : MvPolynomial (Fin d) k →ₐ[k] A,
      Function.Injective g ∧ g.Finite ∧ ringKrullDim A = ↑d := by
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  exact ⟨d, g, hinj, hfin, ringKrullDim_eq_of_noetherNormalization d g hinj hfin⟩

/-- The Krull dimension of any finitely generated algebra over a field is a natural
number (finite and non-negative). -/
theorem noether_normalization_dim_is_nat
    (k : Type*) [Field k] (A : Type*) [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ d : ℕ, ringKrullDim A = ↑d :=
  ringKrullDim_fg_algebra_eq_nat k A

/-- A finite injective ring extension preserves Krull dimension: going-up and
incomparability give matching prime chains in A and B. -/
theorem dim_preserved_by_finite_injective
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    [Module.Finite B A]
    (hinj : Function.Injective (algebraMap B A)) :
    ringKrullDim A = ringKrullDim B :=
  FiniteMorphismDimension.ringKrullDim_eq_of_injective_finite hinj

end Dimension

section Quotient

/-- Noether normalization for quotients of polynomial rings: for a proper ideal I in
k[x_1,...,x_n], the quotient is integral over some k[y_1,...,y_s] with s ≤ n. -/
theorem noether_normalization_quotient {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    ∃ s, s ≤ n ∧ ∃ g : MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin n) k ⧸ I,
      Function.Injective g ∧ g.IsIntegral := by
  obtain ⟨s, hs, g, hinj, hint⟩ := exists_integral_inj_algHom_of_quotient I hI
  exact ⟨s, hs, g, hinj, hint⟩

end Quotient

section AlgebraicVarietyDimension

open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u


end AlgebraicVarietyDimension

end
