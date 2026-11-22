/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

open Polynomial

namespace Lec9Blowups

/-- The blowup (Rees) algebra `⨁_{n ≥ 0} 𝔪ⁿ tⁿ ⊆ A[t]` of the ideal
`𝔪 ⊆ A` (Lec 9, Def 20). -/
def blowupAlgebra (A : Type*) [CommRing A] (𝔪 : Ideal A) : Subalgebra A A[X] :=
  reesAlgebra 𝔪

/-- A monomial `a · tⁿ` lies in the blowup algebra of `𝔪` iff
`a ∈ 𝔪ⁿ`. -/
theorem blowupAlgebra.monomial_mem {A : Type*} [CommRing A] {𝔪 : Ideal A}
    {n : ℕ} {a : A} :
    monomial n a ∈ blowupAlgebra A 𝔪 ↔ a ∈ 𝔪 ^ n :=
  reesAlgebra.monomial_mem

/-- A polynomial lies in the blowup algebra of `𝔪` iff each of its
coefficients lies in the corresponding power of `𝔪`. -/
theorem mem_blowupAlgebra_iff {A : Type*} [CommRing A] {𝔪 : Ideal A}
    (f : A[X]) :
    f ∈ blowupAlgebra A 𝔪 ↔ ∀ i, f.coeff i ∈ 𝔪 ^ i :=
  mem_reesAlgebra_iff (I := 𝔪) f

/-- A ring map `φ : R → A` carries the blowup algebra of `φ⁻¹(𝔪)` into
the blowup algebra of `𝔪`. -/
theorem map_mem_blowupAlgebra {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (𝔪 : Ideal A) (f : R[X]) (hf : f ∈ blowupAlgebra R (𝔪.comap φ)) :
    f.map φ ∈ blowupAlgebra A 𝔪 := by
  rw [mem_blowupAlgebra_iff] at hf ⊢
  intro i
  simp only [coeff_map]
  exact Ideal.le_comap_pow φ i (hf i)

/-- The induced ring map between blowup algebras coming from
`φ : R → A`. -/
noncomputable def blowupMapRestrict {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (𝔪 : Ideal A) :
    blowupAlgebra R (𝔪.comap φ) →+* blowupAlgebra A 𝔪 :=
  (Polynomial.mapRingHom φ).restrict (blowupAlgebra R (𝔪.comap φ)) (blowupAlgebra A 𝔪)
    (fun f hf => map_mem_blowupAlgebra φ 𝔪 f hf)

/-- The induced map between blowup algebras is the polynomial map of
`φ` applied to representatives. -/
theorem blowupMapRestrict_val {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (𝔪 : Ideal A) (f : blowupAlgebra R (𝔪.comap φ)) :
    ((blowupMapRestrict φ 𝔪) f).val = Polynomial.map φ f.val := by
  simp [blowupMapRestrict, RingHom.restrict]

/-- If `φ : R → A` is surjective, the induced map on blowup algebras is
surjective. -/
theorem blowupMapRestrict_surjective {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : Function.Surjective φ) (𝔪 : Ideal A) :
    Function.Surjective (blowupMapRestrict φ 𝔪) := by
  intro ⟨g, hg⟩
  rw [mem_blowupAlgebra_iff] at hg
  classical

  have lift : ∀ i ∈ g.support, ∃ r ∈ (𝔪.comap φ) ^ i, φ r = g.coeff i := by
    intro i _
    have h2 : g.coeff i ∈ Ideal.map φ ((𝔪.comap φ) ^ i) := by
      rw [Ideal.map_pow, Ideal.map_comap_of_surjective φ hφ]
      exact hg i
    exact (Ideal.mem_map_iff_of_surjective φ hφ).mp h2
  choose r hr hrφ using lift

  set f := g.support.sum fun i =>
    monomial i (if hi : i ∈ g.support then r i hi else 0)
  have hf : f ∈ blowupAlgebra R (𝔪.comap φ) := by
    apply Subalgebra.sum_mem
    intro i hi
    simp only [hi, dite_true]
    exact blowupAlgebra.monomial_mem.mpr (hr i hi)
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  show (Polynomial.map φ f) = g
  rw [Polynomial.map_sum]
  conv_rhs => rw [g.as_sum_support]
  apply Finset.sum_congr rfl
  intro i hi
  simp [hi, map_monomial, hrφ i hi]

/-- For a surjection `φ : R → A`, the blowup algebra of `𝔪` in `A` is
isomorphic to the blowup algebra of `φ⁻¹(𝔪)` in `R` modulo the kernel
of the induced map. -/
noncomputable def blowupQuotientEquiv {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : Function.Surjective φ) (𝔪 : Ideal A) :
    (blowupAlgebra R (𝔪.comap φ)) ⧸ RingHom.ker (blowupMapRestrict φ 𝔪)
      ≃+* blowupAlgebra A 𝔪 :=
  RingHom.quotientKerEquivOfSurjective (blowupMapRestrict_surjective φ hφ 𝔪)

/-- Lec 9, Prop 13: the blowup of `A` along `𝔪` is independent of the
chosen surjective presentation of `A`. -/
noncomputable def blowup_independent_of_embedding
    {R₁ R₂ A : Type*} [CommRing R₁] [CommRing R₂] [CommRing A]
    (φ₁ : R₁ →+* A) (hφ₁ : Function.Surjective φ₁)
    (φ₂ : R₂ →+* A) (hφ₂ : Function.Surjective φ₂)
    (𝔪 : Ideal A) :
    (blowupAlgebra R₁ (𝔪.comap φ₁)) ⧸ RingHom.ker (blowupMapRestrict φ₁ 𝔪)
      ≃+*
    (blowupAlgebra R₂ (𝔪.comap φ₂)) ⧸ RingHom.ker (blowupMapRestrict φ₂ 𝔪) :=
  (blowupQuotientEquiv φ₁ hφ₁ 𝔪).trans (blowupQuotientEquiv φ₂ hφ₂ 𝔪).symm

/-- Lec 9, Prop 13 (intrinsic blowup): the blowup at a maximal ideal of
a `k`-algebra `A` is independent of the chosen surjective presentation
by a `k`-algebra `R`. -/
noncomputable def blowup_intrinsic
    (k : Type*) [Field k]
    {R₁ R₂ A : Type*} [CommRing R₁] [CommRing R₂] [CommRing A]
    [Algebra k A] [Algebra k R₁] [Algebra k R₂]
    (φ₁ : R₁ →+* A) (hφ₁ : Function.Surjective φ₁)
    (φ₂ : R₂ →+* A) (hφ₂ : Function.Surjective φ₂)
    (𝔪 : Ideal A) (_h𝔪 : 𝔪.IsMaximal) :
    (blowupAlgebra R₁ (𝔪.comap φ₁)) ⧸ RingHom.ker (blowupMapRestrict φ₁ 𝔪)
      ≃+*
    (blowupAlgebra R₂ (𝔪.comap φ₂)) ⧸ RingHom.ker (blowupMapRestrict φ₂ 𝔪) :=
  blowup_independent_of_embedding φ₁ hφ₁ φ₂ hφ₂ 𝔪

/-- The intrinsic blowup of `A` at a maximal ideal `𝔪` is naturally
isomorphic to the blowup of any `k`-algebra presentation. -/
noncomputable def blowup_intrinsic_equiv
    (k : Type*) [Field k]
    {R A : Type*} [CommRing R] [CommRing A]
    [Algebra k A] [Algebra k R]
    (φ : R →+* A) (hφ : Function.Surjective φ)
    (𝔪 : Ideal A) (_h𝔪 : 𝔪.IsMaximal) :
    (blowupAlgebra R (𝔪.comap φ)) ⧸ RingHom.ker (blowupMapRestrict φ 𝔪)
      ≃+* blowupAlgebra A 𝔪 :=
  blowupQuotientEquiv φ hφ 𝔪

end Lec9Blowups
