/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ValuativeCriterion

open Polynomial

noncomputable section

universe u v

/-- The coefficient of a finite sum of monomials indexed by a finset `s`: it equals
`g i` when `i ∈ s` and `0` otherwise. -/
lemma coeff_finset_sum_monomial {R : Type*} [CommRing R]
    {s : Finset ℕ} {g : ℕ → R} (i : ℕ) :
    (s.sum (fun j => Polynomial.monomial j (g j))).coeff i =
      if i ∈ s then g i else 0 := by
  change (Polynomial.lcoeff R i) (s.sum (fun j => Polynomial.monomial j (g j))) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial, Finset.sum_ite_eq']

namespace ChowBlowup

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A polynomial in the Rees algebra of `I` maps under a ring homomorphism `f` into the
Rees algebra of the pushed-forward ideal `I.map f`. -/
theorem mem_reesAlgebra_map (f : R →+* S) (I : Ideal R)
    (p : R[X]) (hp : p ∈ reesAlgebra I) :
    Polynomial.map f p ∈ reesAlgebra (I.map f) := by
  rw [mem_reesAlgebra_iff] at hp ⊢
  intro i
  rw [Polynomial.coeff_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem f (hp i)

/-- If `s` lies in `(I.map e)^i` for a ring isomorphism `e`, then `e.symm s` lies in `I^i`. -/
lemma symm_mem_ideal_pow_of_mem_map_pow (e : R ≃+* S) (I : Ideal R)
    (i : ℕ) (s : S) (h : s ∈ (I.map (e : R →+* S)) ^ i) :
    e.symm s ∈ I ^ i := by
  rw [← Ideal.map_pow (e : R →+* S)] at h
  rw [Ideal.mem_map_iff_of_surjective (e : R →+* S) e.surjective] at h
  obtain ⟨r, hr, hrs⟩ := h
  have : e.symm s = r := by rw [← hrs]; simp
  rw [this]; exact hr

/-- Pulling back along the inverse of a ring isomorphism preserves membership in the Rees algebra. -/
theorem mem_reesAlgebra_map_symm (e : R ≃+* S) (I : Ideal R)
    (q : S[X]) (hq : q ∈ reesAlgebra (I.map (e : R →+* S))) :
    Polynomial.map (e.symm : S →+* R) q ∈ reesAlgebra I := by
  rw [mem_reesAlgebra_iff] at hq ⊢
  intro i
  rw [Polynomial.coeff_map]
  exact symm_mem_ideal_pow_of_mem_map_pow e I i _ (hq i)

/-- A ring isomorphism `e : R ≃+* S` induces a ring isomorphism between the Rees algebra of `I`
and the Rees algebra of `I.map e`. -/
def reesAlgebra_ringEquiv (e : R ≃+* S) (I : Ideal R) :
    reesAlgebra I ≃+* reesAlgebra (I.map (e : R →+* S)) where
  toFun p := ⟨Polynomial.map (e : R →+* S) p.1,
    mem_reesAlgebra_map _ I p.1 p.2⟩
  invFun q := ⟨Polynomial.map (e.symm : S →+* R) q.1,
    mem_reesAlgebra_map_symm e I q.1 q.2⟩
  left_inv p := by ext; simp [Polynomial.map_map]
  right_inv q := by ext; simp [Polynomial.map_map]
  map_mul' p q := Subtype.ext (Polynomial.map_mul (e : R →+* S))
  map_add' p q := Subtype.ext (Polynomial.map_add (e : R →+* S))

/-- The ring homomorphism from the Rees algebra of `I.comap f` to the Rees algebra of `I`,
induced coefficient-wise by `f`. -/
def reesAlgebra_comap_to_rees {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal A) :
    reesAlgebra (I.comap f) →+* reesAlgebra I :=
  (Polynomial.mapRingHom f).restrict (reesAlgebra (I.comap f)) (reesAlgebra I)
    (fun p hp => by
      rw [mem_reesAlgebra_iff] at hp ⊢
      intro i; simp [coeff_map]; exact Ideal.le_comap_pow f i (hp i))

/-- If `f : R →+* A` is surjective, the induced map of Rees algebras is also surjective. -/
theorem reesAlgebra_comap_to_rees_surjective {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : Function.Surjective f) (I : Ideal A) :
    Function.Surjective (reesAlgebra_comap_to_rees f I) := by
  intro ⟨q, hq⟩
  rw [mem_reesAlgebra_iff] at hq
  classical
  have hlift : ∀ i, ∃ r ∈ (I.comap f) ^ i, f r = q.coeff i := by
    intro i
    have hi := hq i
    rw [← Ideal.map_comap_of_surjective f hf I, ← Ideal.map_pow] at hi
    exact (Ideal.mem_map_iff_of_surjective f hf).mp hi
  choose g hg_mem hg_eq using hlift
  set p := q.support.sum (fun i => Polynomial.monomial i (g i)) with hp_def
  have hp : p ∈ reesAlgebra (I.comap f) := by
    rw [mem_reesAlgebra_iff]
    intro i
    rw [hp_def, coeff_finset_sum_monomial]
    split_ifs with hi
    · exact hg_mem i
    · exact ((I.comap f) ^ i).zero_mem
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  show (Polynomial.map f p) = q
  ext i
  rw [coeff_map, hp_def, coeff_finset_sum_monomial]
  split_ifs with hi
  · exact hg_eq i
  · simp only [map_zero]
    have : q.coeff i = 0 := by rwa [Polynomial.mem_support_iff, not_not] at hi
    exact this.symm

/-- For a surjective ring map `f : R →+* A`, the Rees algebra of `I.comap f` modulo the kernel of the
induced map is isomorphic to the Rees algebra of `I`. -/
def reesAlgebra_quotient_equiv {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : Function.Surjective f) (I : Ideal A) :
    (reesAlgebra (I.comap f)) ⧸ RingHom.ker (reesAlgebra_comap_to_rees f I)
      ≃+* reesAlgebra I :=
  RingHom.quotientKerEquivOfSurjective (reesAlgebra_comap_to_rees_surjective f hf I)

/-- The blowup of `A` along `I` is intrinsic: any two surjective presentations of `A`
yield isomorphic Rees algebra quotients. -/
def blowup_intrinsic
    {R₁ R₂ A : Type*} [CommRing R₁] [CommRing R₂] [CommRing A]
    (f₁ : R₁ →+* A) (hf₁ : Function.Surjective f₁)
    (f₂ : R₂ →+* A) (hf₂ : Function.Surjective f₂)
    (I : Ideal A) :
    (reesAlgebra (I.comap f₁)) ⧸ RingHom.ker (reesAlgebra_comap_to_rees f₁ I)
      ≃+*
    (reesAlgebra (I.comap f₂)) ⧸ RingHom.ker (reesAlgebra_comap_to_rees f₂ I) :=
  (reesAlgebra_quotient_equiv f₁ hf₁ I).trans (reesAlgebra_quotient_equiv f₂ hf₂ I).symm

/-- Specialization of `blowup_intrinsic`: the Rees algebra blowup at a maximal ideal is intrinsic
relative to any surjective `k`-algebra presentation. -/
def blowup_intrinsic_equiv
    (k : Type*) [Field k]
    {R A : Type*} [CommRing R] [CommRing A]
    [Algebra k A] [Algebra k R]
    (f : R →+* A) (hf : Function.Surjective f)
    (𝔪 : Ideal A) (_h𝔪 : 𝔪.IsMaximal) :
    (reesAlgebra (𝔪.comap f)) ⧸ RingHom.ker (reesAlgebra_comap_to_rees f 𝔪)
      ≃+* reesAlgebra 𝔪 :=
  reesAlgebra_quotient_equiv f hf 𝔪

end ChowBlowup

section ReesProperties

variable {R : Type u} [CommRing R]

end ReesProperties

section ChowsLemma

variable {R : Type u} [CommRing R]

/-- The structure map `R → reesAlgebra I` (inclusion as constant polynomials) is injective. -/
theorem algebraMap_reesAlgebra_injective (I : Ideal R) :
    Function.Injective (algebraMap R (reesAlgebra I)) := by
  intro a b hab
  have h : (algebraMap R (reesAlgebra I) a).1 = (algebraMap R (reesAlgebra I) b).1 :=
    congrArg Subtype.val hab
  exact Polynomial.C_injective h

end ChowsLemma

section ChowStatement

end ChowStatement

section ChowsLemmaSchemeTheoretic

open AlgebraicGeometry CategoryTheory Limits

/-- Two schemes `X` and `Y` are birational if there exists a scheme `Z` with open immersions into
both that have dense image. -/
def IsBirational (X Y : Scheme.{u}) : Prop :=
  ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧
    Dense (Set.range f.base) ∧ Dense (Set.range g.base)

/-- A scheme is projective if it admits a closed immersion into some `Proj 𝒜` for a finitely
generated graded algebra `𝒜`. -/
def IsProjectiveScheme (X : Scheme.{u}) : Prop :=
  ∃ (σ : Type u) (A : Type u)
    (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A)
    (𝒜 : ℕ → σ) (_ : GradedRing 𝒜) (_ : Algebra.FiniteType (𝒜 0) A)
    (i : X ⟶ Proj 𝒜), IsClosedImmersion i








end ChowsLemmaSchemeTheoretic
