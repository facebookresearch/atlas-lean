/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.NoetherNormalization
import Atlas.AlgebraicGeometryI.code.NakayamaApplications
import Atlas.AlgebraicGeometryI.code.NoetherNullstellensatzChain
import Atlas.AlgebraicGeometryI.code.LinearChangeVariables
import Atlas.AlgebraicGeometryI.code.NoetherianTopological
import Atlas.AlgebraicGeometryI.code.Lec2AffineVarieties
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 800000


attribute [local instance] MvPolynomial.gradedAlgebra

open PrimeSpectrum TopologicalSpace AlgebraicGeometry

noncomputable section thm31_section

open CategoryTheory

universe v

/-- Lecture 3, Theorem 3.1: an algebraic variety `X` over an algebraically closed field `k` is
affine iff `X ≅ Spec A` for `A = Γ(X, O_X)`, and conversely `Spec A` is a variety whenever `A` is
a reduced finitely generated `k`-algebra. -/
theorem thm3_1_affine_iff_spec
    (k : Type v) [Field k] [IsAlgClosed k] :

    (∀ (X : Scheme.{v}) (f : X ⟶ Spec (CommRingCat.of k))
      [Definition3_AlgebraicVariety k X f] [IsAffine X],
      IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧

    (∀ (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A],
      Definition3_AlgebraicVariety k (Spec (CommRingCat.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
  thm31_affine_variety_characterization (k := k)

end thm31_section


/-- Lecture 3, Theorem 3.2 (Noether normalization): any finitely generated `k`-algebra `A` admits
an injective finite `k`-algebra map from a polynomial ring `k[x_1, …, x_d]`. -/
theorem thm3_2_noether_normalization
    (k : Type*) [Field k]
    (A : Type*) [CommRing A] [Nontrivial A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ∃ (d : ℕ) (g : MvPolynomial (Fin d) k →ₐ[k] A),
      Function.Injective g ∧ g.Finite :=
  noether_normalization_finite k A

/-- Lecture 3, Lemma 3 (linear change of variables): over an infinite field, any nonconstant
polynomial in `n + 1` variables can be transformed by an algebra automorphism so that, viewed as a
polynomial in `x_0` over `k[x_1, …, x_n]`, its leading coefficient is a unit. -/
theorem lemma3_linear_change_monic
    {k : Type*} [Field k] [Infinite k]
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) k)
    (hP : 0 < P.totalDegree) :
    ∃ (φ : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k),
      IsUnit (MvPolynomial.finSuccEquiv k n (φ P)).leadingCoeff :=
  MvPolynomial.exists_algEquiv_monic P hP

/-- Companion to Lemma 3: over an infinite field, any nonzero polynomial in finitely many
variables takes a nonzero value at some point. -/
theorem lemma3_nonzero_polynomial_takes_nonzero_values
    {k : Type*} [Field k] [Infinite k]
    {σ : Type*} [Fintype σ]
    {f : MvPolynomial σ k} (hf : f ≠ 0) :
    ∃ v : σ → k, MvPolynomial.eval v f ≠ 0 :=
  MvPolynomial.exists_eval_ne_zero hf

/-- Lecture 3, Proposition 2 (Hilbert basis theorem): polynomial rings in finitely many variables
over a field are Noetherian. -/
theorem prop2_hilbert_basis_theorem
    (k : Type*) [Field k] (n : ℕ) :
    IsNoetherianRing (MvPolynomial (Fin n) k) :=
  inferInstance

/-- Lecture 3, Lemma 4 (determinant form of Nakayama's lemma): if `I` is an ideal of `R` and `M`
is a finitely generated `R`-module with `IM = M`, then some `a ∈ R` with `a ≡ 1 mod I` annihilates
all of `M`. -/
theorem lemma4_nakayama
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hIM : I • (⊤ : Submodule R M) = ⊤) :
    ∃ a : R, a - 1 ∈ I ∧ ∀ m : M, a • m = 0 :=
  nakayama_determinant_form I hIM

/-- Lecture 3, Theorem 3.3 (essential Nullstellensatz): any field that is a finitely generated
algebra over a field `k` is algebraic over `k`. -/
theorem thm3_3_essential_nullstellensatz
    (k : Type*) [Field k]
    (A : Type*) [Field A] [Algebra k A] [Algebra.FiniteType k A] :
    Algebra.IsAlgebraic k A :=
  essential_nullstellensatz k A

/-- Lecture 3, Definition 7: a topological space is irreducible iff the whole space, viewed as a
subset, is irreducible. -/
theorem def7_irreducible_space_iff (X : Type*) [TopologicalSpace X] :
    IrreducibleSpace X ↔ IsIrreducible (Set.univ : Set X) :=
  irreducibleSpace_def X

/-- Equivalent form of Definition 7: an irreducible space cannot be written as a union of two
proper closed subsets. -/
theorem def7_irreducible_not_union_proper_closed (X : Type*) [TopologicalSpace X]
    [IrreducibleSpace X] (s t : Set X) (hs : IsClosed s) (ht : IsClosed t)
    (hst : s ∪ t = Set.univ) :
    s = Set.univ ∨ t = Set.univ := by
  have hirr := (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
  have hsub : Set.univ ⊆ s ∪ t := hst ▸ le_refl _
  rcases hirr s t hs ht hsub with h | h
  · left; exact Set.univ_subset_iff.mp h
  · right; exact Set.univ_subset_iff.mp h

/-- Lecture 3, Proposition 3: for a reduced ring `A`, the prime spectrum `Spec A` is irreducible
iff `A` is a domain. -/
theorem prop3_spec_irreducible_iff_domain
    (A : Type*) [CommRing A] [IsReduced A] :
    IrreducibleSpace (PrimeSpectrum A) ↔ IsDomain A := by
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  have hnil : nilradical A = ⊥ := nilradical_eq_zero A
  rw [hnil]
  exact ⟨fun _ => IsDomain.of_bot_isPrime A, fun _ => Ideal.isPrime_bot⟩

/-- Lecture 3, Definition 8: a subset is an irreducible component iff it is irreducible and
maximal among irreducible subsets. -/
theorem def8_component_characterization (X : Type*) [TopologicalSpace X]
    (s : Set X) :
    s ∈ irreducibleComponents X ↔
      IsIrreducible s ∧ ∀ t : Set X, IsIrreducible t → s ⊆ t → t ⊆ s := by
  simp only [irreducibleComponents, Set.mem_setOf_eq, Maximal]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun t ht hst => h2 ht hst⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun {t} ht hst => h2 t ht hst⟩

/-- Companion to Definition 8: every irreducible component is closed. -/
theorem def8_component_is_closed (X : Type*) [TopologicalSpace X]
    (s : Set X) (hs : s ∈ irreducibleComponents X) : IsClosed s :=
  isClosed_of_mem_irreducibleComponents s hs

/-- Lecture 3, Proposition 4: a Noetherian topological space has finitely many irreducible
components, whose union is the whole space. -/
theorem prop4_noetherian_finite_union_components
    (X : Type*) [TopologicalSpace X] [NoetherianSpace X] :
    Set.Finite (irreducibleComponents X) ∧
      ⋃₀ irreducibleComponents X = Set.univ := by
  refine ⟨NoetherianSpace.finite_irreducibleComponents, ?_⟩
  ext x
  simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
  exact ⟨irreducibleComponent x,
    irreducibleComponent_mem_irreducibleComponents x,
    mem_irreducibleComponent⟩

/-- Lecture 3, Corollary 5 (form 1): the zero locus of a radical ideal `I ⊆ A` is irreducible iff
`I` is prime. -/
theorem cor5_irreducible_closed_iff_prime
    (A : Type*) [CommRing A] (I : Ideal A) (hI : I.IsRadical) :
    IsIrreducible (PrimeSpectrum.zeroLocus (I : Set A)) ↔ I.IsPrime :=
  PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical I hI

/-- Corollary 5 (form 2): the vanishing-ideal map gives a bijection between closed irreducible
subsets of `Spec A` and prime ideals of `A`. -/
theorem cor5_closed_irreducible_eq_primes
    (A : Type*) [CommRing A] :
    PrimeSpectrum.vanishingIdeal '' {s : Set (PrimeSpectrum A) | IsClosed s ∧ IsIrreducible s} =
      {P : Ideal A | P.IsPrime} :=
  PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible

/-- Corollary 5 (form 3): under this bijection, irreducible components of `Spec A` correspond to
minimal primes of `A` when `A` is Noetherian. -/
theorem cor5_components_eq_minimal_primes
    (A : Type*) [CommRing A] [IsNoetherianRing A] :
    PrimeSpectrum.vanishingIdeal '' irreducibleComponents (PrimeSpectrum A) =
      minimalPrimes A :=
  PrimeSpectrum.vanishingIdeal_irreducibleComponents A

/-- Lecture 3, Corollary 6: in a reduced ring, the intersection of the minimal primes is zero. -/
theorem cor6_zero_eq_inf_minimal_primes
    (A : Type*) [CommRing A] [IsReduced A] :
    sInf (Ideal.minimalPrimes (⊥ : Ideal A)) = (⊥ : Ideal A) := by
  rw [Ideal.sInf_minimalPrimes]
  change nilradical A = ⊥
  exact nilradical_eq_zero A
