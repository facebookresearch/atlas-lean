/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

open MvPolynomial AlgebraicGeometry CategoryTheory

namespace Lec1ZariskiNullstellensatz

noncomputable section

/-- Theorem 1.1 (Lecture 1, essential Nullstellensatz). Any field extension `K/k` that is
finitely generated as a `k`-algebra is algebraic over `k`. -/
theorem thm1_1_essential_nullstellensatz
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.FiniteType k K] : Algebra.IsAlgebraic k K := by


  have : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K

  exact Algebra.IsAlgebraic.of_finite k K

/-- Algebraically closed form of Theorem 1.1: if `k = k̄` is algebraically closed and `K/k`
is a finitely generated `k`-algebra that is a field, then the structure map `k → K` is
bijective, i.e. `K = k`. -/
theorem thm1_1_essential_nullstellensatz_algClosed
    (k K : Type*) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    [Algebra.FiniteType k K] : Function.Bijective (algebraMap k K) := by
  have : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  have : Algebra.IsIntegral k K := Algebra.IsAlgebraic.isIntegral
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Definition 1 (Lecture 1). A subset `V ⊆ k^σ` is Zariski closed if it is the zero set
of some collection of polynomials in `k[x_σ]`. -/
def IsZariskiClosed (k : Type*) [Field k] (σ : Type*) (V : Set (σ → k)) : Prop :=
  ∃ S : Set (MvPolynomial σ k), V = {x | ∀ f ∈ S, MvPolynomial.aeval x f = 0}

/-- A subset is Zariski closed iff it is the zero locus of some ideal of polynomials;
equivalence between cutting out by a set of polynomials and by the ideal it generates. -/
theorem isZariskiClosed_iff_exists_ideal (k : Type*) [Field k] (σ : Type*)
    (V : Set (σ → k)) :
    IsZariskiClosed k σ V ↔
      ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I := by
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨Ideal.span S, (MvPolynomial.zeroLocus_span S).symm⟩
  · rintro ⟨I, rfl⟩
    exact ⟨I, rfl⟩

/-- The vanishing ideal `I(V)` of any subset of affine space is a radical ideal. -/
lemma vanishingIdeal_isRadical (k : Type*) [Field k] (σ : Type*) (V : Set (σ → k)) :
    (MvPolynomial.vanishingIdeal k V).IsRadical := by
  intro f hf
  rw [Ideal.mem_radical_iff] at hf
  obtain ⟨n, hn⟩ := hf
  intro x hx
  have h := hn x hx
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

/-- An ideal and its radical have the same zero locus: `V(I) = V(√I)`. -/
theorem zeroLocus_radical_eq (k : Type*) [Field k] (σ : Type*)
    (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.zeroLocus k I.radical = MvPolynomial.zeroLocus k I := by
  apply le_antisymm
  · exact MvPolynomial.zeroLocus_anti_mono Ideal.le_radical
  · intro x hx p hp
    rw [Ideal.mem_radical_iff] at hp
    obtain ⟨n, hn⟩ := hp
    have := hx _ hn
    rw [map_pow] at this
    exact eq_zero_of_pow_eq_zero this

/-- Hilbert's Nullstellensatz (over an algebraically closed field): `I(V(I)) = √I`. -/
theorem nullstellensatz_correspondence_eq_radical
    (k : Type*) [Field k] [IsAlgClosed k] (σ : Type*) [Finite σ]
    (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = I.radical :=
  MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I

/-- For a radical ideal `I` over `k̄`, we have `I(V(I)) = I`: passing to the zero locus and
back recovers a radical ideal. -/
theorem nullstellensatz_radical_inverse
    (k : Type*) [Field k] [IsAlgClosed k] (σ : Type*) [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsRadical) :
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = I := by
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hI.radical]

/-- For any ideal `I` over `k̄`, the iterated operation `V(I(V(I)))` recovers `V(I)`. -/
theorem nullstellensatz_closed_inverse
    (k : Type*) [Field k] [IsAlgClosed k] (σ : Type*) [Finite σ]
    (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.zeroLocus k
      (MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I)) =
      MvPolynomial.zeroLocus k I := by
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I, zeroLocus_radical_eq]

/-- Theorem 1.2 (Lecture 1). Over an algebraically closed field with finitely many variables,
there is a bijection between radical ideals of `k[x_σ]` and Zariski-closed subsets of `k^σ`,
given by `I ↦ V(I)` with inverse `V ↦ I(V)`. -/
noncomputable def nullstellensatz_bijection
    (k : Type*) [Field k] [IsAlgClosed k] (σ : Type*) [Finite σ] :
    {I : Ideal (MvPolynomial σ k) // I.IsRadical} ≃
      {V : Set (σ → k) // ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I} := by
  refine ⟨
    fun ⟨I, _⟩ => ⟨MvPolynomial.zeroLocus k I, ⟨I, rfl⟩⟩,
    fun ⟨V, _⟩ => ⟨MvPolynomial.vanishingIdeal k V, vanishingIdeal_isRadical k σ V⟩,
    ?_, ?_⟩
  ·
    rintro ⟨I, hI⟩
    exact Subtype.ext
      ((MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I).trans hI.radical)
  ·
    rintro ⟨V, I, rfl⟩
    apply Subtype.ext
    show MvPolynomial.zeroLocus k
      (MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I)) =
      MvPolynomial.zeroLocus k I
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I, zeroLocus_radical_eq]

/-- The classical Zariski topology on affine space `k^σ`: closed sets are the zero loci of
ideals in `k[x_σ]`. -/
noncomputable instance zariskiTopology_classical
    (k : Type*) [Field k] (σ : Type*) [Fintype σ] :
    TopologicalSpace (σ → k) :=
  TopologicalSpace.ofClosed
    {V | ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I}
    ⟨⊤, MvPolynomial.zeroLocus_top.symm⟩
    (fun A hA => by

      have hchoice : ∀ V ∈ A, ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I :=
        fun V hV => hA hV
      let idealOf : (V : Set (σ → k)) → (V ∈ A) → Ideal (MvPolynomial σ k) :=
        fun V hV => Classical.choose (hchoice V hV)
      have hidealOf : ∀ V (hV : V ∈ A), V = MvPolynomial.zeroLocus k (idealOf V hV) :=
        fun V hV => Classical.choose_spec (hchoice V hV)
      refine ⟨⨆ (p : A), idealOf p.val p.prop, ?_⟩
      ext x
      simp only [Set.mem_sInter, MvPolynomial.mem_zeroLocus_iff]
      constructor
      · intro h f hf
        refine Submodule.iSup_induction (motive := fun g => (MvPolynomial.aeval x) g = 0) _ hf
          (fun ⟨V, hV⟩ g hg => ?_) (map_zero _) (fun a b ha hb => ?_)
        · have hxV : x ∈ V := h V hV
          rw [hidealOf V hV] at hxV
          exact hxV g hg
        · change (MvPolynomial.aeval x) a = 0 at ha
          change (MvPolynomial.aeval x) b = 0 at hb
          show (MvPolynomial.aeval x) (a + b) = 0
          rw [map_add, ha, hb, add_zero]
      · intro h V hV
        rw [hidealOf V hV]
        intro f hf
        exact h f (le_iSup (fun (p : A) => idealOf p.val p.prop) ⟨V, hV⟩ hf))
    (fun A ⟨I, hI⟩ B ⟨J, hJ⟩ => by

      refine ⟨I ⊓ J, ?_⟩
      subst hI; subst hJ
      ext x
      simp only [Set.mem_union, MvPolynomial.mem_zeroLocus_iff, Ideal.mem_inf]
      constructor
      · rintro (hI | hJ) f ⟨hfI, hfJ⟩
        · exact hI f hfI
        · exact hJ f hfJ
      · intro h
        by_contra hc
        push Not at hc
        obtain ⟨⟨f, hfI, hf⟩, ⟨g, hgJ, hg⟩⟩ := hc
        have hfg := h (f * g) ⟨I.mul_mem_right g hfI, J.mul_mem_left f hgJ⟩
        rw [map_mul] at hfg
        exact (mul_ne_zero hf hg) hfg)

/-- Closed sets in the classical Zariski topology on `k^σ` are exactly the Zariski-closed
subsets in the polynomial-zero-set sense. -/
theorem zariskiTopology_isClosed_iff
    (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    (Z : Set (σ → k)) :
    @IsClosed _ (zariskiTopology_classical k σ) Z ↔ IsZariskiClosed k σ Z := by
  constructor
  · intro hZ
    have hopen := hZ.isOpen_compl
    change Zᶜᶜ ∈ {V | ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I} at hopen
    rw [compl_compl] at hopen
    obtain ⟨I, rfl⟩ := hopen
    exact ⟨I, rfl⟩
  · intro ⟨S, hS⟩
    constructor
    show Zᶜᶜ ∈ {V | ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I}
    rw [compl_compl]
    exact ⟨Ideal.span S, by rw [hS, MvPolynomial.zeroLocus_span]⟩

/-- The Yoneda-style pullback sending a scheme morphism `X → Spec A` to the induced ring map
`A → Γ(X, 𝒪_X)`. -/
def yonedaPullback (A : CommRingCat) (X : Scheme) :
    (X ⟶ Spec A) → (A ⟶ Γ(X, ⊤)) :=
  fun f => ((ΓSpec.adjunction.homEquiv X (Opposite.op A)).symm.trans (opEquiv _ _)) f

/-- A bundling of the affine variety condition: `A` is a finite-type `k`-algebra and `Spec A`
represents the functor `X ↦ Hom_{Ring}(A, Γ(X, 𝒪_X))`. -/
structure IsAffineVariety' (k : Type*) [Field k] (A : Type*) [CommRing A] [Algebra k A] : Prop where
  finiteType : Algebra.FiniteType k A
  yoneda_bijective : ∀ (X : Scheme), Function.Bijective (yonedaPullback (CommRingCat.of A) X)

/-- The fundamental Spec-Γ adjunction packaged as a bijection: scheme morphisms
`X → Spec A` correspond to ring maps `A → Γ(X, 𝒪_X)`. -/
noncomputable def affine_variety_yoneda
    (A : CommRingCat) (X : Scheme) :
    (X ⟶ Spec A) ≃ (A ⟶ Γ(X, ⊤)) :=
  (ΓSpec.adjunction.homEquiv X (Opposite.op A)).symm.trans (opEquiv _ _)

/-- Any finitely generated `k`-algebra `A` defines an affine variety in the sense of
`IsAffineVariety'`: `Spec A` represents Hom from `A`. -/
theorem isAffineVariety_of_finiteType (k : Type*) [Field k] (A : Type*) [CommRing A] [Algebra k A]
    (hfin : Algebra.FiniteType k A) : IsAffineVariety' k A where
  finiteType := hfin
  yoneda_bijective := fun X => Equiv.bijective (affine_variety_yoneda (CommRingCat.of A) X)

/-- `Spec A` is an affine scheme. -/
instance spec_isAffine (A : CommRingCat) : IsAffine (Spec A) :=
  AlgebraicGeometry.isAffine_Spec A
end

end Lec1ZariskiNullstellensatz
