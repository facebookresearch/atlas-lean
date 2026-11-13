/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.Topology.KrullDimension

set_option maxHeartbeats 400000

noncomputable section

open Set

/-- A topological space has the *proper closed finite* property if every proper closed subset
is finite (characteristic of a one-dimensional space such as an irreducible curve). -/
def ProperClosedFinite (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ s : Set X, IsClosed s → s ≠ Set.univ → s.Finite

/-- Any injective map from a `T1` space to a space whose proper closed subsets are finite is
automatically continuous. -/
theorem continuous_of_injective_of_T1_properClosedFinite
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] (hY : ProperClosedFinite Y)
    {f : X → Y} (hf_inj : Function.Injective f) :
    Continuous f := by
  rw [continuous_def]
  intro U hU
  by_cases hUe : U = ∅
  · simp [hUe]
  · have hUc_ne : Uᶜ ≠ Set.univ := by
      intro h; apply hUe; simp at h; exact h
    have hUc_finite : Uᶜ.Finite := hY Uᶜ hU.isClosed_compl hUc_ne
    have hpre_finite : (f ⁻¹' Uᶜ).Finite := hUc_finite.preimage hf_inj.injOn
    rw [Set.preimage_compl] at hpre_finite
    have hclosed : IsClosed (f ⁻¹' U)ᶜ := hpre_finite.isClosed
    have := hclosed.isOpen_compl
    simp at this
    exact this

/-- Promote an equivalence between two `T1` spaces with the proper-closed-finite property to a
homeomorphism. -/
def Homeomorph.ofEquivProperClosedFinite
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] [T1Space Y]
    (hX : ProperClosedFinite X) (hY : ProperClosedFinite Y)
    (e : X ≃ Y) : X ≃ₜ Y :=
  { toEquiv := e
    continuous_toFun := continuous_of_injective_of_T1_properClosedFinite hY e.injective
    continuous_invFun := continuous_of_injective_of_T1_properClosedFinite hX e.symm.injective }

universe u

/-- Lecture 5, Proposition 6 (irreducible curves are homeomorphic): any two `T1` spaces with the
proper-closed-finite property and equal cardinality are homeomorphic. -/
theorem irreducible_curves_homeomorphic
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] [T1Space Y]
    (hX : ProperClosedFinite X) (hY : ProperClosedFinite Y)
    (hcard : Cardinal.mk X = Cardinal.mk Y) :
    Nonempty (X ≃ₜ Y) := by
  rw [Cardinal.eq] at hcard
  obtain ⟨e⟩ := hcard
  exact ⟨Homeomorph.ofEquivProperClosedFinite hX hY e⟩

/-- In `WithBot ℕ∞`, `x + 1 ≤ 1` implies `x ≤ 0`. -/
lemma WithBot.le_zero_of_add_one_le_one (x : WithBot ℕ∞) (h : x + 1 ≤ 1) : x ≤ 0 := by
  match x, h with
  | ⊥, _ => exact bot_le
  | (y : ℕ∞), h =>
    show (↑y : WithBot ℕ∞) ≤ ↑(0 : ℕ∞); rw [WithBot.coe_le_coe]
    match y with
    | ⊤ =>
      exfalso
      have h1 : (↑(⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ↑(⊤ : ℕ∞) := by
        show (↑(⊤ : ℕ∞) : WithBot ℕ∞) + ↑(1 : ℕ∞) = ↑(⊤ : ℕ∞)
        rw [← WithBot.coe_add]; simp
      rw [h1, show (1 : WithBot ℕ∞) = ↑((1 : ℕ) : ℕ∞) from rfl, WithBot.coe_le_coe] at h
      simp at h
    | (n : ℕ) =>
      show (↑n : ℕ∞) ≤ 0
      have hconv : (↑(↑n : ℕ∞) : WithBot ℕ∞) + 1 = ↑((↑(n + 1) : ℕ∞)) := by
        show (↑(↑n : ℕ∞) : WithBot ℕ∞) + ↑(1 : ℕ∞) = _; rw [← WithBot.coe_add]; norm_cast
      rw [hconv, show (1 : WithBot ℕ∞) = ↑((1 : ℕ) : ℕ∞) from rfl, WithBot.coe_le_coe] at h
      norm_cast at h ⊢; omega

/-- For a Noetherian domain of Krull dimension at most 1, every quotient by a nonzero ideal is
Artinian. -/
theorem isArtinianRing_quotient_of_dim_le_one {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hdim : ringKrullDim A ≤ 1)
    (I : Ideal A) (hI : I ≠ ⊥) :
    IsArtinianRing (A ⧸ I) := by

  have ⟨g, hgI, hg0⟩ : ∃ g ∈ I, g ≠ (0 : A) := by
    by_contra h; push Not at h; apply hI
    ext x; simp; exact ⟨h x, fun hx => hx ▸ I.zero_mem⟩

  have h2 : ringKrullDim (A ⧸ Ideal.span {g}) ≤ 0 :=
    WithBot.le_zero_of_add_one_le_one _
      (le_trans (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
        (mem_nonZeroDivisors_of_ne_zero hg0)) hdim)

  have hgI' : Ideal.span {g} ≤ I := by rwa [Ideal.span_le, Set.singleton_subset_iff]
  haveI : Ring.KrullDimLE 0 (A ⧸ I) := ⟨le_trans (ringKrullDim_le_of_surjective
    (Ideal.Quotient.factor hgI') (Ideal.Quotient.factor_surjective hgI')) h2⟩

  haveI : IsNoetherianRing (A ⧸ I) := Ideal.Quotient.isNoetherianRing I
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- In a Noetherian domain of Krull dimension at most 1, the zero locus of any nonzero ideal is
finite. -/
theorem zeroLocus_finite_of_dim_le_one {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hdim : ringKrullDim A ≤ 1)
    (I : Ideal A) (hI : I ≠ ⊥) :
    (PrimeSpectrum.zeroLocus (I : Set A)).Finite := by
  haveI := isArtinianRing_quotient_of_dim_le_one hdim I hI
  haveI : Finite (PrimeSpectrum (A ⧸ I)) := IsArtinianRing.instFinitePrimeSpectrum _
  have : Finite ↥(PrimeSpectrum.zeroLocus (I : Set A)) :=
    Finite.of_equiv _ (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).toEquiv
  exact Set.toFinite _

/-- The prime spectrum of a Noetherian domain of Krull dimension at most 1 satisfies the
proper-closed-finite property: every proper closed subset is finite. -/
theorem properClosedFinite_primeSpectrum_of_dim_le_one
    {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hdim : ringKrullDim A ≤ 1) :
    ProperClosedFinite (PrimeSpectrum A) := by
  intro S hS hne

  have hS_eq : S = PrimeSpectrum.zeroLocus ↑(PrimeSpectrum.vanishingIdeal S) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hS.closure_eq]

  have hI_ne : PrimeSpectrum.vanishingIdeal S ≠ ⊥ := by
    intro h; apply hne; rw [hS_eq, h, PrimeSpectrum.zeroLocus_bot]

  rw [hS_eq]
  exact zeroLocus_finite_of_dim_le_one hdim _ hI_ne

end
