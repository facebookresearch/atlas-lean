/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.IntersectionDimension
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Localization.Away.Basic

set_option maxHeartbeats 800000

noncomputable section
open Ideal

/-- Cutting by a nonzero element drops the Krull dimension by at least one:
`dim(A/(g)) + 1 ≤ dim A` for a nonzero `g` in a domain. -/
theorem ringKrullDim_quotient_span_succ_le_of_domain {A : Type*} [CommRing A] [IsDomain A]
    (g : A) (hg : g ≠ 0) :
    ringKrullDim (A ⧸ Ideal.span {g}) + 1 ≤ ringKrullDim A :=
  ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hg)

/-- Localizing away from `f` can only decrease the Krull dimension:
`dim A[f⁻¹] ≤ dim A`. -/
theorem ringKrullDim_localization_away_le {A : Type*} [CommRing A] (f : A) :
    ringKrullDim (Localization.Away f) ≤ ringKrullDim A := by
  unfold ringKrullDim
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A (Localization.Away f)))
  intro a b hab
  exact lt_of_le_of_ne (Ideal.comap_mono hab.le) fun heq =>
    hab.ne (PrimeSpectrum.localization_comap_injective _ (Submonoid.powers f) heq)

/-- A prime ideal disjoint from `{1, f, f², …}` has the same height before and after
localizing away from `f`. -/
theorem height_preserved_by_localization_away {A : Type*} [CommRing A] [IsNoetherianRing A]
    (f : A) (P : Ideal A) [P.IsPrime]
    (hfP : Disjoint (Submonoid.powers f : Set A) (P : Set A)) :
    (P.map (algebraMap A (Localization.Away f))).height = P.height :=
  IsLocalization.height_map_of_disjoint (Submonoid.powers f) P hfP




/-- Any minimal prime of a principal ideal `(g)` with `g ≠ 0` in a domain is nonzero. -/
theorem minimalPrime_ne_bot_of_nonzero {A : Type*} [CommRing A] [IsDomain A]
    (g : A) (hg : g ≠ 0) (P : Ideal A)
    (hP : P ∈ (Ideal.span ({g} : Set A)).minimalPrimes) : P ≠ ⊥ := by
  haveI := Ideal.minimalPrimes_isPrime hP
  intro hbot
  have : g ∈ P := hP.1.2 (subset_span (Set.mem_singleton g))
  rw [hbot] at this
  exact hg (Ideal.mem_bot.mp this)

/-- Krull's principal-ideal theorem in a Noetherian domain: a minimal prime over a nonzero
principal ideal has height exactly one. -/
theorem height_eq_one_of_minimalPrime_span_domain {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (g : A) (hg : g ≠ 0) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span ({g} : Set A)).minimalPrimes) :
    P.height = 1 := by

  have h_le : P.height ≤ 1 := by
    have : Submodule.IsPrincipal (Ideal.span ({g} : Set A)) := ⟨⟨g, by simp⟩⟩
    exact height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP

  have h_ne : P.height ≠ 0 := by
    rw [height_eq_primeHeight]
    intro h0
    have hmem : P ∈ minimalPrimes A := Ideal.primeHeight_eq_zero_iff.mp h0
    change P ∈ (⊥ : Ideal A).minimalPrimes at hmem
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at hmem
    have hPbot : P = ⊥ := Set.mem_singleton_iff.mp hmem
    exact minimalPrime_ne_bot_of_nonzero g hg P hP hPbot
  exact le_antisymm h_le (ENat.one_le_iff_ne_zero.mpr h_ne)

/-- The catenary inequality applied to a minimal prime of a nonzero principal ideal:
`1 + dim(A/P) ≤ dim A`. -/
theorem one_add_ringKrullDim_quotient_minimalPrime_le {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (g : A) (hg : g ≠ 0) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span ({g} : Set A)).minimalPrimes) :
    (1 : WithBot ℕ∞) + ringKrullDim (A ⧸ P) ≤ ringKrullDim A := by
  have h_ht : P.height = 1 := height_eq_one_of_minimalPrime_span_domain g hg P hP
  calc (1 : WithBot ℕ∞) + ringKrullDim (A ⧸ P)
      = ↑P.height + ringKrullDim (A ⧸ P) := by rw [h_ht]; rfl
    _ ≤ ringKrullDim A := height_add_ringKrullDim_quotient_le P

/-- For a minimal prime `P` over `(g)`, the dimension of `A/P` is at most the dimension of
`A/(g)`, via the surjective quotient map. -/
theorem ringKrullDim_quotient_minimalPrime_le_quotient_span {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (g : A) (_hg : g ≠ 0) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span ({g} : Set A)).minimalPrimes) :
    ringKrullDim (A ⧸ P) ≤ ringKrullDim (A ⧸ Ideal.span {g}) := by
  apply ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2)
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (Ideal.span {g}) r, rfl⟩


/-- Numeric helper: if `1 + d = n` in `WithBot ℕ∞` and `n ≥ 1`, then `d = n - 1`. -/
lemma withBot_ENat_add_one_eq_coe {d : WithBot ℕ∞} {n : ℕ} (hn : n ≥ 1)
    (h : (1 : WithBot ℕ∞) + d = ↑(↑n)) :
    d = ↑(↑(n - 1) : ℕ∞) := by
  cases d with
  | bot => simp at h
  | coe d' =>
    rw [show (1 : WithBot ℕ∞) = ↑(1 : ℕ∞) from rfl, ← WithBot.coe_add] at h
    have h' : (1 : ℕ∞) + d' = ↑n := WithBot.coe_injective h
    cases d' with
    | top => simp at h'
    | coe m =>
      congr 1; congr 1
      have : 1 + m = n := by
        apply @WithTop.coe_injective ℕ (1 + m) n
        push_cast at h' ⊢; exact h'
      omega

/-- No element of `k = MvPolynomial (Fin 0) k` is irreducible (every nonzero element is a unit). -/
lemma not_irreducible_mvPolynomial_fin_zero (k : Type*) [Field k]
    (f : MvPolynomial (Fin 0) k) : ¬Irreducible f := by
  intro hf
  have hiso := (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toRingEquiv
  have hne' : hiso f ≠ 0 := by
    intro h; exact Irreducible.ne_zero hf (hiso.injective (by simp [h]))
  exact hf.not_isUnit (show IsUnit f by
    rw [← hiso.symm_apply_apply f]; exact (IsUnit.mk0 _ hne').map hiso.symm.toRingHom)

/-- If `MvPolynomial (Fin n) k` admits an irreducible element, then `n ≥ 1`. -/
lemma pos_of_irreducible_mvPolynomial (k : Type*) [Field k] (n : ℕ)
    (f : MvPolynomial (Fin n) k) (hf : Irreducible f) : n ≥ 1 := by
  by_contra h
  push Not at h
  interval_cases n
  exact not_irreducible_mvPolynomial_fin_zero k f hf

/-- The ideal `(f)` cut out by an irreducible polynomial in `k[x₁,…,xₙ]` has height one. -/
theorem height_span_irreducible_mvPolynomial (k : Type*) [Field k] (n : ℕ)
    (f : MvPolynomial (Fin n) k) (hf : Irreducible f) :
    (Ideal.span ({f} : Set (MvPolynomial (Fin n) k))).height = 1 := by
  haveI : (Ideal.span ({f} : Set (MvPolynomial (Fin n) k))).IsPrime := by
    rw [Ideal.span_singleton_prime (Irreducible.ne_zero hf)]
    exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
  have hmem : Ideal.span ({f} : Set (MvPolynomial (Fin n) k)) ∈
      (Ideal.span ({f} : Set (MvPolynomial (Fin n) k))).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _
  have h_le : (Ideal.span ({f} : Set (MvPolynomial (Fin n) k))).height ≤ 1 :=
    height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmem
  have h_ne : (Ideal.span ({f} : Set (MvPolynomial (Fin n) k))).height ≠ 0 := by
    rw [height_eq_primeHeight]; intro h0
    have := Ideal.primeHeight_eq_zero_iff.mp h0
    change _ ∈ (⊥ : Ideal _).minimalPrimes at this
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at this
    have hbot := Set.mem_singleton_iff.mp this
    have : f ∈ (⊥ : Ideal (MvPolynomial (Fin n) k)) := by
      rw [← hbot]; exact subset_span (Set.mem_singleton f)
    exact Irreducible.ne_zero hf (Ideal.mem_bot.mp this)
  exact le_antisymm h_le (ENat.one_le_iff_ne_zero.mpr h_ne)



end
