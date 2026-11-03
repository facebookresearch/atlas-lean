/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

noncomputable section

open MvPolynomial Ideal

namespace CommutativeAlgebra

theorem hilbert_nullstellensatz_base (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    I.IsMaximal ↔ ∃ a : Fin n → ℂ, I = vanishingIdeal ℂ {a} :=
  MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton

theorem vanishingIdeal_singleton_eq_ker_aeval (n : ℕ) (a : Fin n → ℂ) :
    (vanishingIdeal ℂ {a} : Ideal (MvPolynomial (Fin n) ℂ)) =
      RingHom.ker (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) := by
  ext p
  simp [RingHom.mem_ker]

theorem hilbert_nullstellensatz_weak_ker (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    I.IsMaximal ↔
      ∃ a : Fin n → ℂ, I = RingHom.ker (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) := by
  rw [hilbert_nullstellensatz_base]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.trans (vanishingIdeal_singleton_eq_ker_aeval n a)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.trans (vanishingIdeal_singleton_eq_ker_aeval n a).symm⟩

theorem hilbert_nullstellensatz_weak (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) ℂ)
    (J : Ideal (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range P))) :
    J.IsMaximal ↔
      ∃ a : Fin n → ℂ, (∀ i, MvPolynomial.aeval a (P i) = 0) ∧
        J = Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range P))) (vanishingIdeal ℂ {a}) := by
  constructor
  · intro hJ
    haveI : J.IsMaximal := hJ
    have hcomap : (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range P))) J).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨a, ha⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hcomap
    refine ⟨a, ?_, ?_⟩
    · intro i
      have hPi : P i ∈ Ideal.span (Set.range P) := Ideal.subset_span ⟨i, rfl⟩
      have hle : Ideal.span (Set.range P) ≤
          Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range P))) J := by
        intro x hx
        rw [Ideal.mem_comap]
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact J.zero_mem
      have hPiV : P i ∈ vanishingIdeal ℂ ({a} : Set (Fin n → ℂ)) := ha ▸ hle hPi
      simp [vanishingIdeal] at hPiV
      exact hPiV
    · have := (Ideal.map_comap_of_surjective (Ideal.Quotient.mk (Ideal.span (Set.range P)))
        Ideal.Quotient.mk_surjective J).symm
      rw [ha] at this
      exact this
  · rintro ⟨a, ha, rfl⟩
    have hmax : (vanishingIdeal ℂ ({a} : Set (Fin n → ℂ))).IsMaximal :=
      MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mpr ⟨a, rfl⟩
    have hle : Ideal.span (Set.range P) ≤ vanishingIdeal ℂ ({a} : Set (Fin n → ℂ)) := by
      rw [Ideal.span_le]
      intro p ⟨i, hi⟩
      simp [vanishingIdeal]
      rw [← hi]
      exact ha i
    haveI := hmax
    have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span (Set.range P))) ≤
        vanishingIdeal ℂ ({a} : Set (Fin n → ℂ)) := by
      rw [Ideal.mk_ker]
      exact hle
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker
