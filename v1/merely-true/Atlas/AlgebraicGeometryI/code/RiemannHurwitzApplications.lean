/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannHurwitzDegree
import Atlas.AlgebraicGeometryI.code.NormalExtension
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Height

noncomputable section

open RiemannHurwitzFormula CanonicalSheafCurves RiemannHurwitzDegree

namespace RiemannHurwitzApplications

section GenusBounds

/-- Genus lower bound for a degree-`n` cover of a positive-genus target:
`g_X ≥ n · g_Y − (n − 1)`, an immediate consequence of Riemann–Hurwitz with
`deg R ≥ 0`. -/
theorem genus_bound_cover_pos_genus (g_X g_Y n degR : ℤ)
    (hR : 0 ≤ degR)
    (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR)
    (_h_gY : g_Y ≥ 1) :
    g_X ≥ n * g_Y - (n - 1) := by
  linarith

/-- Reformulation of the genus bound: `g_X ≥ n(g_Y − 1) + 1`. -/
theorem genus_bound_cover_pos_genus_alt (g_X g_Y n degR : ℤ)
    (hR : 0 ≤ degR)
    (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR) :
    g_X ≥ n * (g_Y - 1) + 1 := by
  linarith


/-- For a cover of a positive-genus curve, the source genus dominates the
target genus: `g_X ≥ g_Y`. -/
theorem genus_cover_ge_target_genus (g_X g_Y n degR : ℤ)
    (hR : 0 ≤ degR) (hn : n ≥ 1) (h_gY : g_Y ≥ 1)
    (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR) :
    g_X ≥ g_Y := by
  nlinarith

/-- Strict genus inequality `g_X > g_Y` for a degree-`≥ 2` cover of a curve
of general type (`g_Y ≥ 2`). -/
theorem genus_cover_strict_inequality (g_X g_Y n degR : ℤ)
    (hR : 0 ≤ degR) (hn : n ≥ 2) (h_gY : g_Y ≥ 2)
    (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR) :
    g_X > g_Y := by
  nlinarith


/-- Étale cover (no ramification): the Riemann–Hurwitz formula degenerates to
the exact relation `g_X = n(g_Y − 1) + 1`. -/
theorem genus_etale_cover_exact (g_X g_Y n : ℤ)
    (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + 0) :
    g_X = n * (g_Y - 1) + 1 := by
  linarith

end GenusBounds

section Luroth

/-- Lüroth's theorem (target-side): a cover of `ℙ¹` (`g_X = 0`) forces the
target to have genus zero, `g_Y = 0`. -/
theorem luroth_theorem_target_genus_zero (g_Y n degR : ℤ)
    (hR : 0 ≤ degR)
    (hn : n ≥ 1)
    (hgY : g_Y ≥ 0)
    (h_RH : 2 * (0 : ℤ) - 2 = n * (2 * g_Y - 2) + degR) :
    g_Y = 0 := by
  simp only [mul_zero, zero_sub] at h_RH
  nlinarith

/-- For `ℙ¹ → ℙ¹` of degree `n`, the ramification divisor has degree `2(n−1)`. -/
theorem ramification_formula_genus_zero (n degR : ℤ)
    (h_RH : 2 * (0 : ℤ) - 2 = n * (2 * (0 : ℤ) - 2) + degR) :
    degR = 2 * (n - 1) := by
  simp only [mul_zero, zero_sub] at h_RH
  linarith

/-- A degree-1 cover `ℙ¹ → ℙ¹` (an isomorphism) is unramified: `deg R = 0`. -/
theorem degree_one_unramified_genus_zero (degR : ℤ)
    (h_RH : 2 * (0 : ℤ) - 2 = (1 : ℤ) * (2 * (0 : ℤ) - 2) + degR) :
    degR = 0 := by
  simp only [mul_zero, zero_sub, one_mul] at h_RH
  linarith



/-- For an arbitrary cover of `ℙ¹`, `2 g_X = deg R − 2n + 2`. -/
theorem genus_formula_cover_of_P1 (g_X n degR : ℤ)
    (h_RH : 2 * g_X - 2 = n * (2 * (0 : ℤ) - 2) + degR) :
    2 * g_X = degR - 2 * n + 2 := by
  simp only [mul_zero, zero_sub] at h_RH
  linarith

end Luroth

section GenusZero






end GenusZero

section SpecialCases

/-- Specialization to a target `ℙ¹`: `2 g_X = deg R − 2n + 2`. -/
theorem genus_formula_target_P1 (g_X n degR : ℤ)
    (h_RH : 2 * g_X - 2 = n * (2 * 0 - 2) + degR) :
    2 * g_X = degR - 2 * n + 2 := by
  linarith

/-- For a cover of an elliptic curve (`g_Y = 1`), the source has `g_X ≥ 1`. -/
theorem genus_formula_target_elliptic (g_X n degR : ℤ)
    (hR : 0 ≤ degR)
    (h_RH : 2 * g_X - 2 = n * (2 * 1 - 2) + degR) :
    g_X ≥ 1 := by
  linarith

/-- An étale cover of an elliptic curve is itself elliptic: `g_X = 1`. -/
theorem etale_cover_elliptic_genus (g_X n : ℤ)
    (h_RH : 2 * g_X - 2 = n * (2 * 1 - 2) + 0) :
    g_X = 1 := by
  linarith

/-- A cover of a general-type curve (`g_Y ≥ 2`) has genus `g_X ≥ 2`. -/
theorem genus_ge_2_for_cover_of_general_type (g_X g_Y n degR : ℤ)
    (hR : 0 ≤ degR) (hn : n ≥ 1) (h_gY : g_Y ≥ 2)
    (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR) :
    g_X ≥ 2 := by
  nlinarith

end SpecialCases

section Prop39

/-- Prop 39 (Lec, normal domain criterion): the data needed to express
integrality of a fraction in terms of local conditions at height-one primes. -/
structure NormalDomainLocalizationData (R : Type*) [CommRing R] [IsDomain R] where
  isIntegrallyClosed : IsIntegrallyClosed R
  intersection_property :
    ∀ (a b : R), b ≠ 0 →
    (∀ (p : Ideal R), p.IsPrime → p ≠ ⊥ → p.height ≤ (1 : ℕ∞) →
      ∃ (r s : R), s ∉ p ∧ a * s = b * r) →
    ∃ (q : R), a = b * q

/-- Dedekind domains canonically satisfy the normal-domain localization
property: an algebraic Hartogs-type construction recovers the global element
from compatible local fractions. -/
def NormalDomainLocalizationData.ofDedekind
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    NormalDomainLocalizationData R where
  isIntegrallyClosed := inferInstance
  intersection_property := by
    intro a b hb h_local
    have hinj := IsFractionRing.injective R K
    have hb' : algebraMap R K b ≠ 0 := by rwa [Ne, map_eq_zero_iff _ hinj]
    set x := algebraMap R K a * (algebraMap R K b)⁻¹ with hx_def

    have hx_mem : x ∈ Set.range (algebraMap R K) := by
      apply AlgebraicHartogs.algebraicHartogs_dedekind x
      intro v
      obtain ⟨r, s, hs_notin, hrs⟩ := h_local v.asIdeal v.isPrime v.ne_bot
        (by rw [AlgebraicHartogs.height_eq_one_of_prime_ne_bot v.asIdeal v.ne_bot])

      show ∃ (a' s' : R) (_ : s' ∈ v.asIdeal.primeCompl),
        x = algebraMap R K a' * (algebraMap R K s')⁻¹
      refine ⟨r, s, hs_notin, ?_⟩
      have hs' : algebraMap R K s ≠ 0 := by
        intro h0; exact hs_notin (by rw [(map_eq_zero_iff _ hinj).mp h0]; exact v.asIdeal.zero_mem)
      have hmul : algebraMap R K a * algebraMap R K s =
          algebraMap R K b * algebraMap R K r := by rw [← map_mul, ← map_mul, hrs]
      rw [hx_def]
      suffices algebraMap R K a = algebraMap R K r * (algebraMap R K s)⁻¹ * algebraMap R K b by
        rw [this, mul_assoc, mul_inv_cancel₀ hb', mul_one]
      calc algebraMap R K a
          = algebraMap R K a * algebraMap R K s * (algebraMap R K s)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hs', mul_one]
        _ = algebraMap R K b * algebraMap R K r * (algebraMap R K s)⁻¹ := by rw [hmul]
        _ = algebraMap R K r * (algebraMap R K s)⁻¹ * algebraMap R K b := by ring

    obtain ⟨q, hq⟩ := hx_mem
    use q
    apply hinj
    rw [map_mul, hq, hx_def, mul_comm, mul_assoc, inv_mul_cancel₀ hb', mul_one]

/-- The element-criterion form of Prop 39: divisibility `b ∣ a` holds globally
iff it holds at every height-one prime. -/
theorem normal_domain_element_criterion
    (R : Type*) [CommRing R] [IsDomain R]
    (hR : NormalDomainLocalizationData R)
    (a b : R) (hb : b ≠ 0)
    (h_local : ∀ (p : Ideal R), p.IsPrime → p ≠ ⊥ → p.height ≤ (1 : ℕ∞) →
      ∃ (r s : R), s ∉ p ∧ a * s = b * r) :
    ∃ (q : R), a = b * q :=
  hR.intersection_property a b hb h_local

/-- Every Dedekind domain is integrally closed (a normal domain). -/
theorem dedekind_normal_domain (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] :
    IsIntegrallyClosed R :=
  inferInstance

end Prop39

section Examples

end Examples

end RiemannHurwitzApplications

end
