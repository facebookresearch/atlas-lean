/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Kaehler.Basic

noncomputable section

open Ideal

section SheafIsomorphism

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra k R]
variable (S : Type*) [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra k S]
variable [Algebra R S] [IsScalarTower k R S] [NoZeroSMulDivisors R S]
variable [Module.Finite R S]





end SheafIsomorphism

section DegreeFormula

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {S : Type*} [CommRing S] [IsDomain S] [IsDedekindDomain S]
variable [Algebra R S] [NoZeroSMulDivisors R S]

/-- Local degree contribution to the ramification divisor at `p`:
`∑_{P|p} (e_P - 1)`. -/
def localRamificationAt
    (p : Ideal R) [p.IsMaximal] (_hp0 : p ≠ ⊥) (S : Type*) [CommRing S]
    [IsDomain S] [IsDedekindDomain S] [Algebra R S] : ℤ :=
  ∑ P ∈ primesOverFinset p S,
    ((p.ramificationIdx P : ℤ) - 1)

set_option linter.unusedSectionVars false in
/-- The local ramification contribution `∑_{P|p}(e_P - 1)` is non-negative. -/
theorem local_ramification_nonneg
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (0 : ℤ) ≤ ∑ P ∈ primesOverFinset p S,
      ((p.ramificationIdx P : ℤ) - 1) := by
  apply Finset.sum_nonneg
  intro P hP
  have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
  have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
  have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
  omega

set_option linter.unusedSectionVars false in
/-- The local ramification contribution at `p` is bounded by the field
extension degree `[L : K]`. -/
theorem local_ramification_le_finrank
    (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ primesOverFinset p S,
      ((p.ramificationIdx P : ℤ) - 1) ≤ Module.finrank K L := by
  have hfund := sum_ramification_inertia S K L hp0
  calc ∑ P ∈ primesOverFinset p S,
      ((p.ramificationIdx P : ℤ) - 1)
    ≤ ∑ P ∈ primesOverFinset p S,
      (p.ramificationIdx P : ℤ) := by
        apply Finset.sum_le_sum; intro P _; omega
    _ ≤ ∑ P ∈ primesOverFinset p S,
        ((p.ramificationIdx P * inertiaDeg p P : ℕ) : ℤ) := by
        apply Finset.sum_le_sum
        intro P hP
        have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
        have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
        exact_mod_cast Nat.le_mul_of_pos_right _ (inertiaDeg_pos p P)
    _ = (Module.finrank K L : ℤ) := by exact_mod_cast hfund

set_option linter.unusedSectionVars false in
/-- The local ramification contribution vanishes iff every prime above `p`
has ramification index 1 (i.e. `p` is unramified). -/
theorem local_ramification_eq_zero_iff
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (∑ P ∈ primesOverFinset p S,
      ((p.ramificationIdx P : ℤ) - 1)) = 0 ↔
      ∀ P ∈ primesOverFinset p S,
        p.ramificationIdx P = 1 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h P hP
      have := h P hP
      have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
      have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
      have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
      omega
    · intro h P hP
      simp [h P hP]
  · intro P hP
    have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
    have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
    have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
    omega

/-- For an extension `R ⊆ S` of DVRs with fraction fields `K ⊆ L`, the
identity `e · f = [L : K]` holds. -/
theorem DVR_ef_product_eq_degree
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S]
    (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S] [IsDedekindDomain R] [IsDedekindDomain S]
    (hp0 : IsLocalRing.maximalIdeal R ≠ ⊥) :
    (IsLocalRing.maximalIdeal R).ramificationIdx (IsLocalRing.maximalIdeal S) *
      inertiaDeg (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) =
        Module.finrank K L :=
  ramificationIdx_mul_inertiaDeg_of_isLocalRing S K L hp0

end DegreeFormula

section GenusConsequences

/-- Riemann–Hurwitz lower bound for the source genus: `g_X ≥ n(g_Y - 1) + 1`. -/
theorem genus_lower_bound
    (gX gY n degR : ℤ)
    (hRH : 2 * gX - 2 = n * (2 * gY - 2) + degR)
    (hdegR : 0 ≤ degR) :
    gX ≥ n * (gY - 1) + 1 := by
  linarith

/-- Strict genus growth: a ramified degree `≥ 2` cover of a curve of genus
`≥ 2` strictly increases the genus. -/
theorem genus_growth_ramified
    (gX gY n degR : ℤ)
    (hRH : 2 * gX - 2 = n * (2 * gY - 2) + degR)
    (hdegR : 0 ≤ degR)
    (hn : n ≥ 2) (hgY : gY ≥ 2) :
    gX > gY := by
  have := genus_lower_bound gX gY n degR hRH hdegR
  nlinarith

/-- Riemann–Hurwitz specialized to target `ℙ¹` (genus 0). -/
theorem riemann_hurwitz_P1
    (gX n degR : ℤ)
    (hRH : 2 * gX - 2 = n * (2 * 0 - 2) + degR) :
    2 * gX - 2 = -2 * n + degR := by
  linarith

/-- Number of branch points of a hyperelliptic curve `X → ℙ¹`: `b = 2 g + 2`. -/
theorem hyperelliptic_branch_points_from_sheaf
    (gX degR : ℤ)
    (hRH : 2 * gX - 2 = 2 * (2 * 0 - 2) + degR) :
    degR = 2 * gX + 2 := by
  linarith

/-- Étale (unramified) covers: `g_X = n g_Y - n + 1`. -/
theorem etale_genus
    (gX gY n : ℤ)
    (hRH : 2 * gX - 2 = n * (2 * gY - 2) + 0) :
    gX = n * gY - n + 1 := by
  linarith

/-- For an étale double cover: `g_X = 2 g_Y - 1`. -/
theorem etale_double_cover_genus
    (gX gY : ℤ)
    (hRH : 2 * gX - 2 = 2 * (2 * gY - 2) + 0) :
    gX = 2 * gY - 1 := by
  linarith

end GenusConsequences

section Examples

/-- Numerical verification: a double cover of `ℙ¹` with 4 ramification points
yields an elliptic curve (genus 1). -/
theorem elliptic_curve_RH_verification :
    (2 : ℤ) * 1 - 2 = 2 * (2 * 0 - 2) + 4 := by norm_num

/-- Numerical verification: a hyperelliptic genus-2 cover of `ℙ¹` has
ramification divisor degree 6. -/
theorem genus2_hyperelliptic_verification :
    (2 : ℤ) * 2 - 2 = 2 * (2 * 0 - 2) + 6 := by norm_num

/-- Numerical verification: an étale double cover of a genus-2 curve has
source genus 3. -/
theorem etale_double_cover_genus2_verification :
    (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

/-- Numerical verification: a degree-3 cover of `ℙ¹` with `degR = 6` produces
a genus-1 curve. -/
theorem degree3_genus1_verification :
    (2 : ℤ) * 1 - 2 = 3 * (2 * 0 - 2) + 6 := by norm_num

end Examples

end
