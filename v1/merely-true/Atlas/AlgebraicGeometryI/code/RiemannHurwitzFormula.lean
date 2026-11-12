/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Discriminant
import Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves
import Atlas.AlgebraicGeometryI.code.RiemannHurwitz
import Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition

noncomputable section

open Ideal Module

namespace RiemannHurwitzFormula

section DVRRamification

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
variable [Algebra R S]

/-- The ramification index of an extension of DVRs `R ⊆ S`, defined as the
ramification index of the maximal ideals. -/
def DVRRamificationIndex : ℕ :=
  (IsLocalRing.maximalIdeal R).ramificationIdx (IsLocalRing.maximalIdeal S)

/-- An extension of DVRs `R ⊆ S` is unramified iff the ramification index equals 1. -/
def DVRIsUnramified : Prop :=
  DVRRamificationIndex (R := R) (S := S) = 1

/-- Fundamental identity for an extension of DVRs: the ramification index
times the inertia degree equals the field extension degree `[L : K]`. -/
theorem DVR_ef_eq_degree
    (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S] [IsDedekindDomain R] [IsDedekindDomain S]
    (hp0 : IsLocalRing.maximalIdeal R ≠ ⊥) :
    DVRRamificationIndex (R := R) (S := S) *
      inertiaDeg (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) = finrank K L :=
  ramificationIdx_mul_inertiaDeg_of_isLocalRing S K L hp0

/-- In the unramified case for DVRs, the inertia degree equals the field
extension degree `[L : K]`. -/
theorem DVR_unramified_inertiaDeg_eq_degree
    (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S] [IsDedekindDomain R] [IsDedekindDomain S]
    (hp0 : IsLocalRing.maximalIdeal R ≠ ⊥)
    (hunr : DVRIsUnramified (R := R) (S := S)) :
    inertiaDeg (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) = finrank K L := by
  have h := ramificationIdx_mul_inertiaDeg_of_isLocalRing S K L hp0
  unfold DVRIsUnramified DVRRamificationIndex at hunr
  rw [hunr, one_mul] at h
  exact h

/-- The local contribution `e - 1` of a DVR extension to the ramification
divisor is non-negative. -/
theorem DVR_ramification_contribution_nonneg
    [IsDedekindDomain R] [IsDedekindDomain S]
    [NoZeroSMulDivisors R S]
    (hp0 : IsLocalRing.maximalIdeal R ≠ ⊥)
    [(IsLocalRing.maximalIdeal R).IsMaximal]
    [(IsLocalRing.maximalIdeal S).IsPrime]
    [(IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R)] :
    0 ≤ (DVRRamificationIndex (R := R) (S := S) : ℤ) - 1 := by
  unfold DVRRamificationIndex
  have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
    (IsLocalRing.maximalIdeal S) hp0 (p := IsLocalRing.maximalIdeal R)
  omega

end DVRRamification

section RamificationDivisorDegree

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [NoZeroSMulDivisors R S]

/-- The local degree at `p` of the ramification divisor of an extension
`R ⊆ S` of Dedekind domains: the sum over primes `P` over `p` of `e_P - 1`. -/
def ramificationDivisorDegreeAt
    (p : Ideal R) [p.IsMaximal] (_hp0 : p ≠ ⊥) : ℤ :=
  ∑ P ∈ primesOverFinset p S,
    ((p.ramificationIdx P : ℤ) - 1)

/-- The local ramification-divisor degree at `p` is non-negative. -/
theorem ramificationDivisorDegreeAt_nonneg
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    0 ≤ ramificationDivisorDegreeAt S p hp0 := by
  unfold ramificationDivisorDegreeAt
  apply Finset.sum_nonneg
  intro P hP
  have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
  have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
  have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
  omega

/-- The local ramification-divisor degree at `p` is bounded above by the
field extension degree `[L : K]`, via the fundamental identity. -/
theorem ramificationDivisorDegreeAt_le_finrank
    (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ramificationDivisorDegreeAt S p hp0 ≤ finrank K L := by
  unfold ramificationDivisorDegreeAt
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
    _ = (finrank K L : ℤ) := by exact_mod_cast hfund

/-- The local ramification-divisor degree at `p` vanishes iff every prime
above `p` is unramified (`e_P = 1`). -/
theorem ramificationDivisorDegreeAt_eq_zero_iff
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ramificationDivisorDegreeAt S p hp0 = 0 ↔
      ∀ P ∈ primesOverFinset p S,
        p.ramificationIdx P = 1 := by
  unfold ramificationDivisorDegreeAt
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

end RamificationDivisorDegree

section DegreeCorollary

/-- Numerical data attached to a finite morphism `f : X → Y` of smooth curves:
the degree, the degrees of the canonical divisors on source and target, and
the degree of the ramification divisor, with non-negativity/positivity hypotheses. -/
structure CurveMorphismData where
  degree : ℤ
  deg_KX : ℤ
  deg_KY : ℤ
  deg_R : ℤ
  h_deg_R_nonneg : 0 ≤ deg_R
  h_deg_pos : 0 < degree

/-- Given the canonical decomposition `K_X = f*K_Y + R` and the pullback identity
`deg f*K_Y = n · deg K_Y`, we obtain `deg K_X = n · deg K_Y + deg R`. -/
theorem riemann_hurwitz_canonical_decomp (f : CurveMorphismData)
    (deg_fKY : ℤ)
    (h_pullback : deg_fKY = f.degree * f.deg_KY)
    (h_canonical : f.deg_KX = deg_fKY + f.deg_R) :
    f.deg_KX = f.degree * f.deg_KY + f.deg_R := by
  linarith

/-- Riemann–Hurwitz in degree form (Cor 27, Lec 21): for a `CurveCovering`,
`deg K_X = n · deg K_Y + deg R`. -/
theorem riemann_hurwitz_degree_corollary (f : CurveCovering) :
    f.X.degK = f.n * f.Y.degK + f.deg_R :=
  f.degK_eq

/-- Translating Riemann–Hurwitz from canonical degrees to genus form via
`deg K_X = 2 g_X - 2`, `deg K_Y = 2 g_Y - 2`. -/
theorem riemann_hurwitz_genus_from_data (f : CurveMorphismData)
    (g_X g_Y : ℤ)
    (h_gX : f.deg_KX = 2 * g_X - 2)
    (h_gY : f.deg_KY = 2 * g_Y - 2)
    (h_decomp : f.deg_KX = f.degree * f.deg_KY + f.deg_R) :
    2 * g_X - 2 = f.degree * (2 * g_Y - 2) + f.deg_R := by
  rw [← h_gX, ← h_gY]; exact h_decomp

/-- Lower bound for the genus from Riemann–Hurwitz and ramification non-negativity. -/
theorem riemann_hurwitz_genus_lower_bound (f : CurveMorphismData)
    (g_X g_Y : ℤ)
    (h_gX : f.deg_KX = 2 * g_X - 2)
    (h_gY : f.deg_KY = 2 * g_Y - 2)
    (h_decomp : f.deg_KX = f.degree * f.deg_KY + f.deg_R) :
    2 * g_X - 2 ≥ f.degree * (2 * g_Y - 2) := by
  have := riemann_hurwitz_genus_from_data f g_X g_Y h_gX h_gY h_decomp
  linarith [f.h_deg_R_nonneg]

/-- Solving Riemann–Hurwitz for `deg R`: it is determined by the canonical
degrees and the cover degree. -/
theorem riemann_hurwitz_ramification_determines_genus (f : CurveMorphismData)
    (h_decomp : f.deg_KX = f.degree * f.deg_KY + f.deg_R) :
    f.deg_R = f.deg_KX - f.degree * f.deg_KY := by
  linarith [h_decomp]

end DegreeCorollary

section P1Target

/-- Construct `CurveMorphismData` for a degree-`n` cover of `ℙ¹`, where
`deg K_Y = -2`. -/
def CurveMorphismData.toP1 (n : ℤ) (deg_KX deg_R : ℤ)
    (h_nonneg : 0 ≤ deg_R) (h_pos : 0 < n) : CurveMorphismData where
  degree := n
  deg_KX := deg_KX
  deg_KY := -2
  deg_R := deg_R
  h_deg_R_nonneg := h_nonneg
  h_deg_pos := h_pos

/-- Riemann–Hurwitz decomposition for a cover of `ℙ¹` (target genus 0). -/
theorem riemann_hurwitz_P1_target
    (n deg_KX deg_R : ℤ)
    (h_nonneg : 0 ≤ deg_R)
    (h_pos : 0 < n)
    (h_formula : deg_KX = -2 * n + deg_R) :
    (CurveMorphismData.toP1 n deg_KX deg_R h_nonneg h_pos).deg_KX =
    -2 * (CurveMorphismData.toP1 n deg_KX deg_R h_nonneg h_pos).degree +
    (CurveMorphismData.toP1 n deg_KX deg_R h_nonneg h_pos).deg_R := by
  simp [CurveMorphismData.toP1]
  linarith

/-- Riemann–Hurwitz for a cover of `ℙ¹` solved for `deg R`. -/
theorem riemann_hurwitz_P1_genus
    (n g deg_R : ℤ)
    (h_RH : 2 * g - 2 = -2 * n + deg_R) :
    deg_R = 2 * g + 2 * n - 2 := by linarith

/-- Totally ramified cover of `ℙ¹`: if there are `r` totally ramified points
(each contributing `n - 1`), then `2 g = r(n-1) - 2n + 2`. -/
theorem totally_ramified_P1_genus
    (n g r : ℤ)
    (h_RH : 2 * g - 2 = -2 * n + r * (n - 1)) :
    2 * g = r * (n - 1) - 2 * n + 2 := by linarith

end P1Target

section EllipticCurveExample

/-- Numerical identity: a degree-2 cover of `ℙ¹` with 4 simple ramification
points has `n · deg K_{ℙ¹} + deg R = 0`, recovering `deg K_X = 0` for an elliptic curve. -/
theorem elliptic_curve_canonical_degree_zero :
    let n : ℤ := 2
    let num_ram : ℤ := 4
    let e : ℤ := 2
    let deg_R := num_ram * (e - 1)
    let deg_KP1 : ℤ := -2
    n * deg_KP1 + deg_R = 0 := by norm_num

/-- Numerical identity: Riemann–Hurwitz for a double cover of `ℙ¹` with four
simple branch points has genus `g = 1`. -/
theorem elliptic_curve_genus_one :
    let n : ℤ := 2
    let deg_R : ℤ := 4 * (2 - 1)
    let g : ℤ := 1
    2 * g - 2 = n * (-2) + deg_R := by norm_num

/-- `CurveMorphismData` for a double cover `E → ℙ¹` realizing an elliptic curve. -/
def ellipticCurveP1Data : CurveMorphismData where
  degree := 2
  deg_KX := 0
  deg_KY := -2
  deg_R := 4
  h_deg_R_nonneg := by norm_num
  h_deg_pos := by norm_num

/-- Verifies that `ellipticCurveP1Data` satisfies Riemann–Hurwitz in degree form. -/
theorem ellipticCurveP1_satisfies_RH :
    ellipticCurveP1Data.deg_KX =
    ellipticCurveP1Data.degree * ellipticCurveP1Data.deg_KY +
    ellipticCurveP1Data.deg_R := by
  simp [ellipticCurveP1Data]

/-- Numerical: for an elliptic curve `deg K = 0 = 2·1 - 2`. -/
theorem ellipticCurve_genus_from_canonical :
    (0 : ℤ) = 2 * 1 - 2 := by norm_num

end EllipticCurveExample

section Hyperelliptic

/-- For a hyperelliptic curve of genus `g` (a double cover of `ℙ¹`), the
number of branch points satisfies `b = 2g + 2`. -/
theorem hyperelliptic_branch_points_eq (g : ℤ) (b : ℤ)
    (h_RH : 2 * g - 2 = 2 * (-2 : ℤ) + b) :
    b = 2 * g + 2 := by linarith

/-- `CurveMorphismData` for a hyperelliptic double cover of `ℙ¹` realizing a
curve of genus `g`, with `2g + 2` simple branch points. -/
def hyperellipticData (g : ℤ) (hg : 0 ≤ 2 * g + 2) : CurveMorphismData where
  degree := 2
  deg_KX := 2 * g - 2
  deg_KY := -2
  deg_R := 2 * g + 2
  h_deg_R_nonneg := hg
  h_deg_pos := by norm_num

/-- The hyperelliptic data satisfies Riemann–Hurwitz in degree form. -/
theorem hyperellipticData_satisfies_RH (g : ℤ) (hg : 0 ≤ 2 * g + 2) :
    (hyperellipticData g hg).deg_KX =
    (hyperellipticData g hg).degree * (hyperellipticData g hg).deg_KY +
    (hyperellipticData g hg).deg_R := by
  simp [hyperellipticData]
  ring

end Hyperelliptic

section ArithmeticGenusConnection

/-- Express the ramification divisor degree in terms of arithmetic genera. -/
theorem riemann_hurwitz_arithmetic_genus_constraint
    (g_X g_Y : ℕ) (n deg_R : ℤ)
    (h_formula : 2 * (g_X : ℤ) - 2 = n * (2 * (g_Y : ℤ) - 2) + deg_R) :
    deg_R = 2 * (g_X : ℤ) - 2 - n * (2 * (g_Y : ℤ) - 2) := by linarith

/-- Genus growth bound: the source genus satisfies `g_X ≥ n(g_Y - 1) + 1`. -/
theorem riemann_hurwitz_genus_growth
    (g_X g_Y : ℤ) (n deg_R : ℤ) (hR : 0 ≤ deg_R)
    (h_formula : 2 * g_X - 2 = n * (2 * g_Y - 2) + deg_R) :
    g_X ≥ n * (g_Y - 1) + 1 := by linarith

/-- A degree-1 unramified cover is an isomorphism in the sense that source and
target have the same genus. -/
theorem riemann_hurwitz_isomorphism_genus
    (g_X g_Y : ℤ)
    (h_formula : 2 * g_X - 2 = 1 * (2 * g_Y - 2) + 0) :
    g_X = g_Y := by linarith

/-- For an étale (unramified) cover of degree `n`, `g_X = n g_Y - n + 1`. -/
theorem riemann_hurwitz_etale_genus
    (g_X g_Y n : ℤ)
    (h_formula : 2 * g_X - 2 = n * (2 * g_Y - 2) + 0) :
    g_X = n * g_Y - n + 1 := by linarith

end ArithmeticGenusConnection

end RiemannHurwitzFormula

end
