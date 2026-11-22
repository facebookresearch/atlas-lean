/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannHurwitz
import Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves
import Mathlib.RingTheory.DedekindDomain.Different

noncomputable section

open Ideal Module CanonicalSheafCurves

section GlobalRamification

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [NoZeroSMulDivisors R S]

/-- Global ramification contribution: sum of the total ramification at each prime of `R` lying
under the cover `S/R`. -/
def globalRamification
    (basePrimes : Finset (Ideal R))
    (hmax : ∀ p ∈ basePrimes, p.IsMaximal)
    (hbot : ∀ p ∈ basePrimes, p ≠ ⊥) : ℤ :=
  basePrimes.sum fun p =>
    if h : p ∈ basePrimes then
      haveI : p.IsMaximal := hmax p h
      totalRamificationAt S p (hbot p h)
    else 0

/-- Unfolding of `globalRamification` as a sum of local total-ramification contributions. -/
theorem globalRamification_eq
    (basePrimes : Finset (Ideal R))
    (hmax : ∀ p ∈ basePrimes, p.IsMaximal)
    (hbot : ∀ p ∈ basePrimes, p ≠ ⊥) :
    globalRamification S basePrimes hmax hbot =
    basePrimes.sum fun p =>
      if h : p ∈ basePrimes then
        haveI : p.IsMaximal := hmax p h
        totalRamificationAt S p (hbot p h)
      else 0 := rfl

/-- The global ramification is non-negative. -/
theorem globalRamification_nonneg
    (basePrimes : Finset (Ideal R))
    (hmax : ∀ p ∈ basePrimes, p.IsMaximal)
    (hbot : ∀ p ∈ basePrimes, p ≠ ⊥) :
    0 ≤ globalRamification S basePrimes hmax hbot := by
  unfold globalRamification
  apply Finset.sum_nonneg
  intro p hp
  simp [hp]
  haveI : p.IsMaximal := hmax p hp
  exact totalRamificationAt_nonneg S (hbot p hp)

end GlobalRamification

/-- Data of a finite covering of smooth complete curves `X → Y` arising from a Dedekind ring
extension `R ⊂ S`, together with the local canonical-degree decompositions used in the
Riemann–Hurwitz formula. -/
structure CurveCovering where
  R : Type*
  S : Type*
  [instCR : CommRing R]
  [instDR : IsDedekindDomain R]
  [instCS : CommRing S]
  [instDS : IsDedekindDomain S]
  [instAlg : Algebra R S]
  [instNZ : NoZeroSMulDivisors R S]
  X : SmoothCompleteCurve
  Y : SmoothCompleteCurve
  n : ℤ
  h_n_pos : 0 < n
  basePrimes : Finset (Ideal R)
  h_max : ∀ p ∈ basePrimes, p.IsMaximal
  h_bot : ∀ p ∈ basePrimes, p ≠ ⊥
  localDegK_X : Ideal R → ℤ
  localDegK_Y : Ideal R → ℤ
  h_degK_X_sum : X.degK = basePrimes.sum localDegK_X
  h_degK_Y_sum : Y.degK = basePrimes.sum localDegK_Y
  h_local_degree : ∀ p ∈ basePrimes,
    localDegK_X p = n * localDegK_Y p +
      (if h : p ∈ basePrimes then
        haveI : p.IsMaximal := h_max p h
        totalRamificationAt S p (h_bot p h)
      else 0)

attribute [instance] CurveCovering.instCR CurveCovering.instDR
  CurveCovering.instCS CurveCovering.instDS CurveCovering.instAlg
  CurveCovering.instNZ

section GlobalFormula

variable (f : CurveCovering)

/-- The ramification degree `deg R` of a curve covering. -/
def CurveCovering.deg_R : ℤ :=
  globalRamification f.S f.basePrimes f.h_max f.h_bot

/-- `deg R` is non-negative. -/
theorem CurveCovering.deg_R_nonneg : 0 ≤ f.deg_R :=
  globalRamification_nonneg f.S f.basePrimes f.h_max f.h_bot

/-- Canonical divisor identity in a covering: `K_X = n · K_Y + R`. -/
theorem CurveCovering.degK_eq : f.X.degK = f.n * f.Y.degK + f.deg_R := by

  rw [f.h_degK_X_sum]

  have h_sum : f.basePrimes.sum f.localDegK_X =
      f.basePrimes.sum (fun p =>
        f.n * f.localDegK_Y p +
          (if h : p ∈ f.basePrimes then
            haveI : p.IsMaximal := f.h_max p h
            totalRamificationAt f.S p (f.h_bot p h)
          else 0)) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact f.h_local_degree p hp
  rw [h_sum]

  rw [Finset.sum_add_distrib]

  have h_mul : f.basePrimes.sum (fun p => f.n * f.localDegK_Y p) =
      f.n * f.basePrimes.sum f.localDegK_Y := by
    rw [Finset.mul_sum]
  rw [h_mul]

  rw [← f.h_degK_Y_sum]

  rfl

end GlobalFormula

section GenusFormula

variable (f : CurveCovering)





end GenusFormula

section Etale

variable (f : CurveCovering)




end Etale

section Specializations

/-- Numerical identity for hyperelliptic curves: `2g - 2 = 2(2·0 - 2) + (2g + 2)`. -/
theorem hyperelliptic_identity (g : ℤ) :
    2 * g - 2 = 2 * (2 * 0 - 2) + (2 * g + 2) := by ring

end Specializations

section TrivialCovering

open CanonicalSheafCurves








/-- General identity covering: a smooth complete curve `C` paired with itself at degree `1`. -/
def CurveCovering.identityCovering
    (C : SmoothCompleteCurve)
    (p : Ideal ℤ) (hp_max : p.IsMaximal) (hp_bot : p ≠ ⊥)
    (h_totalRam : totalRamificationAt ℤ p hp_bot = 0) :
    CurveCovering where
  R := ℤ
  S := ℤ
  X := C
  Y := C
  n := 1
  h_n_pos := Int.one_pos
  basePrimes := {p}
  h_max := by simp [hp_max]
  h_bot := by simp [hp_bot]
  localDegK_X := fun q => if q = p then C.degK else 0
  localDegK_Y := fun q => if q = p then C.degK else 0
  h_degK_X_sum := by simp
  h_degK_Y_sum := by simp
  h_local_degree := by
    intro q hq
    simp only [Finset.mem_singleton] at hq
    subst hq
    simp only [ite_true, dif_pos (Finset.mem_singleton.mpr rfl)]
    rw [h_totalRam]
    ring

/-- The identity covering has ramification degree `0` when the local total ramification vanishes. -/
theorem CurveCovering.identityCovering_deg_R
    (C : SmoothCompleteCurve)
    (p : Ideal ℤ) (hp_max : p.IsMaximal) (hp_bot : p ≠ ⊥)
    (h_totalRam : totalRamificationAt ℤ p hp_bot = 0) :
    (CurveCovering.identityCovering C p hp_max hp_bot h_totalRam).deg_R = 0 := by
  unfold CurveCovering.deg_R globalRamification CurveCovering.identityCovering
  simp [h_totalRam]


end TrivialCovering

section DirectCovering

/-- Simplified curve-covering structure: stores only the global canonical-degree formula
without local data. -/
structure CurveCoveringDirect where
  R : Type*
  S : Type*
  [instCR : CommRing R]
  [instDR : IsDedekindDomain R]
  [instCS : CommRing S]
  [instDS : IsDedekindDomain S]
  [instAlg : Algebra R S]
  [instNZ : NoZeroSMulDivisors R S]
  X : SmoothCompleteCurve
  Y : SmoothCompleteCurve
  n : ℤ
  h_n_pos : 0 < n
  basePrimes : Finset (Ideal R)
  h_max : ∀ p ∈ basePrimes, p.IsMaximal
  h_bot : ∀ p ∈ basePrimes, p ≠ ⊥
  h_degK_formula :
    X.degK = n * Y.degK + globalRamification S basePrimes h_max h_bot

attribute [instance] CurveCoveringDirect.instCR CurveCoveringDirect.instDR
  CurveCoveringDirect.instCS CurveCoveringDirect.instDS
  CurveCoveringDirect.instAlg CurveCoveringDirect.instNZ

/-- Ramification degree of a `CurveCoveringDirect`. -/
def CurveCoveringDirect.deg_R (f : CurveCoveringDirect) : ℤ :=
  globalRamification f.S f.basePrimes f.h_max f.h_bot

/-- Non-negativity of `deg R` for a `CurveCoveringDirect`. -/
theorem CurveCoveringDirect.deg_R_nonneg (f : CurveCoveringDirect) :
    0 ≤ f.deg_R :=
  globalRamification_nonneg f.S f.basePrimes f.h_max f.h_bot

/-- Canonical-degree identity packaged in `CurveCoveringDirect`. -/
theorem CurveCoveringDirect.degK_eq (f : CurveCoveringDirect) :
    f.X.degK = f.n * f.Y.degK + f.deg_R :=
  f.h_degK_formula






/-- Forgetful map from the local `CurveCovering` data to the simpler `CurveCoveringDirect`. -/
def CurveCovering.toDirect (f : CurveCovering) : CurveCoveringDirect where
  R := f.R
  S := f.S
  X := f.X
  Y := f.Y
  n := f.n
  h_n_pos := f.h_n_pos
  basePrimes := f.basePrimes
  h_max := f.h_max
  h_bot := f.h_bot
  h_degK_formula := f.degK_eq

end DirectCovering

end
