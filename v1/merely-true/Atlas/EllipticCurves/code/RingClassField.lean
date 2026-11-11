/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.EllipticCurves.code.PointCounting
import Atlas.EllipticCurves.code.OrdinarySupersingular
import Atlas.EllipticCurves.code.HilbertClassPolynomial
import Atlas.EllipticCurves.code.CMTorsor

namespace Elliptic_Curves

/-- An integer `D` is the discriminant of an imaginary quadratic order if it
is negative and congruent to `0` or `1` modulo `4`. -/
def IsImagQuadDiscriminant (D : ℤ) : Prop :=
  D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)











/-- The Cornacchia-type norm equation `4p = t^2 - v^2 D` with `t, v` integers,
underlying Theorem 21.5(iv). -/
def NormEquation (D : ℤ) (p : ℕ) (t v : ℤ) : Prop :=
  4 * (p : ℤ) = t ^ 2 - v ^ 2 * D

/-- The prime `p` satisfies the Cornacchia norm equation for discriminant `D`
if there exist integers `t, v` with `4p = t^2 - v^2 D` and `p ∤ t`. -/
def SatisfiesNormEquation (D : ℤ) (p : ℕ) : Prop :=
  ∃ t v : ℤ, NormEquation D p t v ∧ ¬((p : ℤ) ∣ t)


/-- `p` is the norm of a principal ideal in the order of discriminant `D` iff
there exist integers `t, v` with `4p = t^2 - v^2 D` and `2 ∣ t - vD`. This is
condition (i) in Theorem 21.5 of Sutherland. -/
def IsNormOfPrincipalIdeal (D : ℤ) (p : ℕ) : Prop :=
  ∃ t v : ℤ, 4 * (p : ℤ) = t ^ 2 - v ^ 2 * D ∧ 2 ∣ (t - v * D)









/-- Definitional unfolding of `NormEquation D p t v`. -/
@[simp]
theorem normEquation_iff (D : ℤ) (p : ℕ) (t v : ℤ) :
    NormEquation D p t v ↔ 4 * (p : ℤ) = t ^ 2 - v ^ 2 * D :=
  Iff.rfl

/-- The norm equation is symmetric under sign change of `t, v`. -/
theorem normEquation_neg (D : ℤ) (p : ℕ) (t v : ℤ) :
    NormEquation D p t v ↔ NormEquation D p (-t) (-v) := by
  simp only [NormEquation, neg_sq]

/-- If `D < 0` and `NormEquation D p t v` holds, then `t^2 ≤ 4p`. -/
theorem normEquation_sq_le {D : ℤ} {p : ℕ} {t v : ℤ}
    (hD : D < 0) (hne : NormEquation D p t v) :
    t ^ 2 ≤ 4 * (p : ℤ) := by
  unfold NormEquation at hne
  nlinarith [sq_nonneg v]

/-- Definition 21.4 (Sutherland): the Kronecker symbol `(D/p)`. For odd primes
it agrees with the Legendre symbol; for `p = 2` it is `0` if `2 ∣ D`, `+1`
if `D ≡ ±1 mod 8`, and `-1` if `D ≡ ±3 mod 8`. -/
noncomputable def kroneckerSymbol (p : ℕ) [hp : Fact (Nat.Prime p)] (D : ℤ) : ℤ :=
  if p = 2 then
    if D % 2 = 0 then 0
    else if D % 8 = 1 ∨ D % 8 = 7 then 1
    else -1
  else
    legendreSym p D

/-- The Kronecker symbol `(D/p)` always takes values in `{-1, 0, 1}`. -/
theorem kroneckerSymbol_values {p : ℕ} [hp : Fact (Nat.Prime p)] (D : ℤ) :
    kroneckerSymbol p D = -1 ∨ kroneckerSymbol p D = 0 ∨ kroneckerSymbol p D = 1 := by
  unfold kroneckerSymbol
  split_ifs
  · right; left; rfl
  · right; right; rfl
  · left; rfl
  · have hq := quadraticChar_isQuadratic (ZMod p) (D : ZMod p)
    simp only [legendreSym]
    rcases hq with h | h | h
    · right; left; exact_mod_cast h
    · right; right; exact_mod_cast h
    · left; exact_mod_cast h

/-- For an odd prime, the Kronecker symbol coincides with the Legendre symbol. -/
theorem kroneckerSymbol_odd_prime {p : ℕ} [hp : Fact (Nat.Prime p)] (hodd : p ≠ 2) (D : ℤ) :
    kroneckerSymbol p D = legendreSym p D := by
  simp [kroneckerSymbol, hodd]

namespace Deuring

open Polynomial

/-- A "ring class field prime" for Theorem 21.12 (Deuring): a positive integer
`q > 1` that is coprime to the discriminant `D`, intended to represent a
prime power norm of a prime in the ring class field. -/
structure RingClassFieldPrime (D : ℤ) where
  q : ℕ
  q_pos : 1 < q
  coprime_q_D : Nat.Coprime q D.natAbs




end Deuring

end Elliptic_Curves

open NumberField

noncomputable section

namespace DeuringLifting




end DeuringLifting

namespace RingClassField

/-- Predicate (in `Prop`) form of "`D` is the discriminant of an imaginary
quadratic order": `D < 0` and `D ≡ 0` or `1 mod 4`. -/
structure IsImagQuadDisc (D : ℤ) : Prop where
  neg : D < 0
  cong : D % 4 = 0 ∨ D % 4 = 1








































end RingClassField

end

open Elliptic_Curves

namespace CMMethod




/-- The output of the CM method: a curve over a finite field `F` together with
its Frobenius trace witnessing the relation `trace = ±t`. -/
structure CMOutput (F : Type*) [Field F] [Fintype F] [DecidableEq F] where
  curve : WeierstrassCurve.Affine F
  trace : ℤ
  frob_trace_eq : Hasse.traceFrobenius curve = trace ∨
                  Hasse.traceFrobenius curve = -trace

end CMMethod

namespace ProperIdealNormCount

open Elliptic_Curves






end ProperIdealNormCount

namespace RingClassFieldRamification

open Elliptic_Curves




end RingClassFieldRamification

namespace ImagQuadPrimeSplitting

open Elliptic_Curves

/-- Roots in `ZMod p` of the minimal polynomial of `ω = (D + √D)/2` (or
`√D`) for the imaginary quadratic discriminant `D`. -/
noncomputable def rootsMinPolyMod (D : ℤ) (p : ℕ) [Fact (Nat.Prime p)] : Finset (ZMod p) :=
  if D % 4 = 1 then
    Finset.univ.filter (fun x : ZMod p => x ^ 2 - x + ((1 - D) / 4 : ℤ) = 0)
  else
    Finset.univ.filter (fun x : ZMod p => x ^ 2 + ((-D / 4 : ℤ) : ZMod p) = 0)

/-- The number of `𝒪_K`-ideals of norm `p`, counted by the roots of the
minimal polynomial of `ω` modulo `p`. -/
noncomputable def numIdealsOfNorm (D : ℤ) (p : ℕ) [Fact (Nat.Prime p)] : ℤ :=
  (rootsMinPolyMod D p).card

/-- In `ZMod 2`, for any constant `c`, the equation `x^2 + c = 0` has exactly
one solution. -/
lemma card_filter_sq_add_eq_zero_ZMod2 (c : ZMod 2) :
    (Finset.univ.filter (fun x : ZMod 2 => x ^ 2 + c = 0)).card = 1 := by
  revert c; decide

/-- In `ZMod 2`, the equation `x^2 - x + c = 0` has `2` solutions if `c = 0`
and none otherwise. -/
lemma card_filter_sq_sub_x_add_ZMod2 (c : ZMod 2) :
    (Finset.univ.filter (fun x : ZMod 2 => x ^ 2 - x + c = 0)).card =
      if c = 0 then 2 else 0 := by
  revert c; decide

/-- Lemma 21.6 (Sutherland, ideal-counting version): the number of
`𝒪_K`-ideals of norm `p` equals `1 + (D/p)`. -/
theorem numIdealsOfNorm_eq_one_add_kroneckerSymbol (D : ℤ) (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hD : IsImagQuadDiscriminant D) :
    numIdealsOfNorm D p = 1 + kroneckerSymbol p D := by
  obtain ⟨hDneg, hDmod⟩ := hD
  by_cases hp2 : p = 2
  ·
    subst hp2
    unfold numIdealsOfNorm rootsMinPolyMod kroneckerSymbol
    rcases hDmod with hD0 | hD1
    ·
      have hDeven : D % 2 = 0 := by omega
      have hD_not1 : ¬(D % 4 = 1) := by omega
      simp only [hD_not1, ite_false, hDeven, ite_true]
      rw [card_filter_sq_add_eq_zero_ZMod2]; norm_cast
    ·
      have hDodd : ¬(D % 2 = 0) := by omega
      simp only [hD1, ite_true, hDodd, ite_false]
      have hDmod8 : D % 8 = 1 ∨ D % 8 = 5 := by omega
      rcases hDmod8 with h8_1 | h8_5
      · have hc0 : ((((1 - D) / 4 : ℤ) : ZMod 2) = 0) := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Int.dvd_of_emod_eq_zero (by omega)
        rw [card_filter_sq_sub_x_add_ZMod2, if_pos hc0]
        have : D % 8 = 1 ∨ D % 8 = 7 := Or.inl h8_1
        simp [this]
      · have hc1 : ((((1 - D) / 4 : ℤ) : ZMod 2) ≠ 0) := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; intro ⟨k, hk⟩; omega
        rw [card_filter_sq_sub_x_add_ZMod2, if_neg hc1]
        have : ¬(D % 8 = 1 ∨ D % 8 = 7) := by omega
        simp [this]
  ·
    have hodd : p ≠ 2 := hp2
    rw [kroneckerSymbol_odd_prime hodd]
    have hprime : Nat.Prime p := hp.out
    have hcard_sqrts := legendreSym.card_sqrts p hodd D
    suffices h : (rootsMinPolyMod D p).card = {x : ZMod p | x ^ 2 = (D : ZMod p)}.toFinset.card by
      rw [numIdealsOfNorm, h]; linarith
    have h2inv : IsUnit (2 : ZMod p) :=
      ZMod.isUnit_prime_of_not_dvd Nat.prime_two
        (fun h => hodd (hprime.eq_one_or_self_of_dvd 2 h |>.resolve_left (by omega) |>.symm))
    have h2ne : (2 : ZMod p) ≠ 0 := IsUnit.ne_zero h2inv
    have h4_ne : (4 : ZMod p) ≠ 0 := by
      have : IsUnit (4 : ZMod p) := by
        rw [show (4 : ZMod p) = 2 * 2 from by norm_num]; exact h2inv.mul h2inv
      exact IsUnit.ne_zero this
    obtain ⟨u, hu⟩ := h2inv


    have h2u_inv : (2 : ZMod p) * ↑u⁻¹ = 1 := by
      rw [← hu]; exact_mod_cast u.mul_inv

    rcases hDmod with hD0 | hD1
    ·
      simp only [rootsMinPolyMod, show ¬(D % 4 = 1) from by omega, ite_false]
      have h4_cast : (4 : ZMod p) * ((-D / 4 : ℤ) : ZMod p) = ((-D : ℤ) : ZMod p) := by
        rw [← Int.cast_ofNat, ← Int.cast_mul]; congr 1; omega
      have h_fwd : ∀ x : ZMod p, x ^ 2 + ((-D / 4 : ℤ) : ZMod p) = 0 →
          (2 * x) ^ 2 = (D : ZMod p) := by
        intro x hx
        have : (2 * x) ^ 2 = 4 * (x ^ 2 + ((-D / 4 : ℤ) : ZMod p)) + (D : ZMod p) := by
          rw [show (2 * x) ^ 2 = 4 * x ^ 2 from by ring, mul_add, h4_cast]; push_cast; ring
        rw [hx, mul_zero, zero_add] at this; exact this
      have h_bwd : ∀ y : ZMod p, y ^ 2 = (D : ZMod p) →
          (↑u⁻¹ * y) ^ 2 + ((-D / 4 : ℤ) : ZMod p) = 0 := by
        intro y hy
        have : (4 : ZMod p) * ((↑u⁻¹ * y) ^ 2 + ((-D / 4 : ℤ) : ZMod p)) = 0 := by
          have h4u : (4 : ZMod p) * (↑u⁻¹ * y) ^ 2 = y ^ 2 := by
            rw [show (4 : ZMod p) * (↑u⁻¹ * y) ^ 2 = (2 * ↑u⁻¹) ^ 2 * y ^ 2 from by ring]
            rw [h2u_inv, one_pow, one_mul]
          rw [mul_add, h4u, h4_cast, hy]; push_cast; ring
        exact (mul_eq_zero.mp this).resolve_left h4_ne
      apply Finset.card_bij (fun x _ => 2 * x)
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_fwd x hx
      · intro x₁ _ x₂ _ h; exact mul_left_cancel₀ h2ne h
      · intro y hy
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨↑u⁻¹ * y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_bwd y hy⟩,
          by rw [show (2 : ZMod p) * (↑u⁻¹ * y) = (2 * ↑u⁻¹) * y from by ring, h2u_inv, one_mul]⟩
    ·
      simp only [rootsMinPolyMod, show D % 4 = 1 from hD1, ite_true]
      have h4_cast : (4 : ZMod p) * (((1 - D) / 4 : ℤ) : ZMod p) = ((1 - D : ℤ) : ZMod p) := by
        rw [← Int.cast_ofNat, ← Int.cast_mul]; congr 1; omega
      have h_fwd : ∀ x : ZMod p, x ^ 2 - x + ((1 - D) / 4 : ℤ) = 0 →
          (2 * x - 1) ^ 2 = (D : ZMod p) := by
        intro x hx
        have : (2 * x - 1) ^ 2 = 4 * (x ^ 2 - x + ((1 - D) / 4 : ℤ)) + (D : ZMod p) := by
          rw [show (2 * x - 1) ^ 2 = 4 * x ^ 2 - 4 * x + 1 from by ring,
              show (4 : ZMod p) * (x ^ 2 - x + ((1 - D) / 4 : ℤ)) =
                4 * x ^ 2 - 4 * x + 4 * ((1 - D) / 4 : ℤ) from by ring,
              h4_cast]; push_cast; ring
        rw [hx, mul_zero, zero_add] at this; exact this
      have h_bwd : ∀ y : ZMod p, y ^ 2 = (D : ZMod p) →
          (↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ) = 0 := by
        intro y hy
        have key : 2 * (↑u⁻¹ * (y + 1)) - 1 = y := by
          rw [show (2 : ZMod p) * (↑u⁻¹ * (y + 1)) = (2 * ↑u⁻¹) * (y + 1) from by ring]
          rw [h2u_inv, one_mul, add_sub_cancel_right]
        have h1 : (2 * (↑u⁻¹ * (y + 1)) - 1) ^ 2 =
            4 * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) + (D : ZMod p) := by
          rw [show (2 * (↑u⁻¹ * (y + 1)) - 1) ^ 2 =
              4 * (↑u⁻¹ * (y + 1)) ^ 2 - 4 * (↑u⁻¹ * (y + 1)) + 1 from by ring,
              show (4 : ZMod p) * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) =
                4 * (↑u⁻¹ * (y + 1)) ^ 2 - 4 * (↑u⁻¹ * (y + 1)) + 4 * ((1 - D) / 4 : ℤ) from by ring,
              h4_cast]; push_cast; ring
        rw [key, hy] at h1

        have h2 : (4 : ZMod p) * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) = 0 := by
          have : (D : ZMod p) - (D : ZMod p) =
            4 * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) + (D : ZMod p) - (D : ZMod p) := by
            rw [← h1]
          simp only [sub_self, add_sub_cancel_right] at this
          exact this.symm
        exact (mul_eq_zero.mp h2).resolve_left h4_ne
      apply Finset.card_bij (fun x _ => 2 * x - 1)
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_fwd x hx
      · intro x₁ _ x₂ _ h
        have : 2 * x₁ = 2 * x₂ := by linear_combination h
        exact mul_left_cancel₀ h2ne this
      · intro y hy
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨↑u⁻¹ * (y + 1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_bwd y hy⟩,
          by rw [show (2 : ZMod p) * (↑u⁻¹ * (y + 1)) = (2 * ↑u⁻¹) * (y + 1) from by ring,
             h2u_inv, one_mul, add_sub_cancel_right]⟩

end ImagQuadPrimeSplitting

namespace ImagQuadPrimeFactorization

open Elliptic_Curves ProperIdealInvertible

variable {d : ℤ}

/-- The prime ideal `𝔭 = (p, ω - r)` in `ℤ[√d]` above a rational prime `p`
and a root `r` of `x² + d ≡ 0 mod p`, used in Lemma 21.6. -/
def primeIdealAbove (p : ℕ) (r : ℤ) : Ideal (ℤ√d) :=
  Ideal.span {(p : ℤ√d), (⟨-r, 1⟩ : ℤ√d)}









end ImagQuadPrimeFactorization

namespace ImagQuadPrimeSplitting.IdealRootBijection

open Elliptic_Curves ImagQuadPrimeSplitting




end ImagQuadPrimeSplitting.IdealRootBijection

namespace CMMethod.TwistSelection

open Elliptic_Curves

/-- Given an elliptic curve `E/F` with Frobenius trace `±t`, either `E` itself
or its quadratic twist has exactly `|F| + 1 - t` points. This is the twist
selection step in the CM method. -/
theorem exists_curve_or_twist_with_order
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (t : ℤ)
    (hfrob : Hasse.traceFrobenius E = t ∨ Hasse.traceFrobenius E = -t)
    (hE : Hasse.numPoints E ≤ 2 * Fintype.card F + 2) :
    (Hasse.numPoints E : ℤ) = (Fintype.card F : ℤ) + 1 - t ∨
    (QuadraticTwist.twistNumPoints E : ℤ) = (Fintype.card F : ℤ) + 1 - t := by
  rcases hfrob with h | h
  ·
    left
    have := Hasse.numPoints_eq_card_sub_trace E
    linarith
  ·
    right
    have hadd := QuadraticTwist.numPoints_add_twist E hE
    have hnum := Hasse.numPoints_eq_card_sub_trace E
    omega

end CMMethod.TwistSelection
