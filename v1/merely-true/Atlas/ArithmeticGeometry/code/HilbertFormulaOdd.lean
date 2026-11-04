/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.HilbertSymbol
import Atlas.ArithmeticGeometry.code.HenselsLemma
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

open HilbertSymbol

noncomputable section

/-- Symmetry of the Hilbert symbol: $(a, b)_F = (b, a)_F$, since the equation
$ax^2 + by^2 = 1$ is equivalent to $by^2 + ax^2 = 1$. -/
theorem hilbert_symm {F : Type*} [Field F] (a b : Fˣ) :
    hilbertSymbol F a b = hilbertSymbol F b a := by
  unfold hilbertSymbol
  have h : HilbertSymbol.IsSolvable F a b ↔ HilbertSymbol.IsSolvable F b a := by
    constructor
    · rintro ⟨x, y, h⟩
      exact ⟨y, x, by rw [add_comm]; exact h⟩
    · rintro ⟨x, y, h⟩
      exact ⟨y, x, by rw [add_comm]; exact h⟩
  congr 1 <;> exact propext h

/-- Bilinearity in the second argument when $(a, b)_F = 1$: in that case,
$(a, bc)_F = (a, c)_F$. Follows from symmetry and `hilbert_mul_of_eq_one`. -/
theorem hilbert_mul_right_of_eq_one {F : Type*} [Field F] [CharZero F]
    (a b c : Fˣ) (h : hilbertSymbol F a b = 1) :
    hilbertSymbol F a (b * c) = hilbertSymbol F a c := by
  have h' : hilbertSymbol F b a = 1 := by rwa [hilbert_symm]
  have key := hilbertSymbol.hilbert_mul_of_eq_one b c a h'
  rw [h', one_mul] at key
  rw [hilbert_symm a (b * c), key.symm, hilbert_symm]

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The prime $p$ viewed as a unit in $\mathbb{Q}_p^\times$. -/
noncomputable def qpPrime (p : ℕ) [Fact (Nat.Prime p)] : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))

/-- The Legendre symbol $\left(\frac{v}{p}\right)$ of a $p$-adic unit $v \in \mathbb{Z}_p^\times$,
computed via the reduction mod $p$. -/
def padicUnitLegendre (v : ℤ_[p]ˣ) : ℤ :=
  legendreSym p (ZMod.val (PadicInt.toZMod (v : ℤ_[p])) : ℤ)

/-- A "primitive-unit" representative $p^\alpha \cdot u \in \mathbb{Q}_p^\times$
with exponent $\alpha \in \{0, 1\}$ and $u$ a $p$-adic integer unit. -/
noncomputable def padicPowerUnit (p : ℕ) [Fact (Nat.Prime p)]
    (α : Fin 2) (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  (qpPrime p) ^ (α : ℕ) * unitZpToQp u

/-- The image of $p$ under the reduction map $\mathbb{Z}_p \to \mathbb{Z}/p$ is zero. -/
lemma toZMod_p_eq_zero : PadicInt.toZMod (↑p : ℤ_[p]) = 0 :=
  RingHom.mem_ker.mp (by rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton])

/-- For $x \in \mathbb{Z}_p$: $\|x\| < 1$ iff $x \equiv 0 \pmod{p}$. -/
lemma norm_lt_one_iff_toZMod_zero (x : ℤ_[p]) :
    ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [PadicInt.norm_lt_one_iff_dvd]
  exact ⟨fun h => RingHom.mem_ker.mp (by rw [PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]; exact h),
    fun h => by have := RingHom.mem_ker.mpr h; rw [PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this; exact this⟩

/-- For $x \in \mathbb{Z}_p$: $x$ is a unit iff its reduction mod $p$ is non-zero. -/
lemma isUnit_iff_toZMod_ne_zero (x : ℤ_[p]) :
    IsUnit x ↔ PadicInt.toZMod x ≠ 0 := by
  constructor
  · intro hu h; linarith [PadicInt.isUnit_iff.mp hu, (norm_lt_one_iff_toZMod_zero x).mpr h]
  · intro h; rw [PadicInt.isUnit_iff]
    exact le_antisymm (by exact_mod_cast x.2) (not_lt.mp (fun hlt =>
      h ((norm_lt_one_iff_toZMod_zero x).mp hlt)))

/-- For $x \in \mathbb{Z}_p$: $p \mid x$ iff $x \equiv 0 \pmod p$. -/
lemma dvd_iff_toZMod_zero (x : ℤ_[p]) :
    (↑p : ℤ_[p]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← PadicInt.norm_lt_one_iff_dvd, norm_lt_one_iff_toZMod_zero]

/-- The natural number value of $\bar v \in \mathbb{Z}/p$, viewed back in $\mathbb{Z}/p$,
recovers $\bar v$ itself. Used to compute the Legendre symbol. -/
lemma legendreSym_val_eq (v : ℤ_[p]ˣ) :
    (ZMod.val (PadicInt.toZMod (v : ℤ_[p])) : ZMod p) = PadicInt.toZMod (v : ℤ_[p]) := by
  rw [ZMod.natCast_val]; simp

/-- The integer representative of $v \bmod p$ is non-zero in $\mathbb{Z}/p$
(since $v$ is a unit, its reduction is non-zero). -/
lemma padicUnitLegendre_ne_zero (v : ℤ_[p]ˣ) :
    (ZMod.val (PadicInt.toZMod (v : ℤ_[p])) : ZMod p) ≠ 0 := by
  rw [legendreSym_val_eq]
  exact (RingHom.isUnit_map PadicInt.toZMod v.isUnit).ne_zero

set_option maxHeartbeats 1600000 in
/-- (Textbook Lemma 10.8) For an odd prime $p$ and $v \in \mathbb{Z}_p^\times$,
the Hilbert symbol $(p, v)_p$ equals the Legendre symbol $\left(\frac{v}{p}\right)$. -/
theorem hilbert_p_unit_eq_legendre (hp_odd : p ≠ 2) (v : ℤ_[p]ˣ) :
    padicHilbertSymbol p (qpPrime p) (unitZpToQp v) = padicUnitLegendre v := by
  have hne_nat : (ZMod.val (PadicInt.toZMod (v : ℤ_[p])) : ZMod p) ≠ 0 :=
    padicUnitLegendre_ne_zero v
  have hne : ((ZMod.val (PadicInt.toZMod (v : ℤ_[p])) : ℤ) : ZMod p) ≠ 0 := by
    rwa [Int.cast_natCast]
  rcases legendreSym.eq_one_or_neg_one p hne with hleg | hleg <;>
    simp only [padicUnitLegendre, hleg]
  ·
    rw [padicHilbertSymbol.eq_one_iff]
    rw [legendreSym.eq_one_iff p hne] at hleg
    rw [show ((ZMod.val (PadicInt.toZMod (v : ℤ_[p])) : ℤ) : ZMod p) =
         PadicInt.toZMod (v : ℤ_[p]) from by rw [Int.cast_natCast]; exact legendreSym_val_eq v] at hleg
    obtain ⟨w, hw⟩ := hleg
    obtain ⟨w_lift, hw_lift⟩ := ZMod.ringHom_surjective PadicInt.toZMod w
    let f : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C (v : ℤ_[p])
    have hf_aeval : Polynomial.aeval w_lift f = w_lift ^ 2 - (v : ℤ_[p]) := by
      simp [f, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    have hval : ‖Polynomial.aeval w_lift f‖ < 1 := by
      rw [hf_aeval, norm_lt_one_iff_toZMod_zero, map_sub, map_pow, hw_lift]
      rw [show PadicInt.toZMod (v : ℤ_[p]) = w * w from hw]
      ring
    have hw_unit : IsUnit w_lift := by
      rw [isUnit_iff_toZMod_ne_zero]; intro h0
      have : PadicInt.toZMod (v : ℤ_[p]) = 0 := by
        rw [hw, ← hw_lift, h0]; ring
      exact (isUnit_iff_toZMod_ne_zero _).mp v.isUnit this
    have hderiv : ‖Polynomial.aeval w_lift f.derivative‖ = 1 := by
      have hf_deriv : Polynomial.aeval w_lift f.derivative = 2 * w_lift := by
        simp [f, Polynomial.derivative_sub, Polynomial.derivative_pow,
              Polynomial.derivative_X, Polynomial.derivative_C,
              Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      rw [hf_deriv, norm_mul]
      have h2_unit : IsUnit (2 : ℤ_[p]) := by
        rw [PadicInt.isUnit_iff]; by_contra hne2; push_neg at hne2
        have hlt2 : ‖(2 : ℤ_[p])‖ < 1 := lt_of_le_of_ne (2 : ℤ_[p]).2 hne2
        rw [PadicInt.norm_lt_one_iff_dvd] at hlt2; obtain ⟨k, hk⟩ := hlt2
        have h1 := congrArg PadicInt.toZMod hk
        simp only [map_ofNat, map_mul] at h1
        rw [toZMod_p_eq_zero, zero_mul] at h1
        have : (2 : ZMod p) ≠ 0 := by
          rw [Ne, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by norm_cast,
              ZMod.natCast_eq_zero_iff]; intro hdvd
          exact hp_odd (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) (Nat.Prime.two_le hp.out))
        exact this h1
      rw [PadicInt.isUnit_iff.mp h2_unit, PadicInt.isUnit_iff.mp hw_unit, mul_one]
    obtain ⟨z, hz_root, _⟩ := (hensel_lemma_norm f w_lift hval hderiv).exists
    have hz_sq : z ^ 2 = (v : ℤ_[p]) := by
      have h := hz_root
      simp [f, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h
      exact sub_eq_zero.mp h
    have hz_unit : IsUnit z := by
      rw [isUnit_iff_toZMod_ne_zero]; intro h0
      have : PadicInt.toZMod (v : ℤ_[p]) = 0 := by
        have h2 := congrArg PadicInt.toZMod hz_sq
        rw [map_pow, h0, zero_pow (by norm_num : 2 ≠ 0)] at h2; exact h2.symm
      exact (isUnit_iff_toZMod_ne_zero _).mp v.isUnit this
    let z_unit := hz_unit.unit
    refine ⟨0, ((unitZpToQp z_unit)⁻¹ : ℚ_[p]), ?_⟩
    simp only [mul_zero, sq (0 : ℚ_[p]), zero_mul, zero_add]

    have hz_ne : ((unitZpToQp z_unit : ℚ_[p]ˣ) : ℚ_[p]) ≠ 0 := Units.ne_zero _
    have hz_zu_eq : (z_unit : ℤ_[p]) = z := by
      exact hz_unit.unit_spec
    have hz_sq_qp : ((z_unit : ℤ_[p]) : ℚ_[p]) ^ 2 = ((v : ℤ_[p]) : ℚ_[p]) := by
      have h := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hz_sq
      simp only [map_pow] at h
      rw [hz_zu_eq]; exact h
    rw [unitZpToQp_coe]


    field_simp
    exact hz_sq_qp.symm

  ·
    rw [padicHilbertSymbol.eq_neg_one_iff]

    rw [legendreSym.eq_neg_one_iff] at hleg
    rw [show ((ZMod.val (PadicInt.toZMod (v : ℤ_[p])) : ℤ) : ZMod p) =
         PadicInt.toZMod (v : ℤ_[p]) from by rw [Int.cast_natCast]; exact legendreSym_val_eq v] at hleg
    intro ⟨x, y, hsolv⟩
    have hsolvable : IsSolvable ℚ_[p] (qpPrime p) (unitZpToQp v) := ⟨x, y, hsolv⟩
    rw [isSolvable_iff_hasPrimitiveSolution] at hsolvable
    obtain ⟨x₀, y₀, z₀, hunit, heq⟩ := hsolvable


    have heq_zp : (p : ℤ_[p]) * x₀ ^ 2 + (v : ℤ_[p]) * y₀ ^ 2 = z₀ ^ 2 := by
      apply Subtype.coe_injective
      push_cast
      convert heq using 2 <;> simp [qpPrime, unitZpToQp_coe]
    have heq_mod : PadicInt.toZMod (v : ℤ_[p]) * (PadicInt.toZMod y₀) ^ 2 =
                   (PadicInt.toZMod z₀) ^ 2 := by

      have := congrArg PadicInt.toZMod heq_zp
      simp only [map_add, map_mul, map_pow] at this
      rw [toZMod_p_eq_zero, zero_mul, zero_add] at this; exact this
    by_cases hy_unit : IsUnit y₀
    ·
      apply hleg
      have hy_mod_ne : PadicInt.toZMod y₀ ≠ 0 :=
        (isUnit_iff_toZMod_ne_zero _).mp hy_unit
      refine ⟨PadicInt.toZMod z₀ * (PadicInt.toZMod y₀)⁻¹, ?_⟩


      have : PadicInt.toZMod (v : ℤ_[p]) = (PadicInt.toZMod z₀) ^ 2 * ((PadicInt.toZMod y₀) ^ 2)⁻¹ := by
        field_simp
        exact heq_mod
      rw [this]
      ring

    ·
      have hy_mod_zero : PadicInt.toZMod y₀ = 0 := by
        by_contra h; exact hy_unit ((isUnit_iff_toZMod_ne_zero _).mpr h)
      have hz_mod_zero : PadicInt.toZMod z₀ = 0 := by
        have : (PadicInt.toZMod z₀) ^ 2 = 0 := by
          rw [← heq_mod, hy_mod_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
        rwa [sq, mul_self_eq_zero] at this
      have hz_not_unit : ¬IsUnit z₀ := by
        intro h; exact (isUnit_iff_toZMod_ne_zero _).mp h hz_mod_zero
      have hx_unit : IsUnit x₀ := by
        rcases hunit with h | h | h
        · exact h
        · exact absurd h hy_unit
        · exact absurd h hz_not_unit
      have hy_dvd : (↑p : ℤ_[p]) ∣ y₀ := (dvd_iff_toZMod_zero y₀).mpr hy_mod_zero
      have hz_dvd : (↑p : ℤ_[p]) ∣ z₀ := (dvd_iff_toZMod_zero z₀).mpr hz_mod_zero
      obtain ⟨y₁, rfl⟩ := hy_dvd
      obtain ⟨z₁, rfl⟩ := hz_dvd
      have hp_ne : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast Nat.Prime.ne_zero hp.out


      have heq_expand : (p : ℤ_[p]) * x₀ ^ 2 + (v : ℤ_[p]) * ((p : ℤ_[p]) ^ 2 * y₁ ^ 2) =
          (p : ℤ_[p]) ^ 2 * z₁ ^ 2 := by
        have := heq_zp; rw [mul_pow, mul_pow] at this; ring_nf; ring_nf at this; exact this
      have heq_cancel : x₀ ^ 2 = (p : ℤ_[p]) * (z₁ ^ 2 - (v : ℤ_[p]) * y₁ ^ 2) := by
        have h1 : (p : ℤ_[p]) * x₀ ^ 2 = (p : ℤ_[p]) ^ 2 * z₁ ^ 2 - (v : ℤ_[p]) * (p : ℤ_[p]) ^ 2 * y₁ ^ 2 := by
          linear_combination heq_expand
        have h2 : (p : ℤ_[p]) * x₀ ^ 2 = (p : ℤ_[p]) * ((p : ℤ_[p]) * z₁ ^ 2 - (v : ℤ_[p]) * (p : ℤ_[p]) * y₁ ^ 2) := by
          rw [h1]; ring
        exact mul_left_cancel₀ hp_ne (by rw [h2]; ring)

      have hp_dvd_xsq : (↑p : ℤ_[p]) ∣ x₀ ^ 2 := ⟨_, heq_cancel⟩
      have hp_dvd_x : (↑p : ℤ_[p]) ∣ x₀ := by
        rw [sq] at hp_dvd_xsq
        exact (PadicInt.prime_p (p := p)).dvd_or_dvd hp_dvd_xsq |>.elim id id
      have hx_norm := PadicInt.isUnit_iff.mp hx_unit
      have hx_lt : ‖x₀‖ < 1 := (PadicInt.norm_lt_one_iff_dvd x₀).mpr hp_dvd_x
      linarith

/-- (Textbook Theorem 10.7, exponents in $\{0, 1\}$) For an odd prime $p$,
exponents $\alpha, \beta \in \{0, 1\}$, and units $u, v \in \mathbb{Z}_p^\times$,
the Hilbert symbol of $p^\alpha u$ and $p^\beta v$ is given by
$$(p^\alpha u, p^\beta v)_p = (-1)^{\alpha\beta \cdot \frac{p-1}{2}}
  \left(\tfrac{u}{p}\right)^\beta \left(\tfrac{v}{p}\right)^\alpha.$$ -/
theorem hilbert_formula_odd (hp_odd : p ≠ 2)
    (α β : Fin 2) (u v : ℤ_[p]ˣ) :
    padicHilbertSymbol p (padicPowerUnit p α u) (padicPowerUnit p β v) =
    (-1 : ℤ) ^ ((α : ℕ) * (β : ℕ) * ((p - 1) / 2)) *
    padicUnitLegendre u ^ (β : ℕ) *
    padicUnitLegendre v ^ (α : ℕ) := by
  fin_cases α <;> fin_cases β <;> simp only [
    Nat.zero_mul, Nat.mul_zero, pow_zero, mul_one, one_mul,
    padicPowerUnit]

  · exact hilbert_symbol_units_eq_one_of_odd p hp_odd u v

  ·
    simp only [pow_one, padicHilbertSymbol]
    rw [hilbert_symm]


    have hvu : hilbertSymbol ℚ_[p] (unitZpToQp v) (unitZpToQp u) = 1 := by
      rw [← padicHilbertSymbol]
      exact hilbert_symbol_units_eq_one_of_odd p hp_odd v u
    have key := hilbertSymbol.hilbert_mul_of_eq_one
      (unitZpToQp v) (qpPrime p) (unitZpToQp u) hvu
    rw [show (qpPrime p * unitZpToQp v : ℚ_[p]ˣ) = unitZpToQp v * qpPrime p from mul_comm _ _]
    rw [← key, hvu, one_mul]
    exact hilbert_p_unit_eq_legendre hp_odd u

  ·


    simp only [pow_one]
    have huv : padicHilbertSymbol p (unitZpToQp u) (unitZpToQp v) = 1 :=
      hilbert_symbol_units_eq_one_of_odd p hp_odd u v
    have key := hilbertSymbol.hilbert_mul_of_eq_one
      (unitZpToQp u) (qpPrime p) (unitZpToQp v)
      (by rw [padicHilbertSymbol] at huv; exact huv)
    simp only [padicHilbertSymbol]
    rw [show (qpPrime p * unitZpToQp u : ℚ_[p]ˣ) = unitZpToQp u * qpPrime p from mul_comm _ _]
    rw [← key]
    rw [show hilbertSymbol ℚ_[p] (unitZpToQp u) (unitZpToQp v) = 1 from by
      rw [padicHilbertSymbol] at huv; exact huv]
    rw [one_mul]
    exact hilbert_p_unit_eq_legendre hp_odd v

  · simp only [pow_one, padicHilbertSymbol]


    let pu := qpPrime p * unitZpToQp u
    let pv := qpPrime p * unitZpToQp v

    have h_neg_pu : hilbertSymbol ℚ_[p] pu (-(pu)) = 1 := by
      rw [hilbert_symm]; exact hilbertSymbol.hilbert_neg_self pu


    have hpv_factor : pv = -(pu) * (-(unitZpToQp (u⁻¹ * v))) := by
      show qpPrime p * unitZpToQp v =
        -(qpPrime p * unitZpToQp u) * -(unitZpToQp (u⁻¹ * v))
      simp only [neg_mul_neg]
      rw [show unitZpToQp (u⁻¹ * v) = unitZpToQp u⁻¹ * unitZpToQp v from map_mul _ _ _]
      rw [show (unitZpToQp u⁻¹ : ℚ_[p]ˣ) = (unitZpToQp u)⁻¹ from map_inv _ _]
      group

    rw [show (qpPrime p * unitZpToQp v : ℚ_[p]ˣ) = pv from rfl]
    rw [hpv_factor]
    rw [hilbert_mul_right_of_eq_one pu (-(pu)) (-(unitZpToQp (u⁻¹ * v))) h_neg_pu]

    have h_neg_unit : -(unitZpToQp (u⁻¹ * v)) = unitZpToQp (-(u⁻¹ * v)) := by
      ext; simp [unitZpToQp, map_neg, map_mul, map_inv]
    rw [h_neg_unit]

    rw [show hilbertSymbol ℚ_[p] pu (unitZpToQp (-(u⁻¹ * v))) =
      padicHilbertSymbol p (qpPrime p * unitZpToQp u) (unitZpToQp (-(u⁻¹ * v))) from rfl]

    have huv' : padicHilbertSymbol p (unitZpToQp u) (unitZpToQp (-(u⁻¹ * v))) = 1 :=
      hilbert_symbol_units_eq_one_of_odd p hp_odd u (-(u⁻¹ * v))
    have key10 := hilbertSymbol.hilbert_mul_of_eq_one
      (unitZpToQp u) (qpPrime p) (unitZpToQp (-(u⁻¹ * v)))
      (by rw [padicHilbertSymbol] at huv'; exact huv')
    simp only [padicHilbertSymbol]
    rw [show (qpPrime p * unitZpToQp u : ℚ_[p]ˣ) = unitZpToQp u * qpPrime p from mul_comm _ _]
    rw [← key10]
    rw [show hilbertSymbol ℚ_[p] (unitZpToQp u) (unitZpToQp (-(u⁻¹ * v))) = 1 from by
      rw [padicHilbertSymbol] at huv'; exact huv']
    rw [one_mul]


    rw [← padicHilbertSymbol, hilbert_p_unit_eq_legendre hp_odd (-(u⁻¹ * v))]


    show padicUnitLegendre (-(u⁻¹ * v)) =
      (-1 : ℤ) ^ ((p - 1) / 2) * padicUnitLegendre u * padicUnitLegendre v


    have legendre_eq_qchar : ∀ (w : ℤ_[p]ˣ),
        padicUnitLegendre w = quadraticChar (ZMod p) (PadicInt.toZMod (w : ℤ_[p])) := by
      intro w
      unfold padicUnitLegendre legendreSym
      congr 1
      rw [Int.cast_natCast, ZMod.natCast_val]
      simp
    rw [legendre_eq_qchar, legendre_eq_qchar u, legendre_eq_qchar v]


    have htoZMod_neg_inv_mul :
        PadicInt.toZMod ((-(u⁻¹ * v) : ℤ_[p]ˣ) : ℤ_[p]) =
        -(PadicInt.toZMod (u : ℤ_[p]))⁻¹ * PadicInt.toZMod (v : ℤ_[p]) := by
      rw [Units.val_neg, map_neg, Units.val_mul, map_mul]
      have h_inv : PadicInt.toZMod ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = (PadicInt.toZMod (u : ℤ_[p]))⁻¹ := by
        have h_mul_eq_one : PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
          rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
        exact (inv_eq_of_mul_eq_one_right h_mul_eq_one).symm
      rw [h_inv, neg_mul]
    rw [htoZMod_neg_inv_mul]


    have htu_ne : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 :=
      (RingHom.isUnit_map PadicInt.toZMod u.isUnit).ne_zero
    rw [show -(PadicInt.toZMod (u : ℤ_[p]))⁻¹ * PadicInt.toZMod (v : ℤ_[p]) =
        (-1) * (PadicInt.toZMod (u : ℤ_[p]))⁻¹ * PadicInt.toZMod (v : ℤ_[p]) from by ring]
    rw [map_mul (quadraticChar (ZMod p)) ((-1) * _) _, map_mul (quadraticChar (ZMod p)) (-1) _]

    have h_inv_eq : quadraticChar (ZMod p) (PadicInt.toZMod (u : ℤ_[p]))⁻¹ =
        quadraticChar (ZMod p) (PadicInt.toZMod (u : ℤ_[p])) := by
      have h1 : quadraticChar (ZMod p) (PadicInt.toZMod (u : ℤ_[p]) *
          (PadicInt.toZMod (u : ℤ_[p]))⁻¹) = 1 := by
        rw [mul_inv_cancel₀ htu_ne, map_one]
      rw [map_mul] at h1
      rcases (quadraticChar_isQuadratic (ZMod p)) (PadicInt.toZMod (u : ℤ_[p])) with h | h | h <;>
        rcases (quadraticChar_isQuadratic (ZMod p)) (PadicInt.toZMod (u : ℤ_[p]))⁻¹ with h' | h' | h' <;>
        simp_all
    rw [h_inv_eq]

    have h_neg1 : quadraticChar (ZMod p) (-1) = (-1 : ℤ) ^ ((p - 1) / 2) := by
      have hp_mod : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp_odd)
      rw [show quadraticChar (ZMod p) (-1 : ZMod p) =
        quadraticChar (ZMod p) ((-1 : ℤ) : ZMod p) from by push_cast; ring_nf]
      change legendreSym p (-1) = _
      rw [legendreSym.at_neg_one hp_odd, ZMod.χ₄_eq_neg_one_pow hp_mod]
      congr 1
      have : p ≥ 2 := hp.out.two_le
      omega
    rw [h_neg1, mul_assoc]

/-- A "primitive-unit" representative $p^\alpha \cdot u \in \mathbb{Q}_p^\times$
with integer exponent $\alpha \in \mathbb{Z}$ (allowing both positive and negative powers of $p$). -/
noncomputable def padicPowerUnitZ (p : ℕ) [Fact (Nat.Prime p)]
    (α : ℤ) (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  (qpPrime p) ^ α * unitZpToQp u

/-- The Hilbert symbol is trivial on squares: $(s^2, b)_p = 1$ for any $s, b$. -/
lemma hilbert_sq_left (s b : ℚ_[p]ˣ) :
    hilbertSymbol ℚ_[p] (s ^ 2) b = 1 := by
  rw [hilbertSymbol.eq_one_iff]
  exact ⟨(s⁻¹ : ℚ_[p]ˣ), 0, by
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
    ring⟩

/-- Square-invariance of the Hilbert symbol in the first argument:
$(s^2 \cdot a, b)_p = (a, b)_p$. -/
lemma hilbert_sq_mul_left (s a b : ℚ_[p]ˣ) :
    hilbertSymbol ℚ_[p] (s ^ 2 * a) b = hilbertSymbol ℚ_[p] a b := by
  have hsq : hilbertSymbol ℚ_[p] (s ^ 2) b = 1 := hilbert_sq_left s b
  have key := hilbertSymbol.hilbert_mul_of_eq_one (s ^ 2) a b hsq
  rw [hsq, one_mul] at key
  exact key.symm

/-- Square-invariance of the Hilbert symbol in the second argument:
$(a, s^2 \cdot b)_p = (a, b)_p$. -/
lemma hilbert_sq_mul_right (s a b : ℚ_[p]ˣ) :
    hilbertSymbol ℚ_[p] a (s ^ 2 * b) = hilbertSymbol ℚ_[p] a b := by
  rw [hilbert_symm a (s ^ 2 * b), hilbert_sq_mul_left, hilbert_symm]

/-- The natural number $(α \bmod 2).\text{toNat}$ is strictly less than $2$. -/
lemma int_emod_two_toNat_lt (α : ℤ) : (α % 2).toNat < 2 := by
  rcases Int.emod_two_eq_zero_or_one α with h | h <;> simp [h]

/-- Reduces a `padicPowerUnitZ` (integer exponent) to a `padicPowerUnit` ($\{0, 1\}$ exponent)
inside the Hilbert symbol, using square-invariance: $p^{2k} \cdot$(anything) leaves the Hilbert
symbol unchanged. -/
lemma hilbert_padicPowerUnitZ_eq (hp_odd : p ≠ 2) (α : ℤ) (u : ℤ_[p]ˣ) (b : ℚ_[p]ˣ) :
    hilbertSymbol ℚ_[p] (padicPowerUnitZ p α u) b =
    hilbertSymbol ℚ_[p] (padicPowerUnit p ⟨(α % 2).toNat, int_emod_two_toNat_lt α⟩ u) b := by
  unfold padicPowerUnitZ padicPowerUnit

  have hα : α = 2 * (α / 2) + α % 2 := (Int.ediv_add_emod α 2).symm
  conv_lhs => rw [show α = 2 * (α / 2) + α % 2 from hα]
  rw [zpow_add, zpow_mul]


  have hsq : (qpPrime p ^ (2 : ℤ)) ^ (α / 2) = (qpPrime p ^ (α / 2)) ^ (2 : ℕ) := by
    rw [← zpow_natCast (qpPrime p ^ (α / 2)) 2, ← zpow_mul, ← zpow_mul, mul_comm]
    norm_cast
  rw [hsq]
  rw [show (qpPrime p ^ (α / 2)) ^ 2 * qpPrime p ^ (α % 2) * unitZpToQp u =
    (qpPrime p ^ (α / 2)) ^ 2 * (qpPrime p ^ (α % 2) * unitZpToQp u) from by group]
  rw [hilbert_sq_mul_left]
  congr 1
  congr 1
  rcases Int.emod_two_eq_zero_or_one α with h | h <;> simp [h, zpow_natCast]

/-- If $x^2 = 1$ (i.e., $x = \pm 1$), then $x^a = x^b$ whenever $a \equiv b \pmod 2$. -/
lemma pow_eq_of_sq_eq_one_of_mod_two_eq {x : ℤ} (hx : x ^ 2 = 1) {a b : ℕ}
    (h : a % 2 = b % 2) : x ^ a = x ^ b := by
  have hx_val : x = 1 ∨ x = -1 := by
    have hmul : x * x = 1 := by linarith [sq x]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmul with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases hx_val with rfl | rfl
  · simp
  · have ha := Nat.mod_two_eq_zero_or_one a
    have hb := Nat.mod_two_eq_zero_or_one b
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [Even.neg_one_pow (Nat.even_iff.mpr ha), Even.neg_one_pow (Nat.even_iff.mpr hb)]
    · omega
    · omega
    · rw [Odd.neg_one_pow (Nat.odd_iff.mpr ha), Odd.neg_one_pow (Nat.odd_iff.mpr hb)]

/-- The natural number $(α \bmod 2).\text{toNat}$ has the same parity as $|α|$. -/
lemma int_emod_two_toNat_mod_two_eq_natAbs_mod_two (α : ℤ) :
    (α % 2).toNat % 2 = α.natAbs % 2 := by
  rcases Int.emod_two_eq_zero_or_one α with h | h <;> simp [h] <;> omega

/-- The Legendre symbol squared equals $1$, since it takes values in $\{\pm 1\}$. -/
lemma padicUnitLegendre_sq (v : ℤ_[p]ˣ) : padicUnitLegendre v ^ 2 = 1 := by
  have hne_nat := padicUnitLegendre_ne_zero v
  have hne : ((ZMod.val (PadicInt.toZMod (v : ℤ_[p])) : ℤ) : ZMod p) ≠ 0 := by
    rwa [Int.cast_natCast]
  rcases legendreSym.eq_one_or_neg_one p hne with h | h <;>
    simp only [padicUnitLegendre, h] <;> norm_num

/-- (Textbook Theorem 10.7, general form with integer exponents)
For an odd prime $p$, integer exponents $\alpha, \beta \in \mathbb{Z}$, and units
$u, v \in \mathbb{Z}_p^\times$, the Hilbert symbol of $p^\alpha u$ and $p^\beta v$ is
$$(p^\alpha u, p^\beta v)_p = (-1)^{|\alpha|\,|\beta|\,\frac{p-1}{2}}
  \left(\tfrac{u}{p}\right)^{|\beta|} \left(\tfrac{v}{p}\right)^{|\alpha|}.$$ -/
theorem hilbert_formula_odd_general (hp_odd : p ≠ 2)
    (α β : ℤ) (u v : ℤ_[p]ˣ) :
    padicHilbertSymbol p (padicPowerUnitZ p α u) (padicPowerUnitZ p β v) =
    (-1 : ℤ) ^ (α.natAbs * β.natAbs * ((p - 1) / 2)) *
    padicUnitLegendre u ^ β.natAbs *
    padicUnitLegendre v ^ α.natAbs := by

  let α' : Fin 2 := ⟨(α % 2).toNat, int_emod_two_toNat_lt α⟩
  let β' : Fin 2 := ⟨(β % 2).toNat, int_emod_two_toNat_lt β⟩

  have hLHS : padicHilbertSymbol p (padicPowerUnitZ p α u) (padicPowerUnitZ p β v) =
      padicHilbertSymbol p (padicPowerUnit p α' u) (padicPowerUnit p β' v) := by
    simp only [padicHilbertSymbol]
    rw [hilbert_padicPowerUnitZ_eq hp_odd α u]
    rw [hilbert_symm]
    rw [hilbert_padicPowerUnitZ_eq hp_odd β v]
    rw [hilbert_symm]

  rw [hLHS, hilbert_formula_odd hp_odd α' β' u v]

  have hα_parity := int_emod_two_toNat_mod_two_eq_natAbs_mod_two α
  have hβ_parity := int_emod_two_toNat_mod_two_eq_natAbs_mod_two β

  have h_neg1 : (-1 : ℤ) ^ ((α % 2).toNat * (β % 2).toNat * ((p - 1) / 2)) =
      (-1 : ℤ) ^ (α.natAbs * β.natAbs * ((p - 1) / 2)) := by
    apply pow_eq_of_sq_eq_one_of_mod_two_eq (by norm_num)
    rw [Nat.mul_mod ((α % 2).toNat * (β % 2).toNat),
        Nat.mul_mod (α.natAbs * β.natAbs)]
    congr 1
    rw [Nat.mul_mod (α % 2).toNat, Nat.mul_mod α.natAbs, hα_parity, hβ_parity]
  have h_leg_u : padicUnitLegendre u ^ (β % 2).toNat =
      padicUnitLegendre u ^ β.natAbs :=
    pow_eq_of_sq_eq_one_of_mod_two_eq (padicUnitLegendre_sq u) hβ_parity
  have h_leg_v : padicUnitLegendre v ^ (α % 2).toNat =
      padicUnitLegendre v ^ α.natAbs :=
    pow_eq_of_sq_eq_one_of_mod_two_eq (padicUnitLegendre_sq v) hα_parity

  rw [show (α' : ℕ) = (α % 2).toNat from rfl,
      show (β' : ℕ) = (β % 2).toNat from rfl,
      h_neg1, h_leg_u, h_leg_v]

end
