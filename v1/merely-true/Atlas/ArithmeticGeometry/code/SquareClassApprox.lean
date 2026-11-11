/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.LSeries.PrimesInAP

noncomputable section

open scoped BigOperators

/-- Two elements $a, b \in \mathbb{Q}_p$ lie in the same square class if there exists a nonzero
$u \in \mathbb{Q}_p$ such that $a = b \cdot u^2$. -/
def PadicSameSquareClass (p : ℕ) [Fact (Nat.Prime p)] (a b : ℚ_[p]) : Prop :=
  ∃ u : ℚ_[p], u ≠ 0 ∧ a = b * u ^ 2

/-- Two real numbers $a, b \in \mathbb{R}$ lie in the same square class if there exists a nonzero
$u \in \mathbb{R}$ such that $a = b \cdot u^2$ (equivalently, $a$ and $b$ have the same sign). -/
def RealSameSquareClass (a b : ℝ) : Prop :=
  ∃ u : ℝ, u ≠ 0 ∧ a = b * u ^ 2

/-- Reflexivity: any nonzero $a \in \mathbb{Q}_p$ is in the same square class as itself,
witnessed by $u = 1$. -/
lemma PadicSameSquareClass.refl {p : ℕ} [Fact (Nat.Prime p)] {a : ℚ_[p]} (_ha : a ≠ 0) :
    PadicSameSquareClass p a a :=
  ⟨1, one_ne_zero, by ring⟩

/-- Transitivity of the same-square-class relation in $\mathbb{Q}_p$. -/
lemma PadicSameSquareClass.trans {p : ℕ} [Fact (Nat.Prime p)] {a b c : ℚ_[p]}
    (h1 : PadicSameSquareClass p a b) (h2 : PadicSameSquareClass p b c) :
    PadicSameSquareClass p a c := by
  obtain ⟨u, hu, hab⟩ := h1
  obtain ⟨v, hv, hbc⟩ := h2
  exact ⟨u * v, mul_ne_zero hu hv, by rw [hab, hbc]; ring⟩

/-- If $r$ is in the same square class as $s/x$ in $\mathbb{Q}_p$, then $r \cdot s$ is in the same
square class as $x$. Used to rescale the approximating rational. -/
lemma square_class_mul_of_div {p : ℕ} [Fact (Nat.Prime p)]
    (r s : ℚ) (x : ℚ_[p]) (hx : x ≠ 0) (hs : (s : ℚ) ≠ 0)
    (h : PadicSameSquareClass p (↑r : ℚ_[p]) ((↑s : ℚ_[p]) * x⁻¹)) :
    PadicSameSquareClass p (↑(r * s) : ℚ_[p]) x := by
  obtain ⟨w, hw, hrw⟩ := h
  refine ⟨(↑s : ℚ_[p]) * x⁻¹ * w, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (Rat.cast_ne_zero.mpr hs) (inv_ne_zero hx)) hw
  · rw [show (↑(r * s) : ℚ_[p]) = (↑r : ℚ_[p]) * (↑s : ℚ_[p]) from by push_cast; ring,
        hrw]
    field_simp

/-- Two nonzero real numbers with the same sign (equivalently, $a \cdot b > 0$) are in the same
square class, witnessed by $u = \sqrt{a/b}$. -/
lemma real_same_sign_same_square_class (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : 0 < a * b) : RealSameSquareClass a b := by
  have hab' : 0 < a / b := by
    rw [div_pos_iff]
    rcases mul_pos_iff.mp hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · left; exact ⟨ha', hb'⟩
    · right; exact ⟨ha', hb'⟩
  refine ⟨Real.sqrt (a / b), ?_, ?_⟩
  · exact ne_of_gt (Real.sqrt_pos.mpr hab')
  · rw [Real.sq_sqrt hab'.le]; field_simp

/-- The $p$-adic valuation of $p^v$ in $\mathbb{Q}$ is $v$ (for $v \in \mathbb{Z}$). -/
lemma padicValRat_prime_zpow (p : ℕ) [hp : Fact (Nat.Prime p)] (v : ℤ) :
    padicValRat p ((p : ℚ) ^ v) = v := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rcases v with n | n
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    rw [padicValRat.pow hp0]; simp [padicValRat.of_nat]
  · simp only [zpow_negSucc]
    rw [padicValRat.inv, padicValRat.pow hp0]; simp [padicValRat.of_nat]; omega

/-- The $p$-adic norm of $p^v$ in $\mathbb{Q}$ is $p^{-v}$. -/
lemma padicNorm_prime_self_zpow (p : ℕ) [hp : Fact (Nat.Prime p)] (v : ℤ) :
    padicNorm p ((p : ℚ) ^ v) = (p : ℚ) ^ (-v) := by
  have hne : ((p : ℚ) ^ v) ≠ 0 := zpow_ne_zero v (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  rw [padicNorm.eq_zpow_of_nonzero hne, padicValRat_prime_zpow]

/-- For distinct primes $p \neq q$, the $q$-adic norm of $p^v$ is $1$ (since $p$ is a $q$-adic
unit). -/
lemma padicNorm_prime_zpow_ne (p q : ℕ) [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)]
    (hpq : p ≠ q) (v : ℤ) : padicNorm q ((p : ℚ) ^ v) = 1 := by
  have hne : ((p : ℚ) ^ v) ≠ 0 := zpow_ne_zero v (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  rw [padicNorm.eq_zpow_of_nonzero hne]
  suffices padicValRat q ((p : ℚ) ^ v) = 0 by rw [this, neg_zero, zpow_zero]
  have hval : padicValNat q p = 0 := by
    rw [padicValNat.eq_zero_iff]
    right; right
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp h).symm
  rcases v with n | n
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    rw [padicValRat.pow (Nat.cast_ne_zero.mpr hp.out.ne_zero)]
    simp [padicValRat.of_nat, hval]
  · simp only [zpow_negSucc]
    rw [padicValRat.inv, padicValRat.pow (Nat.cast_ne_zero.mpr hp.out.ne_zero)]
    simp [padicValRat.of_nat, hval]

/-- Given pairwise distinct primes $p_0, \dots, p_{n-1}$, the $p_i$-adic norm of
$\prod_j p_j^{v_j}$ equals the $p_i$-adic norm of $p_i^{v_i}$ alone (the other factors are units
at $p_i$). -/
lemma padicNorm_prod_at_prime (n : ℕ) (primes : Fin n → ℕ)
    (hp : ∀ i, Fact (Nat.Prime (primes i)))
    (hinj : Function.Injective primes)
    (vals : Fin n → ℤ) (i : Fin n) :
    padicNorm (primes i) (∏ j : Fin n, (primes j : ℚ) ^ vals j) =
    padicNorm (primes i) ((primes i : ℚ) ^ vals i) := by
  haveI := hp i
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  rw [padicNorm.mul]
  suffices h : ∏ x ∈ Finset.univ.erase i,
      padicNorm (primes i) ((primes x : ℚ) ^ vals x) = 1 by
    have h_prod : padicNorm (primes i)
        (∏ x ∈ Finset.univ.erase i, (primes x : ℚ) ^ vals x) =
        ∏ x ∈ Finset.univ.erase i, padicNorm (primes i) ((primes x : ℚ) ^ vals x) := by
      let f : MonoidWithZeroHom ℚ ℚ :=
        { toFun := padicNorm (primes i), map_zero' := padicNorm.zero,
          map_one' := padicNorm.one, map_mul' := padicNorm.mul }
      exact map_prod f _ _
    rw [h_prod, h, mul_one]
  apply Finset.prod_eq_one
  intro j hj
  haveI := hp j
  exact padicNorm_prime_zpow_ne (primes j) (primes i)
    (fun h => (Finset.ne_of_mem_erase hj) (hinj h)) (vals j)

/-- For a prime $q$ different from each $p_i$, the $q$-adic norm of $\prod_i p_i^{v_i}$ is $1$. -/
lemma padicNorm_prod_primes_eq_one (n : ℕ) (primes : Fin n → ℕ)
    (hp : ∀ i, Fact (Nat.Prime (primes i)))
    (vals : Fin n → ℤ)
    (q : ℕ) [hq : Fact (Nat.Prime q)]
    (hq_not : ∀ i, q ≠ primes i) :
    padicNorm q (∏ i : Fin n, (primes i : ℚ) ^ vals i) = 1 := by
  have h_prod : padicNorm q (∏ i : Fin n, (primes i : ℚ) ^ vals i) =
      ∏ i : Fin n, padicNorm q ((primes i : ℚ) ^ vals i) := by
    let f : MonoidWithZeroHom ℚ ℚ :=
      { toFun := padicNorm q, map_zero' := padicNorm.zero, map_one' := padicNorm.one,
        map_mul' := padicNorm.mul }
    exact map_prod f _ _
  rw [h_prod]
  apply Finset.prod_eq_one
  intro i _
  haveI := hp i
  exact padicNorm_prime_zpow_ne (primes i) q (hq_not i).symm (vals i)

/-- Two $p$-adic units $u, v \in \mathbb{Z}_p^\times$ that are congruent modulo $p^e$ (with
$e = 3$ if $p = 2$ and $e = 1$ otherwise) are in the same square class in $\mathbb{Q}_p^\times$.
The proof applies Hensel's lemma to the polynomial $X^2 - (u/v)$. -/
theorem padic_unit_square_class_of_congr (p : ℕ) [Fact (Nat.Prime p)]
    (u v : ℤ_[p]) (hu : IsUnit u) (hv : IsUnit v)
    (e : ℕ) (he : e = if p = 2 then 3 else 1)
    (hcong : PadicInt.toZModPow e u = PadicInt.toZModPow e v) :
    PadicSameSquareClass p (u : ℚ_[p]) (v : ℚ_[p]) := by
  let c : ℤ_[p] := u * ↑hv.unit⁻¹
  have hc_unit : IsUnit c := IsUnit.mul hu ⟨hv.unit⁻¹, rfl⟩
  have hc_norm : ‖c - 1‖ ≤ ↑p ^ (-(e : ℤ)) := by
    have hv_inv_norm : ‖(↑hv.unit⁻¹ : ℤ_[p])‖ = 1 := by
      have : IsUnit (↑hv.unit⁻¹ : ℤ_[p]) := ⟨hv.unit⁻¹, rfl⟩
      rwa [PadicInt.isUnit_iff] at this
    rw [show c - 1 = (u - v) * ↑hv.unit⁻¹ from by
      show u * ↑hv.unit⁻¹ - 1 = (u - v) * ↑hv.unit⁻¹
      rw [sub_mul]; congr 1; exact hv.mul_val_inv.symm,
      norm_mul, hv_inv_norm, mul_one]
    have hker : u - v ∈ RingHom.ker (PadicInt.toZModPow e) := by
      rw [RingHom.mem_ker, map_sub, hcong, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
    obtain ⟨k, hk⟩ := hker
    rw [hk, norm_mul]
    calc ‖(p : ℤ_[p]) ^ e‖ * ‖k‖
        ≤ ‖(p : ℤ_[p]) ^ e‖ * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one k) (norm_nonneg _)
      _ = ‖(p : ℤ_[p])‖ ^ e := by rw [mul_one, norm_pow]
      _ = _ := by rw [PadicInt.norm_p]; simp [zpow_neg, zpow_natCast]
  have hineq : (p : ℝ) ^ (-(e : ℤ)) < ‖(2 : ℤ_[p])‖ ^ 2 := by
    by_cases hp2 : p = 2
    · subst hp2; simp only [he, ↓reduceIte]
      rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from by norm_cast, PadicInt.norm_p]
      simp; norm_num
    · simp only [he, if_neg hp2]
      have h2norm : ‖(2 : ℤ_[p])‖ = 1 := by
        rw [PadicInt.norm_def]; norm_cast; change ‖((2 : ℕ) : ℚ_[p])‖ = 1
        rw [show ((2 : ℕ) : ℚ_[p]) = ((2 : ℚ) : ℚ_[p]) from by push_cast; ring, Padic.eq_padicNorm]
        suffices h : padicNorm p 2 = 1 by exact_mod_cast h
        rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from by norm_cast, padicNorm.nat_eq_one_iff]
        intro h; exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by omega) h) (Fact.out : Nat.Prime p).two_le)
      rw [h2norm, one_pow]; simp only [Nat.cast_one, zpow_neg_one]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt)
  let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C c
  have hhensel_cond : ‖Polynomial.aeval (1 : ℤ_[p]) F‖ <
      ‖Polynomial.aeval (1 : ℤ_[p]) (Polynomial.derivative F)‖ ^ 2 := by
    have hF_eval : Polynomial.aeval (1 : ℤ_[p]) F = 1 - c := by simp [F, Polynomial.aeval_def]
    have hF_deriv : Polynomial.aeval (1 : ℤ_[p]) (Polynomial.derivative F) = 2 := by
      simp [F, Polynomial.aeval_def, Polynomial.derivative_sub, Polynomial.derivative_pow,
            Polynomial.derivative_X, Polynomial.derivative_C]
    rw [hF_eval, hF_deriv, norm_sub_rev]
    exact lt_of_le_of_lt hc_norm hineq
  obtain ⟨w, hw_eq, _, _, _⟩ := hensels_lemma hhensel_cond
  have hw_sq : w ^ 2 = c := by
    simp only [F, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at hw_eq
    exact sub_eq_zero.mp hw_eq
  have hw_ne : w ≠ 0 := by
    intro h; rw [h, zero_pow (by norm_num : 2 ≠ 0)] at hw_sq
    rw [← hw_sq] at hc_unit; exact not_isUnit_zero hc_unit
  have hu_eq : u = w ^ 2 * ↑hv.unit := by
    rw [hw_sq, mul_assoc, show (↑hv.unit⁻¹ : ℤ_[p]) * ↑hv.unit = 1 from by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one], mul_one]
  refine ⟨(w : ℚ_[p]), fun h => hw_ne (Subtype.val_injective h), ?_⟩
  have h1 : (u : ℚ_[p]) = ((w ^ 2 * ↑hv.unit : ℤ_[p]) : ℚ_[p]) := congrArg _ hu_eq
  rw [h1]; push_cast; rw [hv.unit_spec]; ring

/-- **Existence of a simultaneous prime approximation.** Given finitely many distinct primes
$p_1, \dots, p_n$ and units $u_i \in \mathbb{Z}_{p_i}^\times$, there exists a prime $p_0$ not
among the $p_i$ such that $p_0$ is in the same square class as $u_i$ in $\mathbb{Q}_{p_i}$ for
each $i$. Combines CRT and Dirichlet's theorem on primes in arithmetic progressions. -/
theorem exists_prime_approx_units
    (n : ℕ) (primes : Fin n → ℕ)
    (hp : ∀ i, Fact (Nat.Prime (primes i)))
    (hinj : Function.Injective primes)
    (u : (i : Fin n) → ℚ_[primes i])
    (hu_unit : ∀ i, ‖u i‖ = 1) :
    ∃ p₀ : ℕ, Nat.Prime p₀ ∧ (∀ i, p₀ ≠ primes i) ∧
      ∀ i, @PadicSameSquareClass (primes i) (hp i) (↑(p₀ : ℚ)) (u i) := by

  have hu_le : ∀ i, ‖u i‖ ≤ 1 := fun i => le_of_eq (hu_unit i)
  let u_int : (i : Fin n) → ℤ_[primes i] := fun i => ⟨u i, hu_le i⟩
  have hu_isunit : ∀ i, IsUnit (u_int i) := by
    intro i; haveI := hp i; rw [PadicInt.isUnit_iff]; exact hu_unit i

  let e : Fin n → ℕ := fun i => if primes i = 2 then 3 else 1
  let moduli : Fin n → ℕ := fun i => primes i ^ e i

  let targets : Fin n → ℕ := fun i =>
    @ZMod.val (primes i ^ e i) (@PadicInt.toZModPow (primes i) (hp i) (e i) (u_int i))

  have hmoduli_coprime : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun Nat.Coprime moduli) :=
    fun i _ j _ hij => Nat.coprime_pow_primes _ _ (hp i).out (hp j).out (fun h => hij (hinj h))
  have hmoduli_ne : ∀ i ∈ Finset.univ, moduli i ≠ 0 :=
    fun i _ => pow_ne_zero _ (hp i).out.ne_zero

  obtain ⟨z, hz⟩ := Nat.chineseRemainderOfFinset targets moduli
    Finset.univ hmoduli_ne hmoduli_coprime

  have htarget_coprime : ∀ i, (targets i).Coprime (moduli i) := by
    intro i; haveI := hp i
    exact ZMod.val_coe_unit_coprime ((hu_isunit i).map (PadicInt.toZModPow (e i))).unit

  have hz_coprime_each : ∀ i, z.Coprime (moduli i) := by
    intro i; rw [Nat.Coprime, (hz i (Finset.mem_univ i)).gcd_eq]; exact htarget_coprime i
  let m := ∏ i : Fin n, moduli i
  have hm_ne : m ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hmoduli_ne i (Finset.mem_univ i))
  have hz_coprime_m : z.Coprime m := Nat.Coprime.prod_right (fun i _ => hz_coprime_each i)

  let bound := Finset.univ.sup primes
  obtain ⟨p₀, hp₀_gt, hp₀_prime, hp₀_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq bound hm_ne hz_coprime_m

  have hp₀_ne : ∀ i, p₀ ≠ primes i := by
    intro i h; have := Finset.le_sup (Finset.mem_univ i) (f := primes); omega
  refine ⟨p₀, hp₀_prime, hp₀_ne, fun i => ?_⟩

  haveI : Fact (Nat.Prime (primes i)) := hp i
  haveI : NeZero (primes i ^ e i) := ⟨pow_ne_zero _ (hp i).out.ne_zero⟩

  have hmod_dvd : moduli i ∣ m := Finset.dvd_prod_of_mem moduli (Finset.mem_univ i)
  have hp₀_target : p₀ ≡ targets i [MOD moduli i] :=
    (hp₀_mod.of_dvd hmod_dvd).trans (hz i (Finset.mem_univ i))

  have hcong : @PadicInt.toZModPow (primes i) (hp i) (e i) (p₀ : ℤ_[primes i]) =
      @PadicInt.toZModPow (primes i) (hp i) (e i) (u_int i) := by
    have h1 : @PadicInt.toZModPow (primes i) (hp i) (e i) (p₀ : ℤ_[primes i]) =
        (p₀ : ZMod (primes i ^ e i)) := map_natCast _ p₀
    have h2 : (p₀ : ZMod (primes i ^ e i)) = ((targets i : ℕ) : ZMod (primes i ^ e i)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hp₀_target
    have h3 : ((targets i : ℕ) : ZMod (primes i ^ e i)) =
        @PadicInt.toZModPow (primes i) (hp i) (e i) (u_int i) := by
      show ((@PadicInt.toZModPow (primes i) (hp i) (e i) (u_int i)).val : ZMod (primes i ^ e i)) =
        @PadicInt.toZModPow (primes i) (hp i) (e i) (u_int i)
      simp [ZMod.natCast_val]
    rw [h1, h2, h3]

  have hp₀_unit : IsUnit (p₀ : ℤ_[primes i]) := by
    rw [PadicInt.isUnit_iff]
    have : (p₀ : ℚ_[primes i]) = ((p₀ : ℚ) : ℚ_[primes i]) := by push_cast; ring
    rw [show ‖(p₀ : ℤ_[primes i])‖ = ‖(p₀ : ℚ_[primes i])‖ from rfl, this, Padic.eq_padicNorm]
    exact_mod_cast @padicNorm.padicNorm_of_prime_of_ne (primes i) p₀ (hp i) ⟨hp₀_prime⟩
      (hp₀_ne i).symm

  have hsq := padic_unit_square_class_of_congr (primes i) (p₀ : ℤ_[primes i]) (u_int i)
      hp₀_unit (hu_isunit i) (e i) rfl hcong

  convert hsq using 1

/-- If a rational $y$ has the same $p_i$-adic norm as $x_i$ for each $i$, then $y \cdot x_i^{-1}$
is a unit in $\mathbb{Q}_{p_i}$ for each $i$. -/
theorem padic_unit_norm_of_prod_div
    (n : ℕ) (primes : Fin n → ℕ)
    (hp : ∀ i, Fact (Nat.Prime (primes i)))
    (_hinj : Function.Injective primes)
    (x_fin : (i : Fin n) → ℚ_[primes i])
    (hx_fin : ∀ i, x_fin i ≠ 0)
    (y : ℚ) (_hy : y ≠ 0)
    (hy_norm : ∀ i, ‖(↑y : ℚ_[primes i])‖ = ‖x_fin i‖) :
    ∀ i, ‖(↑y : ℚ_[primes i]) * (x_fin i)⁻¹‖ = 1 := by
  intro i
  haveI := hp i
  rw [norm_mul, hy_norm i, norm_inv, mul_inv_cancel₀]
  exact norm_ne_zero_iff.mpr (hx_fin i)

/-- **Lemma 11.11 (Square-class weak approximation).** Given a finite set $S$ of places of
$\mathbb{Q}$ (a finite set of primes $\{p_i\}$, possibly together with the infinite place) and
nonzero elements $x_i \in \mathbb{Q}_{p_i}^\times$ (and a sign $x_\infty \in \mathbb{R}^\times$
if the infinite place is in $S$), there exists $x \in \mathbb{Q}^\times$ that is in the same
square class as $x_i$ at every place in $S$ and is a $q$-adic unit at every prime $q$ outside
$S$, with at most one possible exception. -/
theorem lemma_11_11
    (n : ℕ) (primes : Fin n → ℕ)
    (hp : ∀ i, Fact (Nat.Prime (primes i)))
    (hinj : Function.Injective primes)
    (x_fin : (i : Fin n) → ℚ_[primes i])
    (hx_fin : ∀ i, x_fin i ≠ 0)
    (infInS : Bool)
    (x_inf : ℝ)
    (hx_inf : infInS = true → x_inf ≠ 0) :
    ∃ (x : ℚ), x ≠ 0 ∧

      (∀ i, @PadicSameSquareClass (primes i) (hp i) (↑x) (x_fin i)) ∧

      (infInS = true → RealSameSquareClass (↑x : ℝ) x_inf) ∧

      (∃ (exceptions : Finset ℕ), exceptions.card ≤ 1 ∧
        ∀ (q : ℕ) (_hq : Fact (Nat.Prime q)),
          q ∉ (Finset.image primes Finset.univ) →
          q ∉ exceptions →
          ‖(↑x : ℚ_[q])‖ = 1) := by
  let vals : Fin n → ℤ := fun i => @Padic.valuation (primes i) (hp i) (x_fin i)
  let prod_val : ℚ := ∏ i : Fin n, (primes i : ℚ) ^ vals i
  have hprod_ne : prod_val ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr (hp i).out.ne_zero)
  have hprod_pos : 0 < prod_val := by
    apply Finset.prod_pos; intro i _
    exact zpow_pos (Nat.cast_pos.mpr (hp i).out.pos) _
  let negSign : Bool := infInS && decide (x_inf < 0)
  let y : ℚ := if negSign = true then -prod_val else prod_val
  have hy_ne : y ≠ 0 := by
    simp only [y, negSign]
    split_ifs <;> simp [hprod_ne]
  have hy_norm : ∀ i, ‖(↑y : ℚ_[primes i])‖ = ‖x_fin i‖ := by
    intro i
    haveI := hp i
    rw [Padic.eq_padicNorm]
    have hpn_y : padicNorm (primes i) y = padicNorm (primes i) prod_val := by
      simp only [y, negSign]; split_ifs <;> simp [padicNorm.neg]
    rw [hpn_y, show prod_val = ∏ j : Fin n, (primes j : ℚ) ^ vals j from rfl,
        padicNorm_prod_at_prime n primes hp hinj vals i,
        padicNorm_prime_self_zpow,
        show vals i = @Padic.valuation (primes i) (hp i) (x_fin i) from rfl]
    rw [Padic.norm_eq_zpow_neg_valuation (hx_fin i)]
    push_cast; ring
  have hu_unit : ∀ i, ‖(↑y : ℚ_[primes i]) * (x_fin i)⁻¹‖ = 1 :=
    padic_unit_norm_of_prod_div n primes hp hinj x_fin hx_fin y hy_ne hy_norm
  let u' : (i : Fin n) → ℚ_[primes i] := fun i => ↑y * (x_fin i)⁻¹
  obtain ⟨p₀, hp₀_prime, hp₀_not_in, hp₀_sq⟩ :=
    exists_prime_approx_units n primes hp hinj u' hu_unit
  refine ⟨(p₀ : ℚ) * y, ?_, ?_, ?_, ?_⟩
  ·
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hp₀_prime.ne_zero) hy_ne
  ·
    intro i
    haveI := hp i
    exact square_class_mul_of_div (↑p₀ : ℚ) y (x_fin i) (hx_fin i) hy_ne (hp₀_sq i)
  ·
    intro hinfS
    apply real_same_sign_same_square_class
    ·
      push_cast
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hp₀_prime.ne_zero) (Rat.cast_ne_zero.mpr hy_ne)
    · exact hx_inf hinfS
    ·
      push_cast
      have hp₀_pos : (0 : ℝ) < (p₀ : ℝ) := Nat.cast_pos.mpr hp₀_prime.pos
      have hprod_pos_r : (0 : ℝ) < (prod_val : ℝ) := Rat.cast_pos.mpr hprod_pos
      show 0 < (↑p₀ * ↑y) * x_inf


      show 0 < ↑↑p₀ * (↑y : ℝ) * x_inf
      have : negSign = decide (x_inf < 0) := by
        simp only [negSign, hinfS, Bool.true_and]
      simp only [y]
      rw [this]
      by_cases hlt : x_inf < 0
      · simp [hlt]
        have h1 : (↑p₀ : ℝ) * -(prod_val : ℝ) < 0 := by nlinarith
        nlinarith [mul_neg_of_neg_of_pos h1 (neg_pos.mpr hlt)]
      · simp [hlt]
        have hxpos : 0 < x_inf := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm (hx_inf hinfS))
        exact mul_pos (mul_pos hp₀_pos hprod_pos_r) hxpos
  ·
    refine ⟨{p₀}, Finset.card_singleton p₀ ▸ le_refl 1, ?_⟩
    intro q hq_prime hq_not_in_S hq_ne_p₀
    haveI := hq_prime
    rw [Padic.eq_padicNorm]
    rw [show (↑p₀ * y : ℚ) = (↑p₀ : ℚ) * y from by norm_cast]
    rw [padicNorm.mul]
    have hq_ne : q ≠ p₀ := by simp at hq_ne_p₀; exact hq_ne_p₀
    rw [@padicNorm.padicNorm_of_prime_of_ne q p₀ hq_prime ⟨hp₀_prime⟩ hq_ne, one_mul]

    have hpn_y : padicNorm q y = padicNorm q prod_val := by
      simp only [y, negSign]; split_ifs <;> simp [padicNorm.neg]
    rw [hpn_y, show prod_val = ∏ i : Fin n, (primes i : ℚ) ^ vals i from rfl]
    rw [show (1 : ℝ) = ↑(1 : ℚ) from by simp]
    congr 1
    exact padicNorm_prod_primes_eq_one n primes hp vals q
      (fun i => by
        intro heq
        exact hq_not_in_S (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩))

end
