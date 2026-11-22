/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Int.GCD
import Mathlib.GroupTheory.OrderOfElement
import Atlas.EllipticCurves.code.PointCounting

/-- Fermat's little theorem in `ZMod p`: for any element `a`, we have
`a ^ p = a` when `p` is prime. -/
theorem fermat_little_theorem (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    a ^ p = a :=
  ZMod.pow_card a

/-- Euler's criterion for primality: an integer `N ≥ 2` is prime iff its
Euler totient equals `N - 1`. -/
theorem totient_eq_sub_one_iff_prime (N : ℕ) (hN : 2 ≤ N) :
    N.totient = N - 1 ↔ N.Prime :=
  Nat.totient_eq_iff_prime (by omega)

/-- `N` is a Carmichael number if it is a composite integer greater than `1`
for which every unit `a` in `ZMod N` satisfies `a ^ (N - 1) = 1`. -/
def IsCarmichael (N : ℕ) : Prop :=
  ¬N.Prime ∧ 1 < N ∧ ∀ a : ZMod N, IsUnit a → a ^ (N - 1) = 1

open scoped Nat

/-- The exponent `s` in the Miller-Rabin decomposition `N - 1 = 2^s * d`,
defined as the `2`-adic valuation of `N - 1`. -/
noncomputable def millerRabinS (N : ℕ) : ℕ := multiplicity 2 (N - 1)

/-- The odd part `d` in the Miller-Rabin decomposition `N - 1 = 2^s * d`. -/
noncomputable def millerRabinD (N : ℕ) : ℕ := (N - 1) / 2 ^ millerRabinS N

/-- The Miller-Rabin decomposition: `N - 1 = 2 ^ millerRabinS N * millerRabinD N`. -/
lemma millerRabin_decomp (N : ℕ) :
    N - 1 = 2 ^ millerRabinS N * millerRabinD N := by
  simp only [millerRabinD, millerRabinS]
  have h := Nat.div_mul_cancel (pow_multiplicity_dvd 2 (N - 1))
  linarith

/-- In an integral domain, if `x ^ (2 ^ n) = 1`, then either `x = 1` or there
exists `i < n` such that `x ^ (2 ^ i) = -1`. This is the algebraic core of the
Miller-Rabin "square-root chain" argument. -/
lemma sq_chain_dichotomy {R : Type*} [CommRing R] [IsDomain R]
    (x : R) (n : ℕ) (h : x ^ (2 ^ n) = 1) :
    x = 1 ∨ ∃ i : ℕ, i < n ∧ x ^ (2 ^ i) = -1 := by
  induction n with
  | zero => simp [pow_zero, pow_one] at h; exact Or.inl h
  | succ n ih =>
    have h2 : (x ^ (2 ^ n)) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ]; exact h
    rw [sq_eq_one_iff] at h2
    rcases h2 with h_one | h_neg
    · rcases ih h_one with h1 | ⟨i, hi, hx⟩
      · exact Or.inl h1
      · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hx⟩
    · exact Or.inr ⟨n, Nat.lt_succ_iff.mpr le_rfl, h_neg⟩

/-- Lemma 11.6 (Sutherland): writing a prime `p = 2^s t + 1` with `t` odd, for
any integer `a` nonzero mod `p`, exactly one of the following holds:
(i) `a^t ≡ 1 (mod p)`; (ii) `a^{2^i t} ≡ -1 (mod p)` for some `0 ≤ i < s`. -/
theorem lemma_11_6 (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) :
    Xor' (a ^ millerRabinD p = 1)
      (∃ i : ℕ, i < millerRabinS p ∧ a ^ (2 ^ i * millerRabinD p) = -1) := by
  haveI : Fact p.Prime := ⟨hp⟩

  have hflt : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha

  rw [millerRabin_decomp p, mul_comm, pow_mul] at hflt

  have h_or := sq_chain_dichotomy (a ^ millerRabinD p) (millerRabinS p) hflt

  have h_not_both : ¬ (a ^ millerRabinD p = 1 ∧
      ∃ i : ℕ, i < millerRabinS p ∧ a ^ (2 ^ i * millerRabinD p) = -1) := by
    rintro ⟨h1, i, his, hi⟩
    have h2 : a ^ (2 ^ i * millerRabinD p) = 1 := by
      rw [mul_comm, pow_mul, h1, one_pow]
    rw [h2] at hi

    have hp2 : p = 2 := by
      by_contra hne
      have : 2 < p := Nat.lt_of_le_of_ne hp.two_le (Ne.symm hne)
      haveI : Fact (2 < p) := ⟨this⟩
      exact CharP.neg_one_ne_one (ZMod p) p hi.symm
    subst hp2
    have : millerRabinS 2 = 0 := by
      simp only [millerRabinS]
      show multiplicity 2 (2 - 1) = 0
      simp only [Nat.reduceSub]
      rw [multiplicity_eq_zero]; omega
    omega

  rcases h_or with h_left | ⟨i, hi_lt, hi_eq⟩
  · left
    exact ⟨h_left, fun ⟨i, _, _⟩ => h_not_both ⟨h_left, i, ‹_›, ‹_›⟩⟩
  · right
    constructor
    · exact ⟨i, hi_lt, by rw [mul_comm, pow_mul]; exact hi_eq⟩
    · intro h_left
      exact h_not_both ⟨h_left, i, hi_lt, by rw [mul_comm, pow_mul]; exact hi_eq⟩

/-- An integer `a` is a Miller-Rabin witness for the compositeness of `N` if
`a` is nonzero mod `N`, `a^d ≢ 1`, and `a^(2^r · d) ≢ -1` for every
`0 ≤ r < s`, where `N - 1 = 2^s · d` with `d` odd. -/
def IsMillerRabinWitness (N a : ℕ) : Prop :=
  (a : ZMod N) ≠ 0 ∧
  (a : ZMod N) ^ millerRabinD N ≠ 1 ∧
  ∀ r : ℕ, r < millerRabinS N → (a : ZMod N) ^ (2 ^ r * millerRabinD N) ≠ -1

noncomputable section

open Classical

/-- The set of Miller-Rabin witnesses in `[1, N-1]`. -/
def millerRabinWitnessSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun a => IsMillerRabinWitness N a)

/-- The set of Miller-Rabin liars (non-witnesses) in `[1, N-1]`. -/
def millerRabinLiarSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun a => ¬ IsMillerRabinWitness N a)

/-- The Miller-Rabin witness set and liar set together partition `[1, N-1]`. -/
lemma millerRabin_witness_liar_card (N : ℕ) :
    (millerRabinWitnessSet N).card + (millerRabinLiarSet N).card =
    (Finset.Icc 1 (N - 1)).card :=
  Finset.card_filter_add_card_filter_not (IsMillerRabinWitness N)

/-- A residue from `[1, N-1]` is nonzero in `ZMod N` whenever `N > 1`. -/
lemma zmod_ne_zero_of_mem_Icc {N : ℕ} (hN : N > 1) {a : ℕ} (ha : a ∈ Finset.Icc 1 (N - 1)) :
    (a : ZMod N) ≠ 0 := by
  haveI : NeZero N := ⟨by omega⟩
  rw [Finset.mem_Icc] at ha
  intro h
  have hval : (a : ZMod N).val = 0 := by rw [h]; simp
  rw [ZMod.val_natCast] at hval
  have hdvd : N ∣ a := Nat.dvd_of_mod_eq_zero hval
  exact absurd (Nat.eq_zero_of_dvd_of_lt hdvd (by omega)) (by omega)

/-- Any Miller-Rabin liar for `N` (with `N > 1`) is coprime to `N`. -/
lemma millerRabin_liar_coprime {N : ℕ} (hN : N > 1) {a : ℕ}
    (ha_mem : a ∈ millerRabinLiarSet N) : a.Coprime N := by
  simp only [millerRabinLiarSet, Finset.mem_filter] at ha_mem
  obtain ⟨ha_Icc, ha_liar⟩ := ha_mem
  have ha_ne : (a : ZMod N) ≠ 0 := zmod_ne_zero_of_mem_Icc hN ha_Icc
  haveI : NeZero N := ⟨by omega⟩
  rw [← ZMod.isUnit_iff_coprime]


  simp only [IsMillerRabinWitness, not_and, not_forall, not_not, exists_prop] at ha_liar
  have ha_liar' := ha_liar ha_ne


  by_cases hd : (a : ZMod N) ^ millerRabinD N = 1
  ·


    exact IsUnit.of_pow_eq_one hd (by
      simp only [millerRabinD]
      exact Nat.div_pos (Nat.le_of_dvd (by omega) (pow_multiplicity_dvd 2 (N - 1)))
        (Nat.pos_of_ne_zero (by positivity)) |>.ne')
  ·
    have : ∃ r, r < millerRabinS N ∧ (a : ZMod N) ^ (2 ^ r * millerRabinD N) = -1 :=
      (ha_liar' hd)
    obtain ⟨r, _, h_neg⟩ := this
    have h1 : (a : ZMod N) ^ (2 ^ r * millerRabinD N * 2) = 1 := by
      rw [pow_mul, h_neg, neg_one_sq]
    exact IsUnit.of_pow_eq_one h1 (by
      have : 0 < 2 ^ r * millerRabinD N := by
        apply Nat.mul_pos (Nat.pos_of_ne_zero (by positivity))
        exact Nat.div_pos (Nat.le_of_dvd (by omega) (pow_multiplicity_dvd 2 (N - 1)))
          (Nat.pos_of_ne_zero (by positivity))
      omega)



end

/-- The `2`-adic valuation of a natural number, computed recursively by
dividing by `2` while the input is even. -/
def twoAdicVal : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 1 + twoAdicVal ((n + 1) / 2) else 0
termination_by n => n
decreasing_by simp_wf; omega

/-- `2 ^ twoAdicVal n` divides `n`. -/
lemma two_pow_twoAdicVal_dvd (n : ℕ) : 2 ^ twoAdicVal n ∣ n := by
  match n with
  | 0 => simp [twoAdicVal]
  | n + 1 =>
    simp only [twoAdicVal]
    split_ifs with h
    · have h2 : 2 ∣ (n + 1) := Nat.dvd_of_mod_eq_zero (by omega)
      have ih := two_pow_twoAdicVal_dvd ((n + 1) / 2)
      rw [pow_add, pow_one]
      exact Nat.mul_dvd_of_dvd_div h2 ih
    · simp
termination_by n
decreasing_by omega

/-- `n = 2 ^ twoAdicVal n * (n / 2 ^ twoAdicVal n)`: extracting the `2`-adic
factor of `n`. -/
lemma twoAdicVal_decomp (n : ℕ) : n = 2 ^ twoAdicVal n * (n / 2 ^ twoAdicVal n) :=
  (Nat.mul_div_cancel' (two_pow_twoAdicVal_dvd n)).symm

/-- One iteration of the Miller-Rabin primality test for a candidate `N` with
a base `a`: succeeds iff `a^d ≡ 1` or `a^(2^r · d) ≡ -1` for some `r < s`,
where `N - 1 = 2^s · d`. -/
def millerRabinStep (N a : ℕ) : Bool :=
  let nm1 := N - 1
  let s := twoAdicVal nm1
  let d := nm1 / 2 ^ s
  ((a : ZMod N) ^ d == 1) ||
  (List.range s).any fun r => ((a : ZMod N) ^ (2 ^ r * d) == -1)

/-- The full Miller-Rabin test: run `millerRabinStep` on each witness in the
list and report `true` iff every one returns `true`. -/
def millerRabinTest (N : ℕ) (witnesses : List ℕ) : Bool :=
  witnesses.all (millerRabinStep N)

/-- In a ring with no zero divisors, if `x ^ 2^n = 1`, then `x = 1` or there
exists `r < n` such that `x ^ 2^r = -1`. -/
lemma pow_two_pow_eq_one_or_neg_one {R : Type*} [Ring R] [NoZeroDivisors R]
    {x : R} {n : ℕ} (hx : x ^ 2 ^ n = 1) :
    x = 1 ∨ ∃ r : ℕ, r < n ∧ x ^ 2 ^ r = -1 := by
  induction n with
  | zero => simp at hx; exact Or.inl hx
  | succ n ih =>
    rw [pow_succ, pow_mul] at hx
    rcases sq_eq_one_iff.mp hx with h | h
    · rcases ih h with h | ⟨r, hr, heq⟩
      · exact Or.inl h
      · exact Or.inr ⟨r, Nat.lt_succ_of_lt hr, heq⟩
    · exact Or.inr ⟨n, lt_add_one n, h⟩

/-- The Miller-Rabin decomposition (restatement): `N - 1 = 2 ^ millerRabinS N *
millerRabinD N`. -/
lemma millerRabin_decompose (N : ℕ) :
    N - 1 = 2 ^ millerRabinS N * millerRabinD N :=
  millerRabin_decomp N

/-- The Miller-Rabin step always returns `true` on a true prime `p` with any
base nonzero mod `p`. -/
theorem millerRabinStep_true_of_prime (p : ℕ) [hp : Fact p.Prime]
    {a : ℕ} (ha : (a : ZMod p) ≠ 0) :
    millerRabinStep p a = true := by
  unfold millerRabinStep
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range]
  set s := twoAdicVal (p - 1) with hs_def
  set d := (p - 1) / 2 ^ s with hd_def
  have fermat : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have decomp : p - 1 = 2 ^ s * d := twoAdicVal_decomp (p - 1)
  rw [decomp] at fermat
  have key : ((a : ZMod p) ^ d) ^ (2 ^ s) = 1 := by
    rw [← pow_mul, mul_comm]; exact fermat
  rcases pow_two_pow_eq_one_or_neg_one key with h | ⟨r, hr, heq⟩
  · exact Or.inl h
  · right; exact ⟨r, hr, by rwa [← pow_mul, mul_comm] at heq⟩

section ECPP

open WeierstrassCurve

/-- A projective `z`-coordinate `Pz` is zero modulo `N` if `N` divides `Pz`. -/
def IsZeroModN (Pz : ℤ) (N : ℕ) : Prop := (N : ℤ) ∣ Pz

/-- A projective `z`-coordinate `Pz` is nonzero modulo `N` if `N` does not
divide `Pz`. -/
def IsNonzeroModN (Pz : ℤ) (N : ℕ) : Prop := ¬ IsZeroModN Pz N

/-- A projective `z`-coordinate `Pz` is strongly nonzero modulo `N` if
`gcd(Pz, N) = 1`. -/
def IsStronglyNonzeroModN (Pz : ℤ) (N : ℕ) : Prop := Int.gcd Pz ↑N = 1

/-- If `Pz` is strongly nonzero mod `N` and `p` is a prime divisor of `N`,
then `p ∤ Pz`. -/
lemma not_dvd_of_stronglyNonzeroModN {Pz : ℤ} {N p : ℕ}
    (hstr : IsStronglyNonzeroModN Pz N) (hp : p.Prime) (hpN : p ∣ N) :
    ¬((p : ℤ) ∣ Pz) := by
  unfold IsStronglyNonzeroModN at hstr
  have hgcd : Nat.gcd Pz.natAbs N = 1 := by
    simp [Int.gcd, Int.natAbs_natCast] at hstr; exact hstr
  intro h
  have h1 : p ∣ Pz.natAbs := by rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at h
  have h2 : p ∣ Nat.gcd Pz.natAbs N := Nat.dvd_gcd h1 hpN
  rw [hgcd] at h2
  exact absurd (Nat.le_of_dvd Nat.one_pos h2) (Nat.not_le.mpr hp.one_lt)

/-- Strongly nonzero mod `N` implies nonzero mod `N`, provided `N > 1`. -/
lemma isNonzeroModN_of_isStronglyNonzeroModN {Pz : ℤ} {N : ℕ}
    (hstr : IsStronglyNonzeroModN Pz N) (hN : 1 < N) :
    IsNonzeroModN Pz N := by
  unfold IsNonzeroModN IsZeroModN
  intro h
  unfold IsStronglyNonzeroModN at hstr
  have hN_dvd_gcd : N ∣ Int.gcd Pz ↑N := by
    simp only [Int.gcd, Int.natAbs_natCast]
    exact Nat.dvd_gcd (Int.natCast_dvd.mp h) (dvd_refl N)
  rw [hstr] at hN_dvd_gcd
  exact absurd (Nat.le_of_dvd Nat.one_pos hN_dvd_gcd) (Nat.not_le.mpr hN)

/-- When `N` is prime, "strongly nonzero mod `N`" coincides with "nonzero
mod `N`". -/
lemma isStronglyNonzeroModN_iff_isNonzeroModN_of_prime {Pz : ℤ} {N : ℕ}
    (hN : N.Prime) :
    IsStronglyNonzeroModN Pz N ↔ IsNonzeroModN Pz N := by
  unfold IsStronglyNonzeroModN IsNonzeroModN IsZeroModN
  constructor
  · intro hgcd hdvd
    have hN_dvd_gcd : N ∣ Int.gcd Pz ↑N := by
      simp only [Int.gcd, Int.natAbs_natCast]
      exact Nat.dvd_gcd (Int.natCast_dvd.mp hdvd) (dvd_refl N)
    rw [hgcd] at hN_dvd_gcd
    exact absurd (Nat.le_of_dvd Nat.one_pos hN_dvd_gcd) (Nat.not_le.mpr hN.one_lt)
  · intro hndvd
    simp only [Int.gcd, Int.natAbs_natCast]
    show Nat.Coprime Pz.natAbs N
    exact Nat.Coprime.symm (hN.coprime_iff_not_dvd.mpr (fun h => hndvd (Int.natCast_dvd.mpr h)))

/-- Monotonicity used in the Goldwasser-Kilian bound: if `p ^ 2 ≤ N`, then
`(√p + 1)^2 ≤ (√√N + 1)^2`. -/
lemma fourth_root_mono {p N : ℕ} (hp2 : p ^ 2 ≤ N) :
    (Real.sqrt ↑p + 1) ^ 2 ≤ (Real.sqrt (Real.sqrt ↑N) + 1) ^ 2 := by
  have h1 : (p : ℝ) ≤ Real.sqrt ↑N := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg (α := ℝ) p)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hp2)
  nlinarith [Real.sqrt_le_sqrt h1, Real.sqrt_nonneg (p : ℝ)]

/-- The hypotheses of the Goldwasser-Kilian primality criterion (Theorem 11.13
of Sutherland): `N, M > 1`, `M > (N^{1/4}+1)^2`, `N` coprime to the
discriminant of `W`, the multiple `MP` is zero mod `N`, and `(M/ℓ)P` is
strongly nonzero mod `N` for every prime `ℓ ∣ M`. -/
structure GoldwasserKilianHyp (W : WeierstrassCurve ℤ) (N M : ℕ)
    (zMP : ℤ) (zMlP : ℕ → ℤ) : Prop where
  hN : N > 1
  hM : M > 1
  hMbound : (M : ℝ) > (Real.sqrt (Real.sqrt ↑N) + 1) ^ 2
  hcop : Nat.Coprime N (Int.natAbs W.Δ)
  hzero : IsZeroModN zMP N
  hstrong : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → IsStronglyNonzeroModN (zMlP ℓ) N

/-- If `N` is coprime to the discriminant of `W` and `p` is a prime divisor
of `N`, then the discriminant maps to a nonzero element of `ZMod p`. -/
lemma disc_ne_zero_of_coprime_dvd (W : WeierstrassCurve ℤ) (N p : ℕ)
    (hcop : Nat.Coprime N (Int.natAbs W.Δ)) (hp : p.Prime) (hpN : p ∣ N) :
    (Int.castRingHom (ZMod p)) W.Δ ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  simp only [Int.coe_castRingHom] at h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h1 : p ∣ W.Δ.natAbs := by
    rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at h
  have h2 : p ∣ Nat.gcd N (W.Δ.natAbs) := Nat.dvd_gcd hpN h1
  rw [hcop] at h2
  exact absurd (Nat.le_of_dvd Nat.one_pos h2) (Nat.not_le.mpr hp.one_lt)





end ECPP
