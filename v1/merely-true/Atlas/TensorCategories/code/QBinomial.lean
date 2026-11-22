/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

set_option maxHeartbeats 400000

variable {k : Type*} [Field k]

/-- The Gaussian (q-)binomial coefficient `qBinomial q n m`, defined by the
recursion `qBinomial q (n+1) (m+1) = q^(m+1) * qBinomial q n (m+1) + qBinomial q n m`,
with `qBinomial q n 0 = 1` and `qBinomial q 0 (m+1) = 0`. -/
def qBinomial (q : k) : ℕ → ℕ → k
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, m + 1 => q ^ (m + 1) * qBinomial q n (m + 1) + qBinomial q n m

/-- The q-binomial coefficient with bottom index `0` equals `1`. -/
@[simp]
lemma qBinomial_zero_right (q : k) (n : ℕ) : qBinomial q n 0 = 1 := by
  cases n <;> simp [qBinomial]

/-- The q-binomial coefficient `qBinomial q n m` vanishes when `n < m`. -/
lemma qBinomial_eq_zero_of_lt (q : k) (n m : ℕ) (h : n < m) : qBinomial q n m = 0 := by
  induction n, m using qBinomial.induct with
  | case1 n => omega
  | case2 n => simp [qBinomial]
  | case3 n m ih1 ih2 =>
    rw [qBinomial, ih1 (by omega), ih2 (by omega)]; simp

/-- The q-binomial coefficient `qBinomial q n n` equals `1`. -/
lemma qBinomial_self (q : k) : ∀ n : ℕ, qBinomial q n n = 1 := by
  intro n; induction n with
  | zero => simp [qBinomial]
  | succ n ih =>
    rw [qBinomial, qBinomial_eq_zero_of_lt q n (n + 1) (by omega)]; simp [ih]

/-- The unnormalized q-factorial `qFactorial q m = ∏_{i<m} (q^{i+1} - 1)`. -/
noncomputable def qFactorial (q : k) (m : ℕ) : k :=
  ∏ i ∈ Finset.range m, (q ^ (i + 1) - 1)

/-- The q-falling factorial `qFallingFact q n m = ∏_{i<m} (q^{n-i} - 1)`. -/
noncomputable def qFallingFact (q : k) (n m : ℕ) : k :=
  ∏ i ∈ Finset.range m, (q ^ (n - i) - 1)

/-- Recurrence: `qFallingFact q n (m+1) = qFallingFact q n m * (q^{n-m} - 1)`. -/
lemma qFallingFact_succ_last (q : k) (n m : ℕ) :
    qFallingFact q n (m + 1) = qFallingFact q n m * (q ^ (n - m) - 1) := by
  simp [qFallingFact, Finset.prod_range_succ]

/-- Recurrence: `qFactorial q (m+1) = qFactorial q m * (q^{m+1} - 1)`. -/
lemma qFactorial_succ (q : k) (m : ℕ) :
    qFactorial q (m + 1) = qFactorial q m * (q ^ (m + 1) - 1) := by
  simp [qFactorial, Finset.prod_range_succ]

/-- Reindexing recurrence:
`qFallingFact q (n+1) (m+1) = qFallingFact q n m * (q^{n+1} - 1)`. -/
lemma qFallingFact_succ_succ (q : k) (n m : ℕ) :
    qFallingFact q (n + 1) (m + 1) = qFallingFact q n m * (q ^ (n + 1) - 1) := by
  unfold qFallingFact
  rw [Finset.prod_range_succ']
  conv_lhs =>
    rw [show n + 1 - 0 = n + 1 from by omega]
    arg 1; arg 2; ext i
    rw [show n + 1 - (i + 1) = n - i from by omega]

/-- A q-product identity used in the recursive proof of the q-binomial formula:
`q^{m+1}(q^{n-m} - 1) + (q^{m+1} - 1) = q^{n+1} - 1` for `m ≤ n`. -/
lemma q_product_identity (q : k) (n m : ℕ) (hm : m ≤ n) :
    q ^ (m + 1) * (q ^ (n - m) - 1) + (q ^ (m + 1) - 1) = q ^ (n + 1) - 1 := by
  have : m + 1 + (n - m) = n + 1 := by omega
  rw [mul_sub, mul_one, ← pow_add, this]; ring

/-- Product formula for the q-binomial coefficient:
`qBinomial q n m * qFactorial q m = qFallingFact q n m` for `m ≤ n`. -/
theorem qBinomial_product_formula (q : k) : ∀ (n m : ℕ), m ≤ n →
    qBinomial q n m * qFactorial q m = qFallingFact q n m := by
  intro n m
  induction n, m using qBinomial.induct with
  | case1 n => intro _; simp [qFactorial, qFallingFact]
  | case2 n => intro h; omega
  | case3 n m ih_m1 ih_m =>
    intro hle
    have hm : m ≤ n := by omega
    rw [qBinomial, add_mul, qFactorial_succ]
    by_cases hm1 : m + 1 ≤ n
    · have eq1 : qBinomial q n (m + 1) * (qFactorial q m * (q ^ (m + 1) - 1)) =
          qFallingFact q n (m + 1) := by rw [← qFactorial_succ]; exact ih_m1 hm1
      have eq2 : qBinomial q n m * qFactorial q m = qFallingFact q n m := ih_m hm
      calc _ = q ^ (m + 1) * qFallingFact q n (m + 1) +
               qFallingFact q n m * (q ^ (m + 1) - 1) := by
                rw [mul_assoc, eq1, ← mul_assoc, eq2]
        _ = q ^ (m + 1) * (qFallingFact q n m * (q ^ (n - m) - 1)) +
             qFallingFact q n m * (q ^ (m + 1) - 1) := by rw [qFallingFact_succ_last]
        _ = qFallingFact q n m * (q ^ (n + 1) - 1) := by
              linear_combination qFallingFact q n m * q_product_identity q n m hm
        _ = qFallingFact q (n + 1) (m + 1) := by rw [qFallingFact_succ_succ]
    · have hmeq : m = n := by omega
      subst hmeq
      rw [qBinomial_eq_zero_of_lt q m (m + 1) (by omega)]
      simp
      rw [← mul_assoc, ih_m (le_refl m), qFallingFact_succ_succ]

/-- The q-falling factorial `qFallingFact q n m` vanishes when `q^n = 1` and `0 < m`. -/
lemma qFallingFact_eq_zero (q : k) (n m : ℕ) (hqn : q ^ n = 1) (hm : 0 < m) :
    qFallingFact q n m = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr hm) (by simp [hqn])

/-- If `q` is a primitive `n`-th root of unity, then `qFactorial q m ≠ 0` for `m < n`. -/
lemma qFactorial_ne_zero (q : k) (n m : ℕ) (hq : IsPrimitiveRoot q n) (hm : m < n) :
    qFactorial q m ≠ 0 := by
  rw [qFactorial, Finset.prod_ne_zero_iff]
  intro i hi; rw [Finset.mem_range] at hi; rw [sub_ne_zero]
  exact_mod_cast hq.pow_ne_one_of_pos_of_lt (by omega) (by omega)

/-- Vanishing of intermediate q-binomial coefficients at a primitive root of unity:
if `q` is a primitive `n`-th root of unity (`n > 1`) then `qBinomial q n m = 0`
for `0 < m < n`. -/
theorem qBinomial_vanish (q : k) (n : ℕ) (_hn : 1 < n)
    (hq : IsPrimitiveRoot q n) (m : ℕ) (hm1 : 0 < m) (hm2 : m < n) :
    qBinomial q n m = 0 := by
  have hle : m ≤ n := le_of_lt hm2
  have hprod := qBinomial_product_formula q n m hle
  rw [qFallingFact_eq_zero q n m hq.pow_eq_one hm1] at hprod
  exact (mul_eq_zero.mp hprod).resolve_right (qFactorial_ne_zero q n m hq hm2)

section QComm

variable {A : Type*} [Ring A] [Algebra k A]

/-- If `ba = q · ab` then `b^m · a = q^m · (a · b^m)`. -/
lemma q_comm_pow_right (q : k) (a b : A) (hcomm : b * a = algebraMap k A q * (a * b)) :
    ∀ m : ℕ, b ^ m * a = algebraMap k A (q ^ m) * (a * b ^ m) := by
  intro m; induction m with
  | zero => simp
  | succ m ihm =>
    rw [pow_succ b m, mul_assoc (b ^ m) b a, hcomm,
        ← mul_assoc (b ^ m), ← Algebra.commutes q (b ^ m), mul_assoc (algebraMap k A q),
        ← mul_assoc (b ^ m) a b, ihm,
        mul_assoc (algebraMap k A (q ^ m)) (a * b ^ m) b,
        ← mul_assoc (algebraMap k A q) (algebraMap k A (q ^ m)), ← map_mul,
        mul_assoc a (b ^ m) b, ← pow_succ]
    ring_nf

/-- Auxiliary identity used in the proof of the q-binomial expansion: multiplying
`c · a^p b^m` by `(a + b)` produces the expected two-term sum involving a factor
of `q^m`. -/
lemma term_mul_add (q : k) (a b : A) (hcomm : b * a = algebraMap k A q * (a * b))
    (c : k) (p m : ℕ) :
    algebraMap k A c * (a ^ p * b ^ m) * (a + b) =
    algebraMap k A (c * q ^ m) * (a ^ (p + 1) * b ^ m) +
    algebraMap k A c * (a ^ p * b ^ (m + 1)) := by
  rw [mul_add]; congr 1
  · rw [mul_assoc (algebraMap k A c) (a ^ p * b ^ m) a,
        mul_assoc (a ^ p) (b ^ m) a,
        q_comm_pow_right q a b hcomm m,
        ← mul_assoc (a ^ p) (algebraMap k A (q ^ m)) (a * b ^ m),
        ← Algebra.commutes (q ^ m) (a ^ p),
        mul_assoc (algebraMap k A (q ^ m)) (a ^ p) (a * b ^ m),
        ← mul_assoc (a ^ p) a (b ^ m), ← pow_succ,
        ← mul_assoc (algebraMap k A c) (algebraMap k A (q ^ m)), ← map_mul]
  · rw [mul_assoc, mul_assoc, ← pow_succ]

/-- q-Binomial expansion: if `ba = q · ab` in `A` then
`(a+b)^n = ∑_{m=0}^{n} (q-binomial coefficient) · a^{n-m} b^m`. -/
theorem q_binomial_expansion (q : k) (a b : A) (hcomm : b * a = algebraMap k A q * (a * b)) :
    ∀ n : ℕ, (a + b) ^ n =
      ∑ m ∈ Finset.range (n + 1), algebraMap k A (qBinomial q n m) * (a ^ (n - m) * b ^ m) := by
  intro n; induction n with
  | zero => simp [qBinomial]
  | succ n ih =>
    rw [pow_succ, ih, Finset.sum_mul]

    conv_lhs =>
      arg 2; ext m
      rw [term_mul_add q a b hcomm (qBinomial q n m) (n - m) m]

    rw [Finset.sum_add_distrib]


    rw [Finset.sum_range_succ'
          (fun m => algebraMap k A (qBinomial q n m * q ^ m) * (a ^ (n - m + 1) * b ^ m))]

    rw [Finset.sum_range_succ
          (fun m => algebraMap k A (qBinomial q n m) * (a ^ (n - m) * b ^ (m + 1)))]

    rw [show n + 1 + 1 = n + 2 from rfl,
        Finset.sum_range_succ'
          (fun m => algebraMap k A (qBinomial q (n + 1) m) * (a ^ (n + 1 - m) * b ^ m))]
    rw [Finset.sum_range_succ
          (fun m => algebraMap k A (qBinomial q (n + 1) (m + 1)) *
            (a ^ (n + 1 - (m + 1)) * b ^ (m + 1)))]

    simp only [qBinomial, pow_zero, mul_one, map_one, one_mul, Nat.sub_zero,
               qBinomial_self, Nat.sub_self, qBinomial_eq_zero_of_lt q n (n + 1) (by omega)]
    simp only [mul_zero, zero_add, map_one, one_mul]


    suffices h :
      ∑ x ∈ Finset.range n,
        algebraMap k A (qBinomial q n (x + 1) * q ^ (x + 1)) *
          (a ^ (n - (x + 1) + 1) * b ^ (x + 1)) +
      ∑ x ∈ Finset.range n,
        algebraMap k A (qBinomial q n x) * (a ^ (n - x) * b ^ (x + 1)) =
      ∑ x ∈ Finset.range n,
        algebraMap k A (q ^ (x + 1) * qBinomial q n (x + 1) + qBinomial q n x) *
          (a ^ (n + 1 - (x + 1)) * b ^ (x + 1)) by
      calc (∑ x ∈ Finset.range n,
              algebraMap k A (qBinomial q n (x + 1) * q ^ (x + 1)) *
                (a ^ (n - (x + 1) + 1) * b ^ (x + 1)) +
            a ^ (n + 1)) +
          (∑ x ∈ Finset.range n,
              algebraMap k A (qBinomial q n x) * (a ^ (n - x) * b ^ (x + 1)) +
            b ^ (n + 1))
        = (∑ x ∈ Finset.range n,
              algebraMap k A (qBinomial q n (x + 1) * q ^ (x + 1)) *
                (a ^ (n - (x + 1) + 1) * b ^ (x + 1)) +
            ∑ x ∈ Finset.range n,
              algebraMap k A (qBinomial q n x) * (a ^ (n - x) * b ^ (x + 1))) +
            (a ^ (n + 1) + b ^ (n + 1)) := by abel
        _ = ∑ x ∈ Finset.range n,
              algebraMap k A (q ^ (x + 1) * qBinomial q n (x + 1) + qBinomial q n x) *
                (a ^ (n + 1 - (x + 1)) * b ^ (x + 1)) +
            (a ^ (n + 1) + b ^ (n + 1)) := by rw [h]
        _ = (∑ x ∈ Finset.range n,
              algebraMap k A (q ^ (x + 1) * qBinomial q n (x + 1) + qBinomial q n x) *
                (a ^ (n + 1 - (x + 1)) * b ^ (x + 1)) +
            b ^ (n + 1)) + a ^ (n + 1) := by abel

    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_range] at hm
    have hsub1 : n - (m + 1) + 1 = n - m := by omega
    have hsub2 : n + 1 - (m + 1) = n - m := by omega
    rw [hsub1, hsub2, ← add_mul, ← map_add]
    congr 1
    ring_nf

/-- Frobenius-type identity at a primitive root of unity: if `q` is a primitive
`n`-th root of unity (`n > 1`) and `ba = q · ab` in `A`, then `(a + b)^n = a^n + b^n`. -/
theorem q_comm_power (q : k) (n : ℕ) (hn : 1 < n) (hq : IsPrimitiveRoot q n)
    (a b : A) (hcomm : b * a = algebraMap k A q * (a * b)) :
    (a + b) ^ n = a ^ n + b ^ n := by
  rw [q_binomial_expansion q a b hcomm n,
      Finset.sum_range_succ', show n = (n - 1) + 1 from by omega,
      Finset.sum_range_succ]
  simp only [show n - 1 + 1 = n from by omega]
  have hmid : ∑ x ∈ Finset.range (n - 1),
      algebraMap k A (qBinomial q n (x + 1)) * (a ^ (n - (x + 1)) * b ^ (x + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_range] at hm
    rw [qBinomial_vanish q n hn hq (m + 1) (by omega) (by omega), map_zero, zero_mul]
  rw [hmid]
  simp [qBinomial_self, add_comm]

end QComm
