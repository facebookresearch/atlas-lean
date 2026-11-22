/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-- An absolute value on a field $k$ is an `AbsoluteValue` with codomain $\mathbb{R}$. -/
abbrev AbsoluteValueOnField (k : Type*) [Field k] := AbsoluteValue k ℝ

namespace AbsoluteValueOnField

variable {k : Type*} [Field k] (v : AbsoluteValueOnField k)

/-- The value $v(x)$ of an absolute value is always non-negative: $0 \le v(x)$. -/
theorem nonneg (x : k) : 0 ≤ v x :=
  AbsoluteValue.nonneg v x

/-- Non-degeneracy of an absolute value: $v(x) = 0 \iff x = 0$. -/
theorem eq_zero_iff (x : k) : v x = 0 ↔ x = 0 :=
  AbsoluteValue.eq_zero v


/-- Theorem 5.3(c), forward direction: if $v$ is nonarchimedean then $v(n) \le 1$ for every
$n \in \mathbb{N}$. -/
theorem thm_5_3c_forward (hna : IsNonarchimedean (v : k → ℝ)) (n : ℕ) : v (n : k) ≤ 1 := by
  rw [show (n : k) = n • (1 : k) from by simp]
  exact le_trans hna.nsmul_le (le_of_eq v.map_one)

/-- Binomial-type bound: assuming $v(n) \le 1$ for every $n$, one has
$v(x+y)^n \le (n+1) \max(v(x), v(y))^n$ for all $n$. -/
lemma binomial_bound (hv : ∀ n : ℕ, v (n : k) ≤ 1) (x y : k) (n : ℕ) :
    v (x + y) ^ n ≤ ((n : ℝ) + 1) * max (v x) (v y) ^ n := by
  rw [show v (x + y) ^ n = v ((x + y) ^ n) from (map_pow v _ n).symm]
  rw [(Commute.all x y).add_pow n]
  calc v (∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * ↑(n.choose m))
      ≤ ∑ m ∈ Finset.range (n + 1), v (x ^ m * y ^ (n - m) * ↑(n.choose m)) :=
        v.sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (n + 1), max (v x) (v y) ^ n := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_range] at hm
        simp only [map_mul, map_pow]
        calc v x ^ m * v y ^ (n - m) * v (↑(n.choose m))
            ≤ v x ^ m * v y ^ (n - m) * 1 := by gcongr; exact hv _
          _ = v x ^ m * v y ^ (n - m) := mul_one _
          _ ≤ max (v x) (v y) ^ m * max (v x) (v y) ^ (n - m) := by
              apply mul_le_mul
              · exact pow_le_pow_left₀ (v.nonneg x) (le_max_left _ _) m
              · exact pow_le_pow_left₀ (v.nonneg y) (le_max_right _ _) (n - m)
              · positivity
              · positivity
          _ = max (v x) (v y) ^ n := by rw [← pow_add]; congr 1; omega
    _ = ((n : ℝ) + 1) * max (v x) (v y) ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- If $r^n \le (n+1) M^n$ holds for every natural number $n$ (with $M \ge 0$), then $r \le M$. -/
lemma le_of_pow_le_mul_pow (r M : ℝ) (hM : 0 ≤ M)
    (h : ∀ n : ℕ, r ^ n ≤ ((n : ℝ) + 1) * M ^ n) : r ≤ M := by
  by_contra hlt
  push Not at hlt
  rcases eq_or_lt_of_le hM with rfl | hM_pos
  · have h1 := h 1; simp at h1; linarith
  · have hrM : 1 < r / M := by rwa [one_lt_div₀ hM_pos]
    have key : ∀ n : ℕ, (r / M) ^ n ≤ (n : ℝ) + 1 := by
      intro n; rw [div_pow, div_le_iff₀ (pow_pos hM_pos n)]; exact h n
    obtain ⟨m, hm⟩ := Real.exists_natCast_add_one_lt_pow_of_one_lt hrM
    exact not_le.mpr hm (key m)

/-- Theorem 5.3(c), backward direction: if $v(n) \le 1$ for every $n \in \mathbb{N}$, then $v$ is
nonarchimedean. -/
theorem thm_5_3c_backward (hv : ∀ n : ℕ, v (n : k) ≤ 1) :
    IsNonarchimedean (v : k → ℝ) := by
  intro x y
  exact le_of_pow_le_mul_pow (v (x + y)) (max (v x) (v y))
    (le_max_of_le_left (v.nonneg x)) (binomial_bound v hv x y)

/-- Theorem 5.3(c): an absolute value $v$ is nonarchimedean iff $v(n) \le 1$ for all natural
numbers $n$. -/
theorem thm_5_3c : IsNonarchimedean (v : k → ℝ) ↔ ∀ n : ℕ, v (n : k) ≤ 1 :=
  ⟨thm_5_3c_forward v, thm_5_3c_backward v⟩

/-- If $a > 0$, $n \ne 0$, and $a^n = 1$, then $a = 1$. -/
lemma eq_one_of_pow_eq_one_of_pos {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : n ≠ 0)
    (h : a ^ n = 1) : a = 1 := by
  by_contra hne
  rcases ne_iff_lt_or_gt.mp hne with hlt | hgt
  · exact absurd h (ne_of_lt (by simpa using pow_lt_pow_left₀ hlt ha.le hn))
  · exact absurd h (ne_of_gt (by simpa using pow_lt_pow_left₀ hgt (by linarith) hn))

/-- In a field $k$ of characteristic $p$, the Frobenius identity reads
$(n : k)^p = n$ for every natural number $n$. -/
lemma natCast_pow_charP (p : ℕ) [CharP k p] [Fact (Nat.Prime p)] (n : ℕ) :
    (n : k) ^ p = (n : k) := by
  haveI : ExpChar k p := expChar_prime k p
  rw [← frobenius_def p (n : k)]
  exact map_natCast (frobenius k p) n

/-- Fermat's little theorem in $k$: if $\mathrm{char}(k) = p$ is prime and $(n : k) \ne 0$, then
$(n : k)^{p-1} = 1$. -/
lemma natCast_pow_char_sub_one_eq_one (p : ℕ) [CharP k p] [hp : Fact (Nat.Prime p)]
    (n : ℕ) (hn : (n : k) ≠ 0) : (n : k) ^ (p - 1) = 1 := by
  have h := natCast_pow_charP (k := k) p n
  have hpp : 0 < p := hp.out.pos
  have h2 : (n : k) ^ (p - 1) * (n : k) = (n : k) := by
    rw [← pow_succ]; rw [show p - 1 + 1 = p from by omega]; exact h
  calc (n : k) ^ (p - 1)
      = (n : k) ^ (p - 1) * ((n : k) * (n : k)⁻¹) := by rw [mul_inv_cancel₀ hn, mul_one]
    _ = ((n : k) ^ (p - 1) * (n : k)) * (n : k)⁻¹ := by ring
    _ = (n : k) * (n : k)⁻¹ := by rw [h2]
    _ = 1 := mul_inv_cancel₀ hn

/-- Corollary 5.4: any absolute value on a field of prime characteristic is nonarchimedean. -/
theorem cor_5_4_nonarchimedean (p : ℕ) [CharP k p] [hp : Fact (Nat.Prime p)] :
    IsNonarchimedean (v : k → ℝ) := by
  apply thm_5_3c_backward
  intro n
  by_cases hn : (n : k) = 0
  · simp [hn, v.map_zero]
  ·
    have h := natCast_pow_char_sub_one_eq_one (k := k) p n hn
    have hv : v (n : k) ^ (p - 1) = 1 := by
      rw [← map_pow v (n : k) (p - 1), h, v.map_one]
    have hvpos : 0 < v (n : k) := by rwa [AbsoluteValue.pos_iff]
    have hp1 : p - 1 ≠ 0 := by have := hp.out.one_lt; omega
    linarith [eq_one_of_pow_eq_one_of_pos hvpos hp1 hv]


end AbsoluteValueOnField

noncomputable section

namespace AbsoluteValueOnField

variable {k : Type*} [Field k]

/-- Definition 5.5: two absolute values $v_1, v_2$ on $k$ are *equivalent* if there exists
$\alpha > 0$ such that $v_2(x) = v_1(x)^\alpha$ for every $x \in k$. -/
def AreEquivalent (v₁ v₂ : AbsoluteValue k ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ x : k, v₂ x = (v₁ x) ^ α

/-- The custom `AreEquivalent` relation coincides with the Mathlib `AbsoluteValue.IsEquiv`
relation. -/
theorem areEquivalent_iff_isEquiv (v₁ v₂ : AbsoluteValue k ℝ) :
    AreEquivalent v₁ v₂ ↔ v₁.IsEquiv v₂ := by
  rw [AbsoluteValue.isEquiv_iff_exists_rpow_eq]
  constructor
  · rintro ⟨α, hα, h⟩
    exact ⟨α, hα, funext fun x => (h x).symm⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun x => (congr_fun h x).symm⟩

end AbsoluteValueOnField

namespace AbsoluteValueOnField

variable {k : Type*} [Field k]

/-- Theorem 5.6 (Ostrowski's theorem for $\mathbb{Q}$): every nontrivial absolute value on
$\mathbb{Q}$ is equivalent either to the real absolute value $|\cdot|_\infty$ or to a $p$-adic
absolute value $|\cdot|_p$ for some prime $p$. -/
theorem ostrowski (v : AbsoluteValue ℚ ℝ) (hv : v.IsNontrivial) :
    AreEquivalent v Rat.AbsoluteValue.real ∨
    ∃ p : ℕ, ∃ (_ : Fact p.Prime), AreEquivalent v (Rat.AbsoluteValue.padic p) := by


  have h := Rat.AbsoluteValue.equiv_real_or_padic v hv


  cases h with
  | inl hreal =>

    exact Or.inl <| (areEquivalent_iff_isEquiv v _).mpr hreal
  | inr hpadic =>

    obtain ⟨p, ⟨hp, _⟩⟩ := hpadic
    obtain ⟨hfact, hequiv⟩ := hp
    exact Or.inr ⟨p, hfact, (areEquivalent_iff_isEquiv v _).mpr hequiv⟩


end AbsoluteValueOnField

end
