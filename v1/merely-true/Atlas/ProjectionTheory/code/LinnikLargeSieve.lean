/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Complex

noncomputable section

namespace LinnikLargeSieve

/-- The set `P_M` of primes lying in the dyadic interval `[M/2, M]`. -/
def primesInRange (M : ℕ) : Finset ℕ :=
  (Finset.Icc (M / 2) M).filter Nat.Prime

/-- Mod-`p` projection of `f : Fin N → ℂ`: $(\pi_p f)(a) = \sum_{n \equiv a \pmod p} f(n)$. -/
def modProjection (N : ℕ) (p : ℕ) (f : Fin N → ℂ) (a : ZMod p) : ℂ :=
  ∑ n : Fin N, if ((n : ℕ) : ZMod p) = a then f n else 0

/-- Average value of `f : Fin N → ℂ`: $\bar f = \tfrac{1}{N} \sum_n f(n)$. -/
def average (N : ℕ) (f : Fin N → ℂ) : ℂ :=
  (1 / (N : ℂ)) * ∑ n : Fin N, f n

/-- High-frequency part `f_H = f - \bar f` of `f : Fin N → ℂ`. -/
def highFreqPart (N : ℕ) (f : Fin N → ℂ) : Fin N → ℂ :=
  fun n => f n - average N f

/-- Squared $L^2$ norm of `g : ZMod p → ℂ`. -/
def l2NormSq_ZMod (p : ℕ) [NeZero p] (g : ZMod p → ℂ) : ℝ :=
  ∑ a : ZMod p, ‖g a‖ ^ 2

/-- High-frequency part of `g : ZMod p → ℂ`: `g(a) - (1/p) ∑_b g(b)`. -/
def highFreqPart_ZMod (p : ℕ) [NeZero p] (g : ZMod p → ℂ) : ZMod p → ℂ :=
  fun a => g a - (1 / (p : ℂ)) * ∑ b : ZMod p, g b

/-- Squared $L^2$ norm of the high-frequency part of the mod-`p` projection:
`‖(π_p f)_H‖_{L^2}^2`. -/
def projHighFreqL2Sq (N : ℕ) (p : ℕ) [NeZero p] (f : Fin N → ℂ) : ℝ :=
  l2NormSq_ZMod p (highFreqPart_ZMod p (modProjection N p f))

/-- Left-hand side of Linnik's large sieve inequality:
$\sum_{p \in P_M} \|(\pi_p f)_H\|_{L^2}^2$. -/
def linnikLHS (N M : ℕ) (f : Fin N → ℂ) : ℝ :=
  ∑ p ∈ primesInRange M,
    if hp : p = 0 then 0
    else haveI : NeZero p := ⟨hp⟩; projHighFreqL2Sq N p f

/-- Fourier transform on $\mathbb{Z}$: $\hat f(\xi) = \sum_n f(n) e^{-2\pi i \xi n}$. -/
def fourierZ (N : ℕ) (f : Fin N → ℂ) (ξ : ℝ) : ℂ :=
  ∑ n : Fin N, f n * Complex.exp (-2 * ↑Real.pi * Complex.I * ↑ξ * ↑(n : ℕ))



/-- The Farey set $Q_M = \{\alpha/p : p \in P_M, 1 \le \alpha \le p - 1\}$ of reduced
fractions with prime denominator in `P_M`. -/
def fareySet (M : ℕ) : Finset ℝ :=
  (primesInRange M).biUnion fun p =>
    (Finset.Icc 1 (p - 1)).image fun (α : ℕ) => (α : ℝ) / (p : ℝ)

/-- Every element of `fareySet M` lies in `[0, 1)`. -/
lemma fareySet_range (M : ℕ) :
    ∀ x ∈ fareySet M, 0 ≤ x ∧ x < 1 := by
  intro x hx
  simp only [fareySet, mem_biUnion, mem_image, Finset.mem_Icc] at hx
  obtain ⟨p, hp_mem, α, ⟨hα_lo, hα_hi⟩, rfl⟩ := hx
  simp only [primesInRange, mem_filter, Finset.mem_Icc] at hp_mem
  have hp_prime := hp_mem.2
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_prime.pos
  constructor
  · exact div_nonneg (by positivity) hp_pos.le
  · rw [div_lt_one hp_pos]
    exact_mod_cast Nat.lt_of_le_of_lt hα_hi (Nat.sub_lt hp_prime.pos Nat.one_pos)

/-- Separation property of the Farey set: any two distinct $\alpha_1/p_1, \alpha_2/p_2 \in Q_M$
satisfy $|\alpha_1/p_1 - \alpha_2/p_2| \ge 1/M^2$. -/
lemma fareySet_separated (M : ℕ) :
    ∀ x ∈ fareySet M, ∀ y ∈ fareySet M, x ≠ y → (1 : ℝ) / (M ^ 2 : ℝ) ≤ |x - y| := by
  intro x hx y hy hxy
  simp only [fareySet, mem_biUnion, mem_image, Finset.mem_Icc, primesInRange, mem_filter] at hx hy
  obtain ⟨p₁, ⟨hp₁_range, hp₁_prime⟩, α₁, ⟨hα₁_lo, hα₁_hi⟩, hx_eq⟩ := hx
  obtain ⟨p₂, ⟨hp₂_range, hp₂_prime⟩, α₂, ⟨hα₂_lo, hα₂_hi⟩, hy_eq⟩ := hy
  subst hx_eq; subst hy_eq
  have hp₁_pos : (0 : ℝ) < p₁ := Nat.cast_pos.mpr hp₁_prime.pos
  have hp₂_pos : (0 : ℝ) < p₂ := Nat.cast_pos.mpr hp₂_prime.pos
  have hM₁ : p₁ ≤ M := hp₁_range.2
  have hM₂ : p₂ ≤ M := hp₂_range.2
  have hdiff : (α₁ : ℝ) / p₁ - (α₂ : ℝ) / p₂ =
      ((α₁ : ℝ) * p₂ - (α₂ : ℝ) * p₁) / (p₁ * p₂) := by field_simp
  rw [hdiff]
  have hnum_ne : (α₁ : ℤ) * p₂ - (α₂ : ℤ) * p₁ ≠ 0 := by
    intro h
    apply hxy
    have h2 : (α₁ : ℝ) * p₂ = (α₂ : ℝ) * p₁ := by
      have : ((α₁ : ℤ) * (p₂ : ℤ) : ℤ) = ((α₂ : ℤ) * (p₁ : ℤ) : ℤ) := by omega
      exact_mod_cast this
    field_simp; linarith
  have hnum_abs : (1 : ℝ) ≤ |((α₁ : ℝ) * (p₂ : ℝ) - (α₂ : ℝ) * (p₁ : ℝ))| := by
    have h1 : (1 : ℤ) ≤ |((α₁ : ℤ) * p₂ - (α₂ : ℤ) * p₁)| := Int.one_le_abs hnum_ne
    exact_mod_cast h1
  have hprod_le : (p₁ : ℝ) * p₂ ≤ (M : ℝ) ^ 2 := by
    have h : (p₁ * p₂ : ℕ) ≤ M ^ 2 := by
      calc p₁ * p₂ ≤ M * M := Nat.mul_le_mul hM₁ hM₂
        _ = M ^ 2 := (Nat.pow_two M).symm
    exact_mod_cast h
  have hprod_pos : (0 : ℝ) < (p₁ : ℝ) * p₂ := mul_pos hp₁_pos hp₂_pos
  have hM_pos : (0 : ℕ) < M := Nat.pos_of_ne_zero (by
    intro hM0; subst hM0; exact absurd (Nat.le_zero.mp hM₁) (Nat.Prime.ne_zero hp₁_prime))
  have hM2_pos : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hprod_pos]
  rw [div_le_div_iff₀ hM2_pos hprod_pos, one_mul]
  calc (p₁ : ℝ) * p₂ ≤ (M : ℝ) ^ 2 := hprod_le
    _ = 1 * (M : ℝ) ^ 2 := (one_mul _).symm
    _ ≤ |((α₁ : ℝ) * (p₂ : ℝ) - (α₂ : ℝ) * (p₁ : ℝ))| * (M : ℝ) ^ 2 := by gcongr



/-- For distinct primes `p₁, p₂ ∈ P_M`, the corresponding sets of fractions
`{α/p : 1 ≤ α ≤ p - 1}` are disjoint. -/
lemma fareySet_pairwiseDisjoint (M : ℕ) :
    (↑(primesInRange M) : Set ℕ).PairwiseDisjoint fun p =>
      (Finset.Icc 1 (p - 1)).image fun (α : ℕ) => (α : ℝ) / (p : ℝ) := by
  intro p₁ hp₁ p₂ hp₂ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [mem_image, Finset.mem_Icc] at hx₁ hx₂
  obtain ⟨α₁, ⟨hα₁_lo, hα₁_hi⟩, hx₁_eq⟩ := hx₁
  obtain ⟨α₂, ⟨hα₂_lo, hα₂_hi⟩, hx₂_eq⟩ := hx₂
  have hp₁_prime : Nat.Prime p₁ := by
    simp only [primesInRange, mem_coe, mem_filter, Finset.mem_Icc] at hp₁; exact hp₁.2
  have hp₂_prime : Nat.Prime p₂ := by
    simp only [primesInRange, mem_coe, mem_filter, Finset.mem_Icc] at hp₂; exact hp₂.2
  have hp₁_pos : (0 : ℝ) < ↑p₁ := Nat.cast_pos.mpr hp₁_prime.pos
  have hp₂_pos : (0 : ℝ) < ↑p₂ := Nat.cast_pos.mpr hp₂_prime.pos
  have heq : (↑α₁ : ℝ) * ↑p₂ = (↑α₂ : ℝ) * ↑p₁ := by
    have h : (↑α₁ : ℝ) / ↑p₁ = (↑α₂ : ℝ) / ↑p₂ := by linarith
    field_simp at h; linarith
  have heq3 : α₁ * p₂ = α₂ * p₁ := by exact_mod_cast heq
  have hdvd : p₁ ∣ α₁ := by
    have h : p₁ ∣ α₁ * p₂ := ⟨α₂, by linarith⟩
    rcases hp₁_prime.dvd_mul.mp h with h | h
    · exact h
    · exfalso
      rcases hp₂_prime.eq_one_or_self_of_dvd p₁ h with rfl | rfl
      · linarith [hp₁_prime.one_lt]
      · exact hne rfl
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

/-- Sums over the Farey set decompose into double sums over `(p, α)` with `p ∈ P_M`
and `1 ≤ α ≤ p - 1`. -/
lemma sum_over_fareySet (M : ℕ) (g : ℝ → ℝ) :
    ∑ ξ ∈ fareySet M, g ξ =
    ∑ p ∈ primesInRange M, ∑ α ∈ Finset.Icc 1 (p - 1), g ((↑α : ℝ) / (↑p : ℝ)) := by
  unfold fareySet
  rw [Finset.sum_biUnion (fareySet_pairwiseDisjoint M)]
  congr 1; ext p
  apply Finset.sum_image
  intro α₁ hα₁ α₂ _ heq
  have hα₁' := Finset.mem_Icc.mp hα₁
  have hp_pos : (0 : ℝ) < (↑p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  exact_mod_cast (div_left_inj' (ne_of_gt hp_pos)).mp heq



end LinnikLargeSieve

end
