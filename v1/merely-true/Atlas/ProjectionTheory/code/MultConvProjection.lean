/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.MultiplicativeConvolution
import Atlas.ProjectionTheory.code.LinnikLargeSieve

open Finset Complex Nat BigOperators

noncomputable section

namespace MultiplicativeConvolution

/-- Multiplicative convolution on `ZMod q`:
$(f *_M g)(a) = \sum_{b, c \in \mathbb{Z}/q,\ bc = a} f(b)\, g(c)$. -/
def mulConv_ZMod (q : ℕ) [NeZero q] (f g : ZMod q → ℂ) (a : ZMod q) : ℂ :=
  ∑ b : ZMod q, ∑ c : ZMod q, if b * c = a then f b * g c else 0

/-- The projection $\pi_q f : \mathbb{Z}/q \to \mathbb{C}$ of an arithmetic function
$f : \mathbb{N} \to \mathbb{C}$ truncated to $[0, N)$: at $a \in \mathbb{Z}/q$ it sums
$f(n)$ over $n < N$ with $n \equiv a \pmod q$. -/
def modProjection_arith (N : ℕ) (q : ℕ) [NeZero q] (f : ℕ → ℂ) (a : ZMod q) : ℂ :=
  ∑ n ∈ Finset.range N, if ((n : ℕ) : ZMod q) = a then f n else 0

/-- Swap the order of four nested sums (two over `ZMod q`, two over `Finset.range N`)
so that the `n, m` sums are outermost — used to rearrange double sums in the
projection-of-convolution computation. -/
lemma sum_comm4 (N q : ℕ) [NeZero q] (h : ZMod q → ZMod q → ℕ → ℕ → ℂ) :
    (∑ b : ZMod q, ∑ c : ZMod q, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, h b c n m) =
    (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∑ b : ZMod q, ∑ c : ZMod q, h b c n m) := by
  trans (∑ b : ZMod q, ∑ n ∈ Finset.range N, ∑ c : ZMod q, ∑ m ∈ Finset.range N, h b c n m)
  · apply Finset.sum_congr rfl; intro b _; exact Finset.sum_comm
  trans (∑ n ∈ Finset.range N, ∑ b : ZMod q, ∑ c : ZMod q, ∑ m ∈ Finset.range N, h b c n m)
  · exact Finset.sum_comm
  apply Finset.sum_congr rfl; intro n _
  trans (∑ b : ZMod q, ∑ m ∈ Finset.range N, ∑ c : ZMod q, h b c n m)
  · apply Finset.sum_congr rfl; intro b _; exact Finset.sum_comm
  trans (∑ m ∈ Finset.range N, ∑ b : ZMod q, ∑ c : ZMod q, h b c n m)
  · exact Finset.sum_comm
  · rfl

/-- Expanding the mod-$q$ multiplicative convolution of two truncated projections:
$\bigl(\pi_q f *_M \pi_q g\bigr)(a) = \sum_{n, m < N,\ nm \equiv a} f(n)\, g(m)$. -/
lemma mulConv_ZMod_eq_double_sum (N q : ℕ) [NeZero q] (f g : ℕ → ℂ) (a : ZMod q) :
    mulConv_ZMod q (modProjection_arith N q f) (modProjection_arith N q g) a =
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      if ((n : ℕ) : ZMod q) * ((m : ℕ) : ZMod q) = a then f n * g m else 0 := by
  simp only [mulConv_ZMod, modProjection_arith]
  have prod_expand : ∀ b c : ZMod q,
    (∑ n ∈ Finset.range N, if ((n : ℕ) : ZMod q) = b then f n else 0) *
    (∑ m ∈ Finset.range N, if ((m : ℕ) : ZMod q) = c then g m else 0) =
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      (if ((n : ℕ) : ZMod q) = b then f n else 0) *
      (if ((m : ℕ) : ZMod q) = c then g m else 0) := by
    intro b c; rw [Finset.sum_mul]; congr 1; ext n; rw [Finset.mul_sum]
  have push_if : ∀ b c : ZMod q,
    (if b * c = a then
      (∑ n ∈ Finset.range N, if ((n : ℕ) : ZMod q) = b then f n else 0) *
      (∑ m ∈ Finset.range N, if ((m : ℕ) : ZMod q) = c then g m else 0)
    else 0) =
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      (if ((n : ℕ) : ZMod q) = b ∧ ((m : ℕ) : ZMod q) = c ∧ b * c = a
       then f n * g m else 0) := by
    intro b c
    rw [prod_expand]
    by_cases hbc : b * c = a
    · simp only [hbc, ite_true]
      apply Finset.sum_congr rfl; intro n _
      apply Finset.sum_congr rfl; intro m _
      by_cases hb : ((n : ℕ) : ZMod q) = b <;> by_cases hc : ((m : ℕ) : ZMod q) = c <;>
        simp [hb, hc, hbc]
    · simp only [hbc, ite_false, and_false, Finset.sum_const_zero]
  simp_rw [push_if]
  rw [sum_comm4]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro m _
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext y; arg 2; ext x
    rw [show (if ((n : ℕ) : ZMod q) = x ∧ ((m : ℕ) : ZMod q) = y ∧ x * y = a
             then f n * g m else 0) =
      (if ((n : ℕ) : ZMod q) = x then
        (if ((m : ℕ) : ZMod q) = y ∧ x * y = a then f n * g m else 0)
      else 0) from by split_ifs <;> tauto]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  conv_lhs =>
    arg 2; ext y
    rw [show (if ((m : ℕ) : ZMod q) = y ∧ ((n : ℕ) : ZMod q) * y = a
             then f n * g m else 0) =
      (if ((m : ℕ) : ZMod q) = y then
        (if ((n : ℕ) : ZMod q) * y = a then f n * g m else 0)
      else 0) from by split_ifs <;> tauto]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- If $f, g$ are supported on positive integers $< N$, then for $n < N^2$ the truncated
product-sum $\sum_{(d_1, d_2) \in [0,N)^2,\ d_1 d_2 = n} f(d_1) g(d_2)$ equals the sum over
the full divisor antidiagonal $\sum_{d_1 d_2 = n} f(d_1) g(d_2)$. -/
lemma sum_product_eq_sum_divisorsAntidiagonal (N : ℕ) (f g : ℕ → ℂ)
    (hf : ∀ n, N ≤ n → f n = 0) (hg : ∀ n, N ≤ n → g n = 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (n : ℕ) (hn : n < N * N) :
    (∑ x ∈ (Finset.range N ×ˢ Finset.range N).filter (fun x => x.1 * x.2 = n),
      f x.1 * g x.2) =
    ∑ x ∈ Nat.divisorsAntidiagonal n, f x.1 * g x.2 := by
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Nat.divisorsAntidiagonal_zero, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro ⟨d1, d2⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    have hprod : d1 * d2 = 0 := hx.2
    rcases Nat.eq_zero_or_pos d1 with hd1 | hd1
    · simp [hd1, hf0]
    · have hd2 : d2 = 0 := (Nat.mul_eq_zero.mp hprod).resolve_left (Nat.pos_iff_ne_zero.mp hd1)
      simp [hd2, hg0]
  · apply Finset.sum_subset
    · intro ⟨d1, d2⟩ hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
      rw [Nat.mem_divisorsAntidiagonal]
      exact ⟨hx.2, hn0⟩
    · intro ⟨d1, d2⟩ hd hd_not
      rw [Nat.mem_divisorsAntidiagonal] at hd
      have h : ¬(d1 < N ∧ d2 < N) := by
        intro ⟨h1, h2⟩
        apply hd_not
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨h1, h2⟩, hd.1⟩
      by_cases hd1 : d1 < N
      · have hd2 : N ≤ d2 := by
          by_contra hlt; push Not at hlt; exact h ⟨hd1, hlt⟩
        simp [hg d2 hd2]
      · simp [hf d1 (by omega)]

/-- Projection of multiplicative convolution (pointwise form): if $f, g$ are supported on
positive integers $< N$, then $\pi_q(f *_M g)(a) = (\pi_q f *_M \pi_q g)(a)$, where the
truncation on the left is taken at $N^2$. -/
theorem modProjection_mulConv (N q : ℕ) [NeZero q] (f g : ℕ → ℂ)
    (hf : ∀ n, N ≤ n → f n = 0) (hg : ∀ n, N ≤ n → g n = 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (a : ZMod q) :
    modProjection_arith (N * N) q (mulConv f g) a =
    mulConv_ZMod q (modProjection_arith N q f) (modProjection_arith N q g) a := by
  rw [mulConv_ZMod_eq_double_sum]
  simp only [modProjection_arith, mulConv]

  simp_rw [show ∀ (n m : ℕ), ((n : ℕ) : ZMod q) * ((m : ℕ) : ZMod q) = ((n * m : ℕ) : ZMod q)
    from by intros; push_cast; ring]

  rw [← Finset.sum_product']
  have hmaps : ∀ x ∈ (Finset.range N) ×ˢ (Finset.range N),
      x.1 * x.2 ∈ Finset.range (N * N) := by
    intro ⟨d1, d2⟩ hx
    simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
    exact Nat.mul_lt_mul'' hx.1 hx.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl; intro n hn
  simp only [Finset.mem_range] at hn

  have h_ind : ∀ x ∈ (Finset.range N ×ˢ Finset.range N).filter (fun x => x.1 * x.2 = n),
    (if ((x.1 * x.2 : ℕ) : ZMod q) = a then f x.1 * g x.2 else 0) =
    (if ((n : ℕ) : ZMod q) = a then f x.1 * g x.2 else 0) := by
    intro x hx; simp only [Finset.mem_filter] at hx; rw [hx.2]
  rw [Finset.sum_congr rfl h_ind]

  split_ifs with ha
  ·
    exact (sum_product_eq_sum_divisorsAntidiagonal N f g hf hg hf0 hg0 n hn).symm
  ·
    simp

/-- Projection-of-convolution identity for `ArithmeticFunction`s: with the support hypotheses
on $f, g$, we have $\pi_q(f * g)(a) = (\pi_q f *_M \pi_q g)(a)$ (here `f * g` is Dirichlet
convolution of arithmetic functions). -/
theorem modProjection_mulConv_arithFun (N q : ℕ) [NeZero q]
    (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, N ≤ n → f n = 0) (hg : ∀ n, N ≤ n → g n = 0) (a : ZMod q) :
    modProjection_arith (N * N) q (fun n => (f * g) n) a =
    mulConv_ZMod q (modProjection_arith N q f) (modProjection_arith N q g) a := by
  have key := modProjection_mulConv N q (fun n => f n) (fun n => g n) hf hg
    f.map_zero g.map_zero a
  simp only [show (fun n => (f * g) n) = mulConv (fun n => f n) (fun n => g n) from by
    ext n; rw [← mulConv_eq_arithmeticFunction_mul]] at key ⊢
  exact key

/-- Functional form of the projection-of-convolution identity: under the support hypotheses,
$\pi_q(f *_M g) = \pi_q f *_M \pi_q g$ as functions on $\mathbb{Z}/q$. -/
theorem modProjection_mulConv_arithFun' (N q : ℕ) [NeZero q]
    (f g : ℕ → ℂ)
    (hf : ∀ n, N ≤ n → f n = 0) (hg : ∀ n, N ≤ n → g n = 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) :
    modProjection_arith (N * N) q (mulConv f g) =
    mulConv_ZMod q (modProjection_arith N q f) (modProjection_arith N q g) := by
  funext a
  exact modProjection_mulConv N q f g hf hg hf0 hg0 a

/-- The mod-$q$ projection of $f$ on $\mathbb{N}$ truncated to $1 \le n < N$ (positive
integers only): $\pi_q^+ f(a) = \sum_{0 < n < N,\ n \equiv a} f(n)$. -/
def modProjection_pos (N : ℕ) (q : ℕ) [NeZero q] (f : ℕ → ℂ) (a : ZMod q) : ℂ :=
  ∑ n ∈ (Finset.range N).filter (· ≠ 0), if ((n : ℕ) : ZMod q) = a then f n else 0

/-- Modify $f : \mathbb{N} \to \mathbb{C}$ so that its value at $0$ is set to $0$, leaving
all other values unchanged. -/
def zeroAt0 (f : ℕ → ℂ) : ℕ → ℂ := fun n => if n = 0 then 0 else f n

/-- `zeroAt0 f` vanishes at $0$. -/
lemma zeroAt0_zero (f : ℕ → ℂ) : zeroAt0 f 0 = 0 := if_pos rfl

/-- If $f$ is supported on $n < N$, so is `zeroAt0 f`. -/
lemma zeroAt0_support (f : ℕ → ℂ) (N : ℕ) (hf : ∀ n, N ≤ n → f n = 0) :
    ∀ n, N ≤ n → zeroAt0 f n = 0 := by
  intro n hn
  unfold zeroAt0
  split
  · rfl
  · exact hf n hn

/-- The positive-truncation projection equals the arithmetic projection of $f$ with its value
at $0$ zeroed out: $\pi_q^+ f = \pi_q (\mathrm{zeroAt0}\, f)$. -/
lemma modProjection_pos_eq_arith_zeroAt0 (N q : ℕ) [NeZero q] (f : ℕ → ℂ)
    (a : ZMod q) :
    modProjection_pos N q f a = modProjection_arith N q (zeroAt0 f) a := by
  simp only [modProjection_pos, modProjection_arith, zeroAt0]
  conv_rhs =>
    arg 2; ext n
    rw [show (if ((n : ℕ) : ZMod q) = a then if n = 0 then 0 else f n else 0) =
      (if n ≠ 0 then (if ((n : ℕ) : ZMod q) = a then f n else 0) else 0) from by
        split_ifs <;> simp_all]
  rw [Finset.sum_filter]

/-- For $n \ne 0$, the multiplicative convolution $(f *_M g)(n)$ is unchanged if we replace
$f, g$ by their `zeroAt0` modifications (the value at $0$ does not contribute when $n > 0$). -/
lemma mulConv_pos_eq_zeroAt0 (f g : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) :
    mulConv f g n = mulConv (zeroAt0 f) (zeroAt0 g) n := by
  simp only [mulConv, zeroAt0]
  apply Finset.sum_congr rfl
  intro ⟨d1, d2⟩ hd
  rw [Nat.mem_divisorsAntidiagonal] at hd
  have hd1 : d1 ≠ 0 := by intro h; rw [h, zero_mul] at hd; exact hn hd.1.symm
  have hd2 : d2 ≠ 0 := by intro h; rw [h, mul_zero] at hd; exact hn hd.1.symm
  simp [hd1, hd2]

/-- Projection of multiplicative convolution (positive-truncation version):
if $f, g$ are supported on $n < N$, then
$\pi_q^+(f *_M g) = \pi_q^+ f *_M \pi_q^+ g$ as functions on $\mathbb{Z}/q$. -/
theorem modProjection_mulConv_pos (N q : ℕ) [NeZero q] (f g : ℕ → ℂ)
    (hf : ∀ n, N ≤ n → f n = 0) (hg : ∀ n, N ≤ n → g n = 0) :
    modProjection_pos (N * N) q (mulConv f g) =
    mulConv_ZMod q (modProjection_pos N q f) (modProjection_pos N q g) := by


  have lhs_eq : ∀ a, modProjection_pos (N * N) q (mulConv f g) a =
      modProjection_arith (N * N) q (mulConv (zeroAt0 f) (zeroAt0 g)) a := by
    intro a
    rw [modProjection_pos_eq_arith_zeroAt0]
    congr 1; funext n
    simp only [zeroAt0]; split_ifs with h
    · subst h; simp [mulConv, Nat.divisorsAntidiagonal_zero]
    · exact mulConv_pos_eq_zeroAt0 f g n h
  have rhs_eq : ∀ a, mulConv_ZMod q (modProjection_pos N q f) (modProjection_pos N q g) a =
      mulConv_ZMod q (modProjection_arith N q (zeroAt0 f))
        (modProjection_arith N q (zeroAt0 g)) a := by
    intro a
    simp only [mulConv_ZMod]
    congr 1; ext b; congr 1; ext c
    split_ifs with h
    · congr 1
      · exact modProjection_pos_eq_arith_zeroAt0 N q f b
      · exact modProjection_pos_eq_arith_zeroAt0 N q g c
    · rfl
  funext a
  rw [lhs_eq, rhs_eq]
  exact congr_fun (modProjection_mulConv_arithFun' N q (zeroAt0 f) (zeroAt0 g)
    (zeroAt0_support f N hf) (zeroAt0_support g N hg)
    (zeroAt0_zero f) (zeroAt0_zero g)) a

end MultiplicativeConvolution

end
