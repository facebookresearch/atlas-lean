/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Real.Lemmas
set_option maxHeartbeats 800000

noncomputable section

open Filter Topology Finset BigOperators

namespace RandomGraph

/-- Linear index assigned to an unordered pair $\{a, b\}$ with $a < b$, given by
$\binom{b}{2} + a$. Used to enumerate edges of the complete graph $K_n$ as
elements of $\mathrm{Fin}\binom{n}{2}$. -/
def pairToEdgeIndex (a b : ℕ) : ℕ := Nat.choose b 2 + a

/-- The index of a pair with $a < b < n$ lies below $\binom{n}{2}$, ensuring that
`pairToEdgeIndex` produces a valid `Fin (Nat.choose n 2)`. -/
lemma pairToEdgeIndex_lt_choose {a b n : ℕ} (hab : a < b) (hbn : b < n) :
    pairToEdgeIndex a b < Nat.choose n 2 := by
  unfold pairToEdgeIndex
  have h1 : Nat.choose b 2 + a < Nat.choose b 2 + b := Nat.add_lt_add_left hab _
  have h2 : Nat.choose b 2 + b = Nat.choose (b + 1) 2 := by
    simp [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  rw [h2] at h1
  exact lt_of_lt_of_le h1 (Nat.choose_le_choose 2 hbn)

/-- Edge index of the ordered pair $(i, j)$ with $i < j$ in $K_n$, as an element of
$\mathrm{Fin}\binom{n}{2}$. -/
def edgeIndex (n : ℕ) (i j : Fin n) (hij : i.val < j.val) : Fin (Nat.choose n 2) :=
  ⟨pairToEdgeIndex i.val j.val, pairToEdgeIndex_lt_choose hij j.isLt⟩

/-- Tests whether the edge $\{i, j\}$ is present according to the bit-vector $f$
encoding a graph on $n$ vertices; returns false unless $i < j$. -/
def edgePresent (n : ℕ) (f : Fin (Nat.choose n 2) → Bool) (i j : Fin n) : Bool :=
  if h : i.val < j.val then f (edgeIndex n i j h) else false

/-- Decides whether the graph on $n$ vertices encoded by $f$ contains a triangle, by
searching for an ordered triple $i < j < k$ with all three edges present. -/
def hasTriangle (n : ℕ) (f : Fin (Nat.choose n 2) → Bool) : Bool :=
  (Finset.univ.val : Multiset (Fin n × Fin n × Fin n)).toList.any fun ijk =>
    let i := ijk.1
    let j := ijk.2.1
    let k := ijk.2.2
    edgePresent n f i j && edgePresent n f i k && edgePresent n f j k &&
    decide (i.val < j.val) && decide (j.val < k.val)

/-- The probability that $G(n, p)$ contains a triangle, computed by summing the
indicator of `hasTriangle` weighted by the Bernoulli$(p)$ product weights over all
$2^{\binom{n}{2}}$ edge configurations. -/
def erdosRenyiTriangleProb (n : ℕ) (p : ℝ) : ℝ :=
  let m := Nat.choose n 2
  ∑ f : Fin m → Bool,
    (if hasTriangle n f then 1 else 0) *
    ∏ i : Fin m, (if f i then p else 1 - p)

/-- Each product Bernoulli weight $\prod_i (\text{if } f_i \text{ then } p \text{ else } 1-p)$
is nonnegative whenever $0 \le p \le 1$. -/
lemma bernoulli_weight_nonneg {m : ℕ} (f : Fin m → Bool) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (0 : ℝ) ≤ ∏ i : Fin m, (if f i then p else 1 - p) := by
  apply Finset.prod_nonneg
  intro i _; split_ifs <;> linarith

/-- The product Bernoulli$(p)$ weights summed over $\{0,1\}^m$ equal $1$, by the
binomial identity $(p + (1-p))^m = 1$. -/
lemma sum_bernoulli_weights (m : ℕ) (p : ℝ) :
    ∑ f : Fin m → Bool, ∏ i : Fin m, (if f i then p else 1 - p) = 1 := by
  have key : (∑ f : Fin m → Bool, ∏ i : Fin m, (if f i then p else 1 - p))
    = ∏ _i : Fin m, (p + (1 - p)) := by
    symm
    calc ∏ _i : Fin m, (p + (1 - p))
        = ∏ i : Fin m, ∑ b : Bool, (if b then p else 1 - p) := by
          congr 1; ext i; rw [Fintype.sum_bool]; simp
      _ = ∑ x ∈ Fintype.piFinset (fun (_ : Fin m) => Finset.univ (α := Bool)),
            ∏ i : Fin m, (if x i then p else 1 - p) := by
          rw [Finset.prod_univ_sum]
      _ = ∑ f : Fin m → Bool, ∏ i : Fin m, (if f i then p else 1 - p) := by
          rw [Fintype.piFinset_univ]
  rw [key]; simp [add_sub_cancel]

/-- The triangle-containment probability in $G(n, p)$ is nonnegative for $p \in [0, 1]$. -/
theorem erdosRenyiTriangleProb_nonneg (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ erdosRenyiTriangleProb n p := by
  unfold erdosRenyiTriangleProb
  apply Finset.sum_nonneg
  intro f _
  apply mul_nonneg
  · split_ifs <;> linarith
  · exact bernoulli_weight_nonneg f p hp hp1

/-- The triangle-containment probability in $G(n, p)$ is at most $1$ for $p \in [0, 1]$. -/
theorem erdosRenyiTriangleProb_le_one (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    erdosRenyiTriangleProb n p ≤ 1 := by
  unfold erdosRenyiTriangleProb
  have hsum : ∑ f : Fin (Nat.choose n 2) → Bool,
      ∏ i : Fin (Nat.choose n 2), (if f i then p else 1 - p) = 1 :=
    sum_bernoulli_weights _ p
  calc ∑ f : Fin (Nat.choose n 2) → Bool,
        (if hasTriangle n f then (1 : ℝ) else 0) *
        ∏ i : Fin (Nat.choose n 2), (if f i then p else 1 - p)
      ≤ ∑ f : Fin (Nat.choose n 2) → Bool,
        ∏ i : Fin (Nat.choose n 2), (if f i then p else 1 - p) := by
        apply Finset.sum_le_sum
        intro f _
        have hprod := bernoulli_weight_nonneg f p hp hp1
        split_ifs with h
        · linarith [one_mul (∏ i : Fin (Nat.choose n 2), (if f i then p else 1 - p))]
        · linarith [zero_mul (∏ i : Fin (Nat.choose n 2), (if f i then p else 1 - p))]
    _ = 1 := hsum

/-- The expected number of triangles in $G(n, p)$, given by
$\mathbb{E}[X] = \binom{n}{3} p^3$ (Proposition 4.1.2). -/
noncomputable def expectedTriangles (n : ℕ) (p : ℝ) : ℝ :=
  (Nat.choose n 3 : ℝ) * p ^ 3

/-- The expected number of triangles in $G(n, p)$ is nonnegative when $p \ge 0$. -/
lemma expectedTriangles_nonneg (n : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    0 ≤ expectedTriangles n p :=
  mul_nonneg (Nat.cast_nonneg' _) (pow_nonneg hp 3)





/-- Upper bound for the expected number of triangles:
$\binom{n}{3} p^3 \le (np)^3 / 6$, using $\binom{n}{3} \le n^3/3!$. -/
lemma expectedTriangles_le (n : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    expectedTriangles n p ≤ ((↑n : ℝ) * p) ^ 3 / 6 := by
  unfold expectedTriangles
  have h6 : (6 : ℝ) = (Nat.factorial 3 : ℝ) := by norm_num [Nat.factorial]
  have hchoose : (Nat.choose n 3 : ℝ) ≤ ((n : ℝ) ^ 3) / (Nat.factorial 3 : ℝ) :=
    Nat.choose_le_pow_div 3 n
  have hp3 : (0 : ℝ) ≤ p ^ 3 := pow_nonneg hp 3
  calc (Nat.choose n 3 : ℝ) * p ^ 3
      ≤ ((n : ℝ) ^ 3 / (Nat.factorial 3 : ℝ)) * p ^ 3 :=
        mul_le_mul_of_nonneg_right hchoose hp3
    _ = ((n : ℝ) * p) ^ 3 / 6 := by
        rw [h6]; ring

/-- If $np_n \to 0$ then the expected number of triangles tends to $0$, by squeezing
$\binom{n}{3} p_n^3$ between $0$ and $(np_n)^3 / 6$. -/
theorem expectedTriangles_tendsto_zero
    (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (h : Tendsto (fun (n : ℕ) => (↑n : ℝ) * p n) atTop (𝓝 0)) :
    Tendsto (fun (n : ℕ) => expectedTriangles n (p n)) atTop (𝓝 0) := by
  have hcube : Tendsto (fun (n : ℕ) => ((↑n : ℝ) * p n) ^ 3) atTop (𝓝 0) := by
    have h3 := h.pow 3
    simp only [zero_pow (by norm_num : 3 ≠ 0)] at h3
    exact h3
  have hbound : Tendsto (fun (n : ℕ) => ((↑n : ℝ) * p n) ^ 3 / 6) atTop (𝓝 0) := by
    have h6 := hcube.div_const (6 : ℝ)
    simp only [zero_div] at h6
    exact h6
  apply squeeze_zero'
  · exact Eventually.of_forall (fun (n : ℕ) => by
      unfold expectedTriangles
      exact mul_nonneg (Nat.cast_nonneg' (Nat.choose n 3)) (pow_nonneg (hp n) 3))
  · exact Eventually.of_forall (fun (n : ℕ) => expectedTriangles_le n (p n) (hp n))
  · exact hbound

/-- **Below-threshold side of the triangle threshold.** If $np_n \to 0$ and a triangle
probability sequence is bounded above by the first moment, then it tends to $0$. -/
theorem triangleThreshold_below
    (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (probTriangle : ℕ → ℝ)
    (hprob_nonneg : ∀ n, 0 ≤ probTriangle n)
    (hMarkov : ∀ n, probTriangle n ≤ expectedTriangles n (p n))
    (hpn : Tendsto (fun (n : ℕ) => (n : ℝ) * p n) atTop (nhds 0)) :
    Tendsto probTriangle atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall hprob_nonneg
  · exact Eventually.of_forall hMarkov
  · exact expectedTriangles_tendsto_zero p hp hpn

section VarianceRatio

set_option maxHeartbeats 1600000

/-- For $n \ge 4$, $n^3 \le 48 \binom{n}{3}$, providing a lower bound for $\binom{n}{3}$
in terms of $n^3$. -/
lemma nat_cube_le_48_choose_three (n : ℕ) (hn : 4 ≤ n) :
    n ^ 3 ≤ 48 * Nat.choose n 3 := by
  have hdesc : Nat.descFactorial n 3 = 6 * Nat.choose n 3 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; norm_num [Nat.factorial]
  have hdesc2 : Nat.descFactorial n 3 = n * (n - 1) * (n - 2) := by
    simp [Nat.descFactorial_succ, Nat.descFactorial_zero]; ring
  have h8 : n ^ 3 ≤ 8 * (n * (n - 1) * (n - 2)) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [show 4 + m - 1 = m + 3 from by omega, show 4 + m - 2 = m + 2 from by omega]
    nlinarith [Nat.zero_le m, sq_nonneg m]
  linarith [hdesc ▸ hdesc2]

/-- Real-valued version of the inequality $n^3 / 48 \le \binom{n}{3}$ for $n \ge 4$. -/
lemma choose_three_ge (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) ^ 3 / 48 ≤ (Nat.choose n 3 : ℝ) := by
  have h48 := nat_cube_le_48_choose_three n hn
  have hcast : (n : ℝ) ^ 3 ≤ 48 * (Nat.choose n 3 : ℝ) := by exact_mod_cast h48
  linarith

/-- Lower bound for the expected number of triangles:
$(np)^3 / 48 \le \binom{n}{3} p^3$ for $n \ge 4$. -/
lemma expectedTriangles_ge (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hn : 4 ≤ n) :
    ((↑n : ℝ) * p) ^ 3 / 48 ≤ expectedTriangles n p := by
  unfold expectedTriangles
  have hchoose := choose_three_ge n hn
  calc ((↑n : ℝ) * p) ^ 3 / 48
      = (↑n : ℝ) ^ 3 / 48 * p ^ 3 := by ring
    _ ≤ (Nat.choose n 3 : ℝ) * p ^ 3 :=
        mul_le_mul_of_nonneg_right hchoose (pow_nonneg hp 3)

/-- A bound on the variance-numerator term: when $np \ge 1$,
$\binom{n}{3} p^3 + \binom{n}{4} p^5 \le (np)^4$. -/
lemma variance_numerator_le (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hnp : 1 ≤ (↑n : ℝ) * p) :
    expectedTriangles n p + (↑(Nat.choose n 4) : ℝ) * p ^ 5 ≤ ((↑n : ℝ) * p) ^ 4 := by
  have hnp_nn : (0 : ℝ) ≤ (↑n : ℝ) * p := le_trans zero_le_one hnp
  have h1 : expectedTriangles n p ≤ ((↑n : ℝ) * p) ^ 3 / 6 :=
    expectedTriangles_le n p hp
  have h2 : (↑(Nat.choose n 4) : ℝ) * p ^ 5 ≤ ((↑n : ℝ) * p) ^ 4 / 24 := by
    have hc4 : (Nat.choose n 4 : ℝ) ≤ (↑n : ℝ) ^ 4 / ↑(Nat.factorial 4) :=
      @Nat.choose_le_pow_div ℝ _ _ _ 4 n
    calc (↑(Nat.choose n 4) : ℝ) * p ^ 5
        ≤ ((↑n : ℝ) ^ 4 / ↑(Nat.factorial 4)) * p ^ 5 :=
          mul_le_mul_of_nonneg_right hc4 (pow_nonneg hp 5)
      _ = ((↑n : ℝ) * p) ^ 4 * p / 24 := by norm_num [Nat.factorial]; ring
      _ ≤ ((↑n : ℝ) * p) ^ 4 * 1 / 24 := by
          have : ((↑n : ℝ) * p) ^ 4 * p ≤ ((↑n : ℝ) * p) ^ 4 * 1 :=
            mul_le_mul_of_nonneg_left hp1 (pow_nonneg hnp_nn 4)
          exact div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 24)
      _ = ((↑n : ℝ) * p) ^ 4 / 24 := by ring
  have h3 : ((↑n : ℝ) * p) ^ 3 ≤ ((↑n : ℝ) * p) ^ 4 := by
    calc ((↑n : ℝ) * p) ^ 3 = ((↑n : ℝ) * p) ^ 3 * 1 := (mul_one _).symm
      _ ≤ ((↑n : ℝ) * p) ^ 3 * ((↑n : ℝ) * p) :=
          mul_le_mul_of_nonneg_left hnp (pow_nonneg hnp_nn 3)
      _ = ((↑n : ℝ) * p) ^ 4 := by ring
  linarith [pow_nonneg hnp_nn 4]

/-- If $np_n \to \infty$, then the variance-over-squared-mean ratio for the triangle
count tends to $0$, the key second-moment input for the above-threshold direction. -/
theorem triangle_variance_ratio_tendsto_zero
    (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (hpn : Tendsto (fun (n : ℕ) => (n : ℝ) * p n) atTop atTop) :
    Tendsto (fun n => (expectedTriangles n (p n) + (↑(Nat.choose n 4) : ℝ) * (p n) ^ 5) /
      (expectedTriangles n (p n)) ^ 2) atTop (nhds 0) := by
  set f := fun (n : ℕ) => (expectedTriangles n (p n) + (↑(Nat.choose n 4) : ℝ) * (p n) ^ 5) /
      (expectedTriangles n (p n)) ^ 2
  set g := fun (n : ℕ) => (2304 : ℝ) / ((↑n : ℝ) * p n) ^ 2

  have hnp2 : Tendsto (fun (n : ℕ) => ((↑n : ℝ) * p n) ^ 2) atTop atTop := by
    apply Filter.tendsto_atTop.mpr; intro b
    filter_upwards [Filter.tendsto_atTop.mp hpn (max b 1)] with n hn
    calc b ≤ (↑n : ℝ) * p n := le_of_max_le_left hn
      _ ≤ ((↑n : ℝ) * p n) ^ 2 := le_self_pow₀ (le_of_max_le_right hn) (by norm_num)

  have hg : Tendsto g atTop (𝓝 0) := hnp2.const_div_atTop 2304

  show Tendsto f atTop (𝓝 0)
  apply squeeze_zero'
  ·
    apply Eventually.of_forall; intro n
    apply div_nonneg
    · exact add_nonneg (expectedTriangles_nonneg n (p n) (hp n))
        (mul_nonneg (Nat.cast_nonneg' _) (pow_nonneg (hp n) 5))
    · exact sq_nonneg _
  ·
    filter_upwards [Filter.tendsto_atTop.mp hpn 1,
                    Filter.eventually_ge_atTop 4] with n hnp1 hn4

    have hnp_pos : (0 : ℝ) < (↑n : ℝ) * p n := lt_of_lt_of_le one_pos hnp1
    have hnp_nn := hnp_pos.le
    have hmu_lower := expectedTriangles_ge n (p n) (hp n) hn4
    have hmu_pos : (0 : ℝ) < expectedTriangles n (p n) := by linarith [pow_pos hnp_pos 3]
    have hmu_sq_pos : (0 : ℝ) < (expectedTriangles n (p n)) ^ 2 := sq_pos_of_pos hmu_pos
    have hnum := variance_numerator_le n (p n) (hp n) (hp1 n) hnp1
    have hmu_sq_lower : ((↑n : ℝ) * p n) ^ 6 / 2304 ≤ (expectedTriangles n (p n)) ^ 2 := by
      have h_sq : (((↑n : ℝ) * p n) ^ 3 / 48) ^ 2 ≤ (expectedTriangles n (p n)) ^ 2 :=
        sq_le_sq' (by linarith [hmu_pos, pow_pos hnp_pos 3]) hmu_lower
      linarith [show (((↑n : ℝ) * p n) ^ 3 / 48) ^ 2 = ((↑n : ℝ) * p n) ^ 6 / 2304 from by ring]

    have hnp6_pos : (0 : ℝ) < ((↑n : ℝ) * p n) ^ 6 / 2304 := by positivity
    calc f n = (expectedTriangles n (p n) + (↑(Nat.choose n 4) : ℝ) * (p n) ^ 5) /
          (expectedTriangles n (p n)) ^ 2 := rfl
      _ ≤ ((↑n : ℝ) * p n) ^ 4 / (expectedTriangles n (p n)) ^ 2 := by
          exact div_le_div_of_nonneg_right hnum hmu_sq_pos.le
      _ ≤ ((↑n : ℝ) * p n) ^ 4 / (((↑n : ℝ) * p n) ^ 6 / 2304) := by
          exact div_le_div_of_nonneg_left (by positivity) hnp6_pos hmu_sq_lower
      _ = 2304 / ((↑n : ℝ) * p n) ^ 2 := by
          have hne : ((↑n : ℝ) * p n) ≠ 0 := ne_of_gt hnp_pos
          field_simp [hne]
      _ = g n := rfl
  · exact hg

end VarianceRatio



end RandomGraph
