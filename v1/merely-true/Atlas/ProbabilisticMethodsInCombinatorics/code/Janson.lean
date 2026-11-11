/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 800000

open Filter Real
open scoped Topology

noncomputable section

namespace Janson

/-- A Janson setup consists of $N$ independent Bernoulli variables with success probabilities
`prob i ∈ [0,1]` and a family of $k$ "bad events" indexed by subsets $S_i \subseteq \{0,\dots,N-1\}$,
where event $i$ occurs iff every coordinate in $S_i$ is present in the random subset. -/
structure JansonSetup where
  N : ℕ
  k : ℕ
  prob : Fin N → ℝ
  S : Fin k → Finset (Fin N)
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_le_one : ∀ i, prob i ≤ 1

/-- Probability that the $i$-th bad event $A_i$ occurs, i.e.
$\mathbb{P}(A_i) = \prod_{j \in S_i} p_j$. -/
def JansonSetup.probEvent (J : JansonSetup) (i : Fin J.k) : ℝ :=
  ∏ j ∈ J.S i, J.prob j

/-- The expected number of bad events, $\mu = \sum_{i=1}^{k} \mathbb{P}(A_i)$. -/
def JansonSetup.mu (J : JansonSetup) : ℝ :=
  ∑ i : Fin J.k, J.probEvent i

/-- Dependency relation between bad events: events $A_i$ and $A_j$ are dependent iff
$i \ne j$ and $S_i \cap S_j \ne \emptyset$. -/
def JansonSetup.dep (J : JansonSetup) (i j : Fin J.k) : Prop :=
  i ≠ j ∧ (J.S i ∩ J.S j).Nonempty

/-- Decidability of the dependency relation. -/
instance (J : JansonSetup) (i j : Fin J.k) : Decidable (J.dep i j) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Joint probability $\mathbb{P}(A_i \cap A_j) = \prod_{l \in S_i \cup S_j} p_l$. -/
def JansonSetup.probJoint (J : JansonSetup) (i j : Fin J.k) : ℝ :=
  ∏ l ∈ J.S i ∪ J.S j, J.prob l

/-- The dependency parameter $\Delta = \sum_{i \sim j} \mathbb{P}(A_i \cap A_j)$, summed over
ordered dependent pairs $(i,j)$. -/
def JansonSetup.delta (J : JansonSetup) : ℝ :=
  ∑ i : Fin J.k, ∑ j : Fin J.k,
    if J.dep i j then J.probJoint i j else 0

/-- Probability that none of the bad events occur, i.e. $\mathbb{P}(\bigcap_i \overline{A_i})$,
expressed as a sum over the random subset $T$ of coordinates that are present. -/
def JansonSetup.probNone (J : JansonSetup) : ℝ :=
  ∑ T : Finset (Fin J.N),
    (if ∀ i : Fin J.k, ¬(J.S i ⊆ T) then
      (∏ j ∈ T, J.prob j) * (∏ j ∈ Finset.univ.filter (fun j => j ∉ T), (1 - J.prob j))
    else 0)

/-- Probability that the random subset of present coordinates equals exactly $T$. -/
def JansonSetup.probSubset (J : JansonSetup) (T : Finset (Fin J.N)) : ℝ :=
  (∏ i ∈ T, J.prob i) * (∏ i ∈ Finset.univ \ T, (1 - J.prob i))

/-- Given a subset $T$ of present coordinates, counts the number of bad events $A_i$ that
occur, i.e. the number of indices $i$ with $S_i \subseteq T$. -/
def JansonSetup.countEvents (J : JansonSetup) (T : Finset (Fin J.N)) : ℕ :=
  (Finset.univ.filter (fun i => J.S i ⊆ T)).card

/-- Lower-tail probability $\mathbb{P}(X \le \mu - t)$ where $X = \sum_i \mathbf{1}_{A_i}$
counts how many bad events occur. -/
def JansonSetup.probLowerTail (J : JansonSetup) (t : ℝ) : ℝ :=
  ∑ T ∈ Finset.powerset Finset.univ,
    if (J.countEvents T : ℝ) ≤ J.mu - t then J.probSubset T else 0



/-- Expected number of triangles in $G(n,p)$: $\mu = \binom{n}{3} p^3$. -/
def mu_triangles (n : ℕ) (p : ℝ) : ℝ :=
  (n.choose 3 : ℝ) * p ^ 3

/-- Janson dependency parameter for triangles in $G(n,p)$: counts ordered pairs of
triangles sharing an edge, weighted by the joint probability $p^5$. -/
def delta_triangles (n : ℕ) (p : ℝ) : ℝ :=
  (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * p ^ 5

/-- Auxiliary asymptotic estimate: if $p(n) \sqrt{n} \to 0$ then
$\Delta_{\triangle}(n, p(n)) / \mu_{\triangle}(n, p(n)) \to 0$. -/
theorem triangle_free_delta_over_mu_tendsto
    (p : ℕ → ℝ)
    (hp_pos : ∀ᶠ n in atTop, 0 < p n)
    (hp_small : Tendsto (fun n => p n * Real.sqrt n) atTop (𝓝 0)) :
    Tendsto (fun (n : ℕ) => delta_triangles n (p n) / mu_triangles n (p n)) atTop (𝓝 0) := by

  have hp2n : Tendsto (fun (n : ℕ) => (n : ℝ) * (p n) ^ 2) atTop (𝓝 0) := by
    have h := hp_small.pow 2
    simp only [zero_pow (by norm_num : 2 ≠ 0)] at h
    refine h.congr' ?_
    filter_upwards with n
    simp only [mul_pow, sq_sqrt (Nat.cast_nonneg' n)]
    ring


  have h3np2 : Tendsto (fun (n : ℕ) => 3 * ((n : ℝ) * (p n) ^ 2)) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = 3 * 0 from by ring]
    exact hp2n.const_mul 3
  apply squeeze_zero_norm' _ h3np2
  filter_upwards [hp_pos, Filter.eventually_ge_atTop 4] with n hn hn4
  simp only [delta_triangles, mu_triangles]
  have hp_nn : (0 : ℝ) < p n := hn
  have hn_cast : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hcn3_pos : (0 : ℝ) < (n.choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hmu_pos : (0 : ℝ) < (n.choose 3 : ℝ) * p n ^ 3 :=
    mul_pos hcn3_pos (pow_pos hp_nn 3)
  have h_ratio_nonneg : 0 ≤ (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * p n ^ 5 /
      ((n.choose 3 : ℝ) * p n ^ 3) := by
    apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact_mod_cast Nat.zero_le _
          · linarith
        · linarith
      · exact pow_nonneg (le_of_lt hp_nn) 5
    · exact le_of_lt hmu_pos
  rw [Real.norm_of_nonneg h_ratio_nonneg]
  rw [show p n ^ 5 = p n ^ 2 * p n ^ 3 from by ring]
  rw [show (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * (p n ^ 2 * p n ^ 3) /
      ((n.choose 3 : ℝ) * p n ^ 3) =
      (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) / (n.choose 3 : ℝ) * p n ^ 2 from by
    field_simp]

  have h_nat_bound : n.choose 2 * (n - 2) * (n - 3) ≤ 3 * n * n.choose 3 := by
    have h_c3_rel : n.choose 2 * (n - 2) = 3 * n.choose 3 := by
      have h := Nat.choose_succ_right_eq n 2
      simp only [show 2 + 1 = 3 from rfl] at h
      rw [Nat.choose_two_right] at h ⊢; omega
    nlinarith [Nat.sub_le n 3, h_c3_rel]
  have h_real_bound : (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) ≤
      3 * (n : ℝ) * (n.choose 3 : ℝ) := by
    have h_lhs_eq : (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) =
        ((n.choose 2 * (n - 2) * (n - 3) : ℕ) : ℝ) := by
      push_cast
      simp [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n)]
    have h_rhs_eq : 3 * (n : ℝ) * (n.choose 3 : ℝ) =
        ((3 * n * n.choose 3 : ℕ) : ℝ) := by
      push_cast; ring
    rw [h_lhs_eq, h_rhs_eq]; exact_mod_cast h_nat_bound
  calc (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) / (n.choose 3 : ℝ) * p n ^ 2
      ≤ 3 * (n : ℝ) * p n ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hcn3_pos]
        nlinarith [sq_nonneg (p n), h_real_bound]
    _ = 3 * ((n : ℝ) * p n ^ 2) := by ring

/-- Closed-form for $\binom{n}{3}$ cast to $\mathbb{R}$: $\binom{n}{3} = n(n-1)(n-2)/6$. -/
lemma choose_three_cast (n : ℕ) (hn : 3 ≤ n) :
    (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
  have h_desc : n.descFactorial 3 = n * (n - 1) * (n - 2) := by
    simp [Nat.descFactorial]; ring
  rw [Nat.choose_eq_descFactorial_div_factorial, h_desc]
  have h_div6 : 6 ∣ n * (n - 1) * (n - 2) := by
    rw [← h_desc, show (6 : ℕ) = (3 : ℕ).factorial from by norm_num]
    exact Nat.factorial_dvd_descFactorial n 3
  rw [show (3 : ℕ).factorial = 6 from by norm_num]
  have h_cast : (↑(n * (n - 1) * (n - 2)) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  rw [Nat.cast_div h_div6 (by norm_num : (6 : ℝ) ≠ 0), h_cast]
  norm_num

/-- Auxiliary limit: $(c/n) \sqrt{n} = c/\sqrt{n} \to 0$ as $n \to \infty$. -/
lemma const_div_n_mul_sqrt_tendsto (c : ℝ) :
    Tendsto (fun n : ℕ => c / (n : ℝ) * Real.sqrt n) atTop (𝓝 0) := by
  have heq : ∀ᶠ n : ℕ in atTop, c / (n : ℝ) * Real.sqrt n = c / Real.sqrt n := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    rw [div_mul_eq_mul_div, show c * Real.sqrt n / (n : ℝ) = c * (Real.sqrt n / n) from by ring]
    congr 1
    field_simp
    exact Real.sq_sqrt (le_of_lt hn_pos)
  have hlim : Tendsto (fun n : ℕ => c / Real.sqrt n) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  exact hlim.congr' (heq.mono fun n h => h.symm)

/-- Asymptotic limit: $\mu_{\triangle}(n, c/n) = \binom{n}{3}(c/n)^3 \to c^3/6$. -/
theorem mu_triangles_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => mu_triangles n (c / (n : ℝ))) atTop (𝓝 (c ^ 3 / 6)) := by
  have key : ∀ᶠ n : ℕ in atTop, mu_triangles n (c / (n : ℝ)) =
      c ^ 3 / 6 * (1 - 1 / (n : ℝ)) * (1 - 2 / (n : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    simp only [mu_triangles]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    rw [choose_three_cast n (by omega : 3 ≤ n)]
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    field_simp
  have hlim : Tendsto (fun n : ℕ => c ^ 3 / 6 * (1 - 1 / (n : ℝ)) * (1 - 2 / (n : ℝ)))
      atTop (𝓝 (c ^ 3 / 6)) := by
    have h_inv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h_factor1 : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h_inv
    have h_factor2 : Tendsto (fun n : ℕ => 1 - 2 / (n : ℝ)) atTop (𝓝 1) := by
      have h2inv : Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
        have := h_inv.const_mul 2
        simp only [mul_one_div, mul_zero] at this
        exact this
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h2inv
    conv_rhs => rw [show c ^ 3 / 6 = c ^ 3 / 6 * 1 * 1 from by ring]
    exact ((tendsto_const_nhds.mul h_factor1).mul h_factor2)
  exact hlim.congr' (key.mono fun n h => h.symm)

/-- Specialization of `triangle_free_delta_over_mu_tendsto` to $p = c/n$:
$\Delta_{\triangle}(n, c/n) / \mu_{\triangle}(n, c/n) \to 0$. -/
theorem cor_triangle_free_delta_over_mu (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => delta_triangles n (c / (n : ℝ)) / mu_triangles n (c / (n : ℝ)))
      atTop (𝓝 0) := by
  apply triangle_free_delta_over_mu_tendsto
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact div_pos hc (by exact_mod_cast (show 0 < n by omega))
  · exact const_div_n_mul_sqrt_tendsto c

/-- Auxiliary limit: $\Delta_{\triangle}(n, c/n) \to 0$ as $n \to \infty$. -/
lemma delta_triangles_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => delta_triangles n (c / (n : ℝ))) atTop (𝓝 0) := by
  have hmu := mu_triangles_tendsto c hc
  have h_ratio := cor_triangle_free_delta_over_mu c hc
  have hmu_pos : ∀ᶠ n : ℕ in atTop, 0 < mu_triangles n (c / (n : ℝ)) := by
    have : (0 : ℝ) < c ^ 3 / 6 := by positivity
    exact hmu.eventually (eventually_gt_nhds this)
  have heq : ∀ᶠ n : ℕ in atTop, delta_triangles n (c / (n : ℝ)) =
      (delta_triangles n (c / (n : ℝ)) / mu_triangles n (c / (n : ℝ))) *
        mu_triangles n (c / (n : ℝ)) := by
    filter_upwards [hmu_pos] with n hn
    rw [div_mul_cancel₀]; exact ne_of_gt hn
  rw [show (0 : ℝ) = 0 * (c ^ 3 / 6) from by ring]
  exact (h_ratio.mul hmu).congr' (heq.mono fun n h => h.symm)

/-- Corollary 8.1.7. Abstract form: if a probability sequence is sandwiched between
$\exp(-\mu_n)$ and $\exp(-\mu_n + \Delta_n/2)$ for the triangle counts in $G(n, c/n)$, then
$-\log(\text{prob}_n) \to c^3/6$. -/
theorem corollary_8_1_7 (c : ℝ) (hc : 0 < c)
    (prob_tf : ℕ → ℝ)
    (hprob_pos : ∀ᶠ n in atTop, 0 < prob_tf n)
    (_hprob_le : ∀ᶠ n in atTop, prob_tf n ≤ 1)

    (h_upper : ∀ᶠ n in atTop,
      prob_tf n ≤ Real.exp (-(mu_triangles n (c / n)) + delta_triangles n (c / n) / 2))

    (h_lower : ∀ᶠ n in atTop,
      Real.exp (-(mu_triangles n (c / n))) ≤ prob_tf n) :
    Tendsto (fun n : ℕ => -Real.log (prob_tf n)) atTop (𝓝 (c ^ 3 / 6)) := by

  have h_squeeze_lower : ∀ᶠ n in atTop,
      mu_triangles n (c / n) - delta_triangles n (c / n) / 2 ≤ -Real.log (prob_tf n) := by
    filter_upwards [h_upper, hprob_pos] with n hu hp
    have h1 : Real.log (prob_tf n) ≤
        -(mu_triangles n (c / n)) + delta_triangles n (c / n) / 2 := by
      calc Real.log (prob_tf n)
          ≤ Real.log (Real.exp (-(mu_triangles n (c / n)) + delta_triangles n (c / n) / 2)) :=
            Real.log_le_log hp hu
        _ = -(mu_triangles n (c / n)) + delta_triangles n (c / n) / 2 := Real.log_exp _
    linarith
  have h_squeeze_upper : ∀ᶠ n in atTop,
      -Real.log (prob_tf n) ≤ mu_triangles n (c / n) := by
    filter_upwards [h_lower, hprob_pos] with n hl _hp
    have h1 : -(mu_triangles n (c / n)) ≤ Real.log (prob_tf n) := by
      calc -(mu_triangles n (c / n))
          = Real.log (Real.exp (-(mu_triangles n (c / n)))) := (Real.log_exp _).symm
        _ ≤ Real.log (prob_tf n) := Real.log_le_log (Real.exp_pos _) hl
    linarith

  have h_lower_lim : Tendsto (fun n : ℕ =>
      mu_triangles n (c / n) - delta_triangles n (c / n) / 2) atTop (𝓝 (c ^ 3 / 6)) := by
    have h_half_delta : Tendsto (fun n : ℕ => delta_triangles n (c / (n : ℝ)) / 2)
        atTop (𝓝 0) := by
      rw [show (0 : ℝ) = 0 / 2 from by ring]
      exact (delta_triangles_tendsto_zero c hc).div_const 2
    conv_rhs => rw [show c ^ 3 / 6 = c ^ 3 / 6 - 0 from by ring]
    exact (mu_triangles_tendsto c hc).sub h_half_delta

  have h_upper_lim : Tendsto (fun n : ℕ => mu_triangles n (c / (n : ℝ)))
      atTop (𝓝 (c ^ 3 / 6)) := mu_triangles_tendsto c hc

  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_lim h_upper_lim
    h_squeeze_lower h_squeeze_upper

/-- Probability that $G(n,p)$ is triangle-free, computed under the binomial random graph
measure on $\mathrm{Fin}\, n$. -/
def triangleFreeProb (n : ℕ) (p : ↑unitInterval) : ℝ :=
  (SimpleGraph.binomialRandom (Fin n) p).real {G | G.CliqueFree 3}

/-- Triangle-free probability at edge density $p = c/n$, returning $0$ if $c/n$ falls
outside the unit interval. -/
def triangleFreeProb_cn (c : ℝ) (n : ℕ) : ℝ :=
  if h : c / (n : ℝ) ∈ unitInterval then
    triangleFreeProb n ⟨c / (n : ℝ), h⟩
  else 0






end Janson

namespace JansonInequalities

open Filter Asymptotics Real

/-- Theorem 8.1.6/8.1.7/8.1.8 (Janson II). Optimization of the parametric Janson bound:
if for every $q \in [0,1]$ we have $v \le \exp(-q\mu + q^2 \Delta / 2)$, then
$v \le \exp(-\mu^2 / (2\Delta))$, by choosing $q = \mu/\Delta$. -/
theorem janson_inequality_II
    {μ Δ v : ℝ} (hμ_pos : 0 < μ) (hΔ_ge_μ : Δ ≥ μ)
    (hbound : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → v ≤ Real.exp (-q * μ + q ^ 2 * Δ / 2)) :
    v ≤ Real.exp (-(μ ^ 2) / (2 * Δ)) := by
  have hΔ_pos : (0 : ℝ) < Δ := lt_of_lt_of_le hμ_pos hΔ_ge_μ
  have hq_nonneg : (0 : ℝ) ≤ μ / Δ := div_nonneg (le_of_lt hμ_pos) (le_of_lt hΔ_pos)
  have hq_le_one : μ / Δ ≤ 1 := div_le_one_of_le₀ hΔ_ge_μ (le_of_lt hΔ_pos)
  have key := hbound (μ / Δ) hq_nonneg hq_le_one
  suffices h : -(μ / Δ) * μ + (μ / Δ) ^ 2 * Δ / 2 = -(μ ^ 2) / (2 * Δ) by
    rwa [h] at key
  field_simp
  ring

/-- Asymptotic identity: if $\mu \asymp n^3 p^3$ and $\Delta \asymp n^4 p^5$, then
$\mu^2 / (2\Delta) \asymp n^2 p$, the natural Janson II exponent for triangles. -/
theorem mu_sq_over_delta_isTheta
    (μ Δ p : ℕ → ℝ)
    (hμ_theta : μ =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 3 * p n ^ 3))
    (hΔ_theta : Δ =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 4 * p n ^ 5))
    (hp_pos : ∀ᶠ (n : ℕ) in atTop, 0 < p n)
    (hn_pos : ∀ᶠ (n : ℕ) in atTop, (0 : ℝ) < n)
    (hΔ_pos : ∀ᶠ (n : ℕ) in atTop, 0 < Δ n) :
    (fun n : ℕ => μ n ^ 2 / (2 * Δ n)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 * p n) := by
  have hμ_sq : (fun n : ℕ => μ n ^ 2) =Θ[atTop]
      (fun n : ℕ => ((n : ℝ) ^ 3 * p n ^ 3) ^ 2) := hμ_theta.pow 2
  have hμ_sq_div_Δ : (fun n : ℕ => μ n ^ 2 / Δ n) =Θ[atTop]
      (fun n : ℕ => ((n : ℝ) ^ 3 * p n ^ 3) ^ 2 / ((n : ℝ) ^ 4 * p n ^ 5)) :=
    hμ_sq.div hΔ_theta
  have h_simp : (fun n : ℕ => ((n : ℝ) ^ 3 * p n ^ 3) ^ 2 / ((n : ℝ) ^ 4 * p n ^ 5))
      =ᶠ[atTop] (fun n : ℕ => (n : ℝ) ^ 2 * p n) := by
    filter_upwards [hp_pos, hn_pos] with n hp hn
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn
    have hp_ne : p n ≠ 0 := ne_of_gt hp
    field_simp
  have h4 : (fun n : ℕ => μ n ^ 2 / Δ n) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 * p n) :=
    hμ_sq_div_Δ.trans h_simp.isTheta
  have h5 : (fun n : ℕ => μ n ^ 2 / (2 * Δ n)) =ᶠ[atTop]
      (fun n : ℕ => (1 / 2 : ℝ) * (μ n ^ 2 / Δ n)) := by
    filter_upwards [hΔ_pos] with n hΔ
    have hΔ_ne : Δ n ≠ 0 := ne_of_gt hΔ
    field_simp
  have h6 : (fun n : ℕ => (1 / 2 : ℝ) * (μ n ^ 2 / Δ n)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 * p n) := by
    rwa [Asymptotics.isTheta_const_mul_left (show (1 / 2 : ℝ) ≠ 0 from by norm_num)]
  exact h5.isTheta.trans h6

/-- Bundle of asymptotic data for triangles in $G(n, p(n))$: triangle-free probability,
Janson parameters $\mu$ and $\Delta$ with their correct asymptotic order. -/
structure TriangleFreeGnpData (p : ℕ → ℝ) where
  prob_tf : ℕ → ℝ
  μ : ℕ → ℝ
  Δ : ℕ → ℝ
  prob_tf_pos : ∀ᶠ n in atTop, 0 < prob_tf n
  prob_tf_le_one : ∀ᶠ n in atTop, prob_tf n ≤ 1
  μ_isTheta : μ =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 3 * p n ^ 3)
  Δ_isTheta : Δ =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 4 * p n ^ 5)
  Δ_pos : ∀ᶠ n in atTop, 0 < Δ n

/-- For any fixed $k \in \mathbb{N}$, $(n - k) \asymp n$ as $n \to \infty$. -/
lemma isTheta_natCast_sub_const (k : ℕ) :
    (fun n : ℕ => (n : ℝ) - (k : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
  constructor
  · apply IsBigO.of_bound 1
    filter_upwards [Filter.eventually_ge_atTop k] with n hn
    simp only [one_mul]
    have hk : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by positivity)]
    linarith
  · apply IsBigO.of_bound 2
    filter_upwards [Filter.eventually_ge_atTop (2 * k)] with n hn
    have hk : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show k ≤ n from by omega)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by linarith)]
    have : (n : ℝ) / 2 ≤ (n : ℝ) - k := by
      have hcast : (2 * k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    linarith

/-- Constructs a `TriangleFreeGnpData` bundle for a probability sequence $p(n)$ that is
eventually positive and bounded away from $1$. The triangle-free probability used is the
naive empty-graph bound $(1-p)^{\binom{n}{2}}$ for the lower bound. -/
def triangleFreeGnpData_exists (p : ℕ → ℝ)
    (hp_pos : ∀ᶠ n in atTop, 0 < p n)
    (hp_le : ∀ᶠ n in atTop, p n ≤ 0.99) :
    TriangleFreeGnpData p := by
  refine ⟨fun n => (1 - p n) ^ Nat.choose n 2,
         fun n => Janson.mu_triangles n (p n),
         fun n => Janson.delta_triangles n (p n), ?_, ?_, ?_, ?_, ?_⟩
  ·
    filter_upwards [hp_pos, hp_le] with n hp hle
    apply pow_pos; linarith
  ·
    filter_upwards [hp_pos, hp_le] with n hp hle
    apply pow_le_one₀ (by linarith) (by linarith)
  ·
    show (fun n : ℕ => (n.choose 3 : ℝ) * p n ^ 3) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ 3 * p n ^ 3)
    exact (isTheta_choose 3).mul (isTheta_refl _ _)
  ·
    show (fun n : ℕ => (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * p n ^ 5) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ 4 * p n ^ 5)
    have h_coeff : (fun n : ℕ => (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ 4) := by
      have h1 := isTheta_choose 2
      have h2 := isTheta_natCast_sub_const 2
      have h3 := isTheta_natCast_sub_const 3
      have hmul := h1.mul h2 |>.mul h3
      have heq : (fun n : ℕ => (n : ℝ) ^ 2 * (↑n) * (↑n)) = (fun n : ℕ => (n : ℝ) ^ 4) := by
        ext n; ring
      rwa [heq] at hmul
    exact h_coeff.mul (isTheta_refl _ _)
  ·
    filter_upwards [hp_pos, Filter.eventually_ge_atTop 4] with n hp hn
    simp only [Janson.delta_triangles]
    have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
      have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hn3 : (0 : ℝ) < (n : ℝ) - 3 := by
      have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hcn2 : (0 : ℝ) < (n.choose 2 : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n)
    apply mul_pos
    · apply mul_pos
      · exact mul_pos hcn2 hn2
      · exact hn3
    · positivity







end JansonInequalities

namespace Janson

open Real



end Janson
