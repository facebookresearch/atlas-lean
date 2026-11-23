/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Entropy
import Mathlib.Probability.Distributions.Uniform

set_option maxHeartbeats 800000

open Finset Real

namespace ShannonEntropy

/-- The support of a PMF on a finite type, returned as a `Finset`: the set of
elements $s$ with $p(s) \neq 0$. -/
noncomputable def supportFinset {S : Type*} [Fintype S] (p : PMF S) : Finset S :=
  Finset.univ.filter (fun s => p s ≠ 0)

/-- The finset support of any PMF is nonempty. -/
lemma supportFinset_nonempty {S : Type*} [Fintype S] (p : PMF S) :
    (supportFinset p).Nonempty := by
  rw [supportFinset, Finset.filter_nonempty_iff]
  obtain ⟨a, ha⟩ := p.support_nonempty
  exact ⟨a, Finset.mem_univ a, (p.mem_support_iff a).mp ha⟩

/-- Membership in the finset support: $s \in \text{supportFinset}(p) \iff p(s) \neq 0$. -/
lemma mem_supportFinset_iff {S : Type*} [Fintype S] (p : PMF S) (s : S) :
    s ∈ supportFinset p ↔ p s ≠ 0 := by
  simp [supportFinset]

/-- The support of the uniform PMF on a nonempty finset $s$ is exactly $s$. -/
lemma supportFinset_uniformOfFinset {S : Type*} [Fintype S] (s : Finset S) (hs : s.Nonempty) :
    supportFinset (PMF.uniformOfFinset s hs) = s := by
  ext x
  simp only [supportFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [PMF.uniformOfFinset_apply hs]
  constructor
  · intro h; by_contra hx; simp [hx] at h
  · intro hx; simp only [hx, ↓reduceIte]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top s.card)

/-- The Shannon entropy can be computed by summing over the support only:
$H(p) = \sum_{s \in \text{supp}(p)} \text{negMulLog}(p(s))$. -/
lemma shannonEntropy_eq_sum_support {S : Type*} [Fintype S] (p : PMF S) :
    shannonEntropy p = ∑ s ∈ supportFinset p, negMulLog (p s).toReal := by
  simp only [shannonEntropy]; symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx; simp [Finset.mem_filter] at hx; simp [hx, negMulLog_zero]

/-- The probabilities on the support sum to one: $\sum_{s \in \text{supp}(p)} p(s) = 1$. -/
lemma sum_support_toReal_eq_one {S : Type*} [Fintype S] (p : PMF S) :
    ∑ s ∈ supportFinset p, (p s).toReal = 1 := by
  have h := pmf_sum_toReal_eq_one p
  rw [show (∑ t : S, (p t).toReal) = ∑ t ∈ (univ : Finset S), (p t).toReal from rfl] at h
  rw [← h]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx; simp at hx; simp [hx]

/-- The Shannon entropy of the uniform distribution on a nonempty finset $s$ is
$\log |s|$ (the natural-log analogue of the textbook's $\log_2$ version). -/
lemma entropy_uniformOfFinset {S : Type*} [Fintype S] (s : Finset S) (hs : s.Nonempty) :
    shannonEntropy (PMF.uniformOfFinset s hs) = Real.log s.card := by
  simp only [shannonEntropy]
  have h_split : ∑ x : S, negMulLog ((PMF.uniformOfFinset s hs) x).toReal =
      ∑ x ∈ s, negMulLog ((PMF.uniformOfFinset s hs) x).toReal := by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx; rw [PMF.uniformOfFinset_apply_of_notMem hs hx]; simp [negMulLog_zero]
  rw [h_split]
  have h_val : ∀ x ∈ s, negMulLog ((PMF.uniformOfFinset s hs) x).toReal =
      negMulLog (s.card : ℝ)⁻¹ := by
    intro x hx; rw [PMF.uniformOfFinset_apply_of_mem hs hx]; congr 1
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.sum_congr rfl h_val, Finset.sum_const, nsmul_eq_mul]
  simp only [negMulLog]; field_simp; rw [one_div, Real.log_inv, neg_neg]

/-- Lemma 10.1.4 (uniform bound, equality case): $H(X) = \log |\text{supp}(X)|$
if and only if $X$ is uniform on its support. -/
theorem entropy_eq_log_card_iff {S : Type*} [Fintype S] (p : PMF S) :
    shannonEntropy p = Real.log (supportFinset p).card ↔
    p = PMF.uniformOfFinset (supportFinset p) (supportFinset_nonempty p) := by
  constructor
  · intro h_eq
    set supp := supportFinset p
    set n := supp.card
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Finset.Nonempty.card_pos (supportFinset_nonempty p)
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have h1n_ne : (1 : ℝ) / (n : ℝ) ≠ 0 := div_ne_zero one_ne_zero hn_ne
    have hw_nn : ∀ i ∈ supp, (0 : ℝ) ≤ 1 / (n : ℝ) :=
      fun _ _ => div_nonneg zero_le_one hn_pos.le
    have hw_sum : ∑ _ ∈ supp, (1 : ℝ) / (n : ℝ) = 1 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [mul_comm, div_mul_cancel₀ 1 hn_ne]
    have hmem : ∀ i ∈ supp, (p i).toReal ∈ Set.Ici (0 : ℝ) :=
      fun _ _ => Set.mem_Ici.mpr ENNReal.toReal_nonneg
    have h_wavg : ∑ i ∈ supp, (1 / (n : ℝ)) • (p i).toReal = 1 / (n : ℝ) := by
      simp only [smul_eq_mul, ← Finset.mul_sum]
      rw [sum_support_toReal_eq_one, mul_one]
    have jensen_eq_iff := strictConcaveOn_negMulLog.map_sum_eq_iff' hw_nn hw_sum hmem
    have h_negMulLog_val : negMulLog (1 / (n : ℝ)) = (1 / n) * Real.log n := by
      simp [negMulLog]
    have h_sum_rhs : ∑ i ∈ supp, (1 / (n : ℝ)) • negMulLog ((p i).toReal) =
        (1 / n) * Real.log n := by
      simp only [smul_eq_mul, ← Finset.mul_sum]
      rw [← shannonEntropy_eq_sum_support]
      change (1 / (n : ℝ)) * shannonEntropy p = (1 / n) * Real.log n
      rw [h_eq]
    have h_lhs : negMulLog (∑ i ∈ supp, (1 / (n : ℝ)) • (p i).toReal) =
        ∑ i ∈ supp, (1 / (n : ℝ)) • negMulLog ((p i).toReal) := by
      rw [h_wavg, h_negMulLog_val, h_sum_rhs]
    have h_all_eq := jensen_eq_iff.mp h_lhs
    have h_prob_eq : ∀ j ∈ supp, (p j).toReal = 1 / (n : ℝ) := by
      intro j hj
      have := h_all_eq j hj h1n_ne
      rwa [h_wavg] at this
    ext s
    by_cases hs : s ∈ supp
    · rw [PMF.uniformOfFinset_apply_of_mem (supportFinset_nonempty p) hs]
      have h1 := h_prob_eq s hs
      have h2 : ((n : ENNReal)⁻¹).toReal = (n : ℝ)⁻¹ := by
        rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
      rw [show (1 : ℝ) / (n : ℝ) = (n : ℝ)⁻¹ from one_div _] at h1
      rw [← h2] at h1
      exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top p s)
        (ENNReal.inv_ne_top.mpr (by exact_mod_cast (Finset.Nonempty.card_pos
          (supportFinset_nonempty p)).ne'))).mp h1
    · rw [PMF.uniformOfFinset_apply_of_notMem (supportFinset_nonempty p) hs]
      rw [mem_supportFinset_iff] at hs
      exact of_not_not hs
  · intro h_eq
    rw [h_eq]
    rw [supportFinset_uniformOfFinset]
    exact entropy_uniformOfFinset _ _

/-- Theorem 10.1.12 (binomial tail bound, multiplicative form): For $1 \leq k \leq n/2$,
$\sum_{i=0}^{k} \binom{n}{i} \leq (n/k)^k \cdot (n/(n-k))^{n-k}$. -/
theorem binomial_tail_entropy_bound (n k : ℕ) (hk : 0 < k) (hkn : 2 * k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤
      ((n : ℝ) / k) ^ k * ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk_lt_n : (k : ℝ) < (n : ℝ) := by exact_mod_cast (show k < n by omega)
  have h2k_le_n : (2 : ℝ) * k ≤ n := by exact_mod_cast hkn
  have hnk_pos : (0 : ℝ) < (n : ℝ) - (k : ℝ) := by linarith
  have hnk_ne : ((n : ℝ) - (k : ℝ)) ≠ 0 := ne_of_gt hnk_pos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  set x := (k : ℝ) / ((n : ℝ) - k) with hx_def
  have hx_pos : 0 < x := div_pos hk_pos hnk_pos
  have hx_le_one : x ≤ 1 := by
    rw [hx_def, div_le_one hnk_pos]; linarith

  have step1 : (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤ (1 + x) ^ n / x ^ k := by
    rw [le_div_iff₀ (pow_pos hx_pos k)]
    have s1 : (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) * x ^ k ≤
        ∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ) * x ^ i := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_of_le_one hx_pos.le hx_le_one
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      · positivity
    have s2 : ∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ) * x ^ i ≤ (1 + x) ^ n := by
      have expand : (1 + x) ^ n = ∑ m ∈ range (n + 1), (n.choose m : ℝ) * x ^ m := by
        rw [show (1 : ℝ) + x = x + 1 from by ring, add_pow x 1 n]
        simp [mul_comm]
      rw [expand]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (by omega)
      · intro i _ _; positivity
    linarith

  have h1x : 1 + x = (n : ℝ) / ((n : ℝ) - k) := by
    rw [hx_def]; field_simp; linarith
  have step2 : (1 + x) ^ n / x ^ k =
      ((n : ℝ) / k) ^ k * ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) := by
    rw [h1x, hx_def]
    have h1 : ((k : ℝ) / ((n : ℝ) - k)) ^ k ≠ 0 :=
      pow_ne_zero _ (div_ne_zero hk_ne hnk_ne)
    rw [div_eq_iff h1, div_pow, div_pow, div_pow, div_pow,
      div_mul_div_comm, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    have h2 : (↑n - (↑k : ℝ)) ^ (n - k) * (↑n - (↑k : ℝ)) ^ k = (↑n - (↑k : ℝ)) ^ n := by
      rw [← pow_add]; congr 1; omega
    have h3 : (↑n : ℝ) ^ k * (↑n : ℝ) ^ (n - k) = (↑n : ℝ) ^ n := by
      rw [← pow_add]; congr 1; omega
    have lhs_eq : (↑n : ℝ) ^ n * ((↑k : ℝ) ^ k * (↑n - ↑k) ^ (n - k) * (↑n - ↑k) ^ k) =
        (↑n : ℝ) ^ n * (↑k : ℝ) ^ k * (↑n - ↑k) ^ n := by
      rw [show (↑k : ℝ) ^ k * (↑n - ↑k) ^ (n - k) * (↑n - ↑k) ^ k =
        (↑k : ℝ) ^ k * ((↑n - ↑k) ^ (n - k) * (↑n - ↑k) ^ k) from by ring]
      rw [h2]; ring
    have rhs_eq : (↑n : ℝ) ^ k * (↑n : ℝ) ^ (n - k) * (↑k : ℝ) ^ k * (↑n - ↑k) ^ n =
        (↑n : ℝ) ^ n * (↑k : ℝ) ^ k * (↑n - ↑k) ^ n := by
      rw [show (↑n : ℝ) ^ k * (↑n : ℝ) ^ (n - k) * (↑k : ℝ) ^ k =
        ((↑n : ℝ) ^ k * (↑n : ℝ) ^ (n - k)) * (↑k : ℝ) ^ k from by ring]
      rw [h3]
    linarith [lhs_eq, rhs_eq]
  linarith [step1, step2]

end ShannonEntropy
