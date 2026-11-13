/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerEntropy

open Finset BigOperators ShannonEntropy Real

namespace ShearerEntropy

variable {n : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The marginal of $p$ on the empty set has zero Shannon entropy. -/
lemma shannonEntropy_marginal_empty (p : PMF (Fin n → Ω)) :
    shannonEntropy (marginal p ∅) = 0 := by
  classical
  simp only [shannonEntropy]
  haveI : IsEmpty ↥(∅ : Finset (Fin n)) := Finset.instIsEmpty
  haveI : Unique (↥(∅ : Finset (Fin n)) → Ω) := Pi.uniqueOfIsEmpty _
  rw [Fintype.sum_unique]
  have h1 : (marginal p ∅) default = 1 := by
    have htsum := (marginal p ∅).tsum_coe
    rw [tsum_fintype, Fintype.sum_unique] at htsum
    exact_mod_cast htsum
  rw [h1, ENNReal.toReal_one, negMulLog_one]

/-- Canonical equivalence between functions `Fin n → Ω` and functions from the subtype of the
universal finset to `Ω`. -/
noncomputable def funUnivEquiv (n : ℕ) (Ω : Type*) :
    (Fin n → Ω) ≃ (↥(Finset.univ : Finset (Fin n)) → Ω) where
  toFun := fun x i => x i.val
  invFun := fun f i => f ⟨i, Finset.mem_univ i⟩
  left_inv := fun x => by funext i; simp
  right_inv := fun f => by funext ⟨i, _⟩; simp

/-- The marginal of $p$ on the universal finset has the same entropy as $p$ itself. -/
lemma shannonEntropy_marginal_univ (p : PMF (Fin n → Ω)) :
    shannonEntropy (marginal p Finset.univ) = shannonEntropy p := by
  classical
  have heq : marginal p Finset.univ = PMF.map (funUnivEquiv n Ω) p := by
    simp only [marginal, funUnivEquiv, PMF.map]
    rfl
  rw [heq, shannonEntropy_map_equiv]

/-- Rewrite the filter `{j : Fin n | j ≤ i}` as `{j : Fin n | j.val < i.val + 1}`. -/
lemma filter_le_eq_filter_val_lt_succ (i : Fin n) :
    Finset.filter (· ≤ i) (Finset.univ : Finset (Fin n)) =
    Finset.filter (fun j : Fin n => j.val < i.val + 1) Finset.univ := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val]
  omega

/-- Rewrite the filter `{j : Fin n | j < i}` as `{j : Fin n | j.val < i.val}`. -/
lemma filter_lt_eq_filter_val_lt (i : Fin n) :
    Finset.filter (· < i) (Finset.univ : Finset (Fin n)) =
    Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]

/-- The chain rule for Shannon entropy expressed as a telescoping sum of conditional entropies:
$H(p) = \sum_i \bigl(H(p|_{j \le i}) - H(p|_{j < i})\bigr)$. -/
theorem chain_rule_telescoping (p : PMF (Fin n → Ω)) :
    shannonEntropy p = ∑ i : Fin n,
      (shannonEntropy (marginal p (Finset.filter (· ≤ i) Finset.univ)) -
       shannonEntropy (marginal p (Finset.filter (· < i) Finset.univ))) := by
  classical

  let f : ℕ → ℝ := fun k =>
    shannonEntropy (marginal p (Finset.filter (fun j : Fin n => j.val < k) Finset.univ))

  have hterms : ∀ (i : Fin n),
      shannonEntropy (marginal p (Finset.filter (· ≤ i) Finset.univ)) -
      shannonEntropy (marginal p (Finset.filter (· < i) Finset.univ)) =
      f (i.val + 1) - f i.val := by
    intro i
    simp only [f]
    rw [filter_le_eq_filter_val_lt_succ i, filter_lt_eq_filter_val_lt i]

  simp_rw [hterms]

  rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1) - f i) n, Finset.sum_range_sub]

  have hf0 : f 0 = 0 := by
    show shannonEntropy (marginal p (Finset.filter (fun j : Fin n => j.val < 0) Finset.univ)) = 0
    have hempty : Finset.filter (fun j : Fin n => j.val < 0) Finset.univ = ∅ := by
      ext j; simp
    rw [hempty]
    exact shannonEntropy_marginal_empty p
  have hfn : f n = shannonEntropy p := by
    show shannonEntropy (marginal p (Finset.filter (fun j : Fin n => j.val < n) Finset.univ)) =
      shannonEntropy p
    have huniv : Finset.filter (fun j : Fin n => j.val < n) Finset.univ = Finset.univ := by
      ext j; simp
    rw [huniv]
    exact shannonEntropy_marginal_univ p
  linarith



end ShearerEntropy
