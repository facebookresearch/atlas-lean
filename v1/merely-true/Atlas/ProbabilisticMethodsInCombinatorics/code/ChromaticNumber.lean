/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter8.JansonInequality

namespace ChromaticNumber

open Finset Real Filter Nat Classical

/-- Expected number of $k$-cliques in $G(n,1/2)$:
$\mu = \binom{n}{k} \cdot 2^{-\binom{k}{2}}$. -/
noncomputable def muClique (n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * (2 : ℝ) ^ (-(Nat.choose k 2 : ℤ))

/-- The largest $k \le n$ for which the expected number $\mu(n,k)$ of $k$-cliques in
$G(n,1/2)$ is still at least $1$. -/
noncomputable def k₀ (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => (1 : ℝ) ≤ muClique n k) n

/-- Clique number of a finite graph on `Fin n`: the largest $k \le n$ such that $G$
contains a clique of size $k$. -/
noncomputable def cliqueNum {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.findGreatest (fun k => ¬G.CliqueFree k) n

/-- Probability of an event $A$ on graphs sampled from $G(n,1/2)$, computed combinatorially
as the fraction of graphs on $\{1,\dots,n\}$ satisfying $A$. -/
noncomputable def probGnHalf (n : ℕ) (A : SimpleGraph (Fin n) → Prop) : ℝ :=
  ((Finset.univ.filter (fun G => A G)).card : ℝ) /
  (Fintype.card (SimpleGraph (Fin n)) : ℝ)

/-- The $\Delta$ quantity from Janson's inequality applied to the $k$-clique event in
$G(n,1/2)$: a sum over the shared-vertex parameter $s \in [2, k-1]$ that bounds the
correlation between pairs of overlapping $k$-cliques. -/
noncomputable def deltaClique (n k : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 2 (k - 1),
    (Nat.choose k s : ℝ) * (Nat.choose (n - k) (k - s) : ℝ) *
    (Nat.choose n k : ℝ) * (2 : ℝ) ^ (-(2 * Nat.choose k 2 - Nat.choose s 2 : ℤ))

/-- The threshold clique-size $k_0(n)$ is at most $n$, since it is the greatest such value
in $\{0, \dots, n\}$. -/
lemma k₀_le (n : ℕ) : k₀ n ≤ n := Nat.findGreatest_le n

/-- Dual characterization of `cliqueNum`: for $0 < m \le n$, the clique number of $G$ is
strictly less than $m$ iff $G$ contains no $m$-clique. -/
lemma cliqueNum_lt_iff_cliqueFree {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ)
    (hm : m ≤ n) (hm0 : 0 < m) :
    cliqueNum G < m ↔ G.CliqueFree m := by
  simp only [cliqueNum]
  constructor
  · intro h
    by_contra habs
    exact Nat.not_lt.mpr (Nat.le_findGreatest hm habs) h
  · intro hcf
    by_contra hlt
    push_neg at hlt
    have hne : (Nat.findGreatest (fun k => ¬G.CliqueFree k) n) ≠ 0 := by omega
    exact (Nat.findGreatest_of_ne_zero rfl hne) (SimpleGraph.CliqueFree.mono hlt hcf)





/-- Elementary bound $L! \le 2^{\binom{L}{2}}$, used in estimating the asymptotics of the
clique-counting quantities. -/
lemma factorial_le_two_pow_choose (L : ℕ) : L ! ≤ 2 ^ Nat.choose L 2 := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ]
    have hchoose : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
      simp [Nat.choose_succ_succ, Nat.choose_one_right]; omega
    rw [hchoose, Nat.pow_add]
    calc (n + 1) * n ! ≤ 2 ^ n * n ! := Nat.mul_le_mul_right _ n.lt_two_pow_self
      _ ≤ 2 ^ n * 2 ^ Nat.choose n 2 := Nat.mul_le_mul_left _ ih
      _ = 2 ^ Nat.choose n 2 * 2 ^ n := by ring













end ChromaticNumber
