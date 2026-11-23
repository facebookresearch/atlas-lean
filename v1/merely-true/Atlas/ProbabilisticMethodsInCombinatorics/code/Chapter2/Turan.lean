/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Real.Basic

open Finset Fintype SimpleGraph

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {r : ℕ}

/-- Integer form of **Turán's theorem (Theorem 2.3.6, Turán 1941)**: any
$K_{r+1}$-free graph $G$ on $|V|$ vertices satisfies
$2 r \cdot |E(G)| \leq (r - 1) \cdot |V|^2$. -/
theorem CliqueFree.two_mul_r_mul_card_edgeFinset_le (cf : G.CliqueFree (r + 1)) :
    2 * r * #G.edgeFinset ≤ (r - 1) * (Fintype.card V) ^ 2 := by
  calc 2 * r * #G.edgeFinset
      ≤ 2 * r * ((Fintype.card V ^ 2 - (Fintype.card V % r) ^ 2) * (r - 1) / (2 * r) +
          (Fintype.card V % r).choose 2) := by
        gcongr
        exact cf.card_edgeFinset_le
    _ ≤ 2 * r * #(turanGraph (Fintype.card V) r).edgeFinset := by
        gcongr
        rw [card_edgeFinset_turanGraph]
    _ ≤ (r - 1) * (Fintype.card V) ^ 2 :=
        mul_card_edgeFinset_turanGraph_le

/-- Real form of **Turán's theorem (Theorem 2.3.6)**: any $K_{r+1}$-free graph on $|V|$
vertices has at most $\left(1 - \tfrac{1}{r}\right) \tfrac{|V|^2}{2}$ edges. -/
theorem CliqueFree.card_edgeFinset_le_real (cf : G.CliqueFree (r + 1)) (hr : 0 < r) :
    (#G.edgeFinset : ℝ) ≤ (1 - 1 / (r : ℝ)) * (Fintype.card V : ℝ) ^ 2 / 2 := by
  have hr' : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have h := cf.two_mul_r_mul_card_edgeFinset_le
  have h1 : 1 ≤ r := hr

  have hR : 2 * (r : ℝ) * (↑(#G.edgeFinset)) ≤ ((r : ℝ) - 1) * (↑(Fintype.card V)) ^ 2 := by
    exact_mod_cast h


  have h2r : (0 : ℝ) < 2 * ↑r := mul_pos two_pos hr'
  have hne : (2 * (r : ℝ)) ≠ 0 := ne_of_gt h2r
  calc (↑(#G.edgeFinset) : ℝ)
      = 2 * ↑r * ↑(#G.edgeFinset) / (2 * ↑r) := by
        rw [mul_div_cancel_left₀ _ hne]
    _ ≤ ((↑r - 1) * (↑(Fintype.card V)) ^ 2) / (2 * ↑r) := by
        exact div_le_div_of_nonneg_right hR (le_of_lt h2r)
    _ = (1 - 1 / (↑r : ℝ)) * (↑(Fintype.card V) : ℝ) ^ 2 / 2 := by
        have hne' : (↑r : ℝ) ≠ 0 := ne_of_gt hr'
        have key : (↑r - 1 : ℝ) / (↑r : ℝ) = 1 - 1 / (↑r : ℝ) := by
          rw [sub_div, div_self hne']
        rw [← key, div_mul_eq_mul_div]
        rw [show (2 : ℝ) * (↑r : ℝ) = (↑r : ℝ) * 2 from mul_comm _ _, ← div_div]

end SimpleGraph
