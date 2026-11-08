/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SidorenkoCompleteBipartite

open SimpleGraph Finset BigOperators

/-- Homomorphism count $\mathrm{hom}(K_{s,t}, G)$ from the complete bipartite graph
$K_{s,t}$ into $G$: choose an $s$-tuple $\mathbf{x}$ in $V(G)$, then count its common
neighborhood and raise to the power $t$. -/
noncomputable def homCountBip {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (s t : ℕ) : ℕ :=
  ∑ xs : Fin s → W,
    ((Finset.univ.filter fun y => ∀ i : Fin s, G.Adj (xs i) y).card) ^ t

/-- Jensen-style inequality for $\mathbb{N}$-valued sums:
$(\sum_i f(i))^{n+1} \le |s|^n \sum_i f(i)^{n+1}$. -/
lemma nat_jensen_pow {ι : Type*} (s : Finset ι) (f : ι → ℕ) (n : ℕ) :
    (∑ i ∈ s, f i) ^ (n + 1) ≤ s.card ^ n * ∑ i ∈ s, f i ^ (n + 1) :=
  pow_sum_le_card_mul_sum_pow (fun _ _ => Nat.zero_le _) n

/-- Core inequality for Sidorenko on complete bipartite graphs: twice the edge count to
the power $st$ is at most $n^{2st - s - t}$ times the homomorphism count $\mathrm{hom}(K_{s,t}, G)$,
where $n = |V(G)|$. -/
lemma key_inequality {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (_hW : 0 < Fintype.card W) :
    (2 * G.edgeFinset.card) ^ (s * t) ≤
      (Fintype.card W) ^ (2 * s * t - s - t) * homCountBip G s t := by
  set n := Fintype.card W

  have hJensen : homCountBip G s 1 ^ t ≤ n ^ (s * (t - 1)) * homCountBip G s t := by
    unfold homCountBip
    simp only [pow_one]
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, (Nat.succ_pred_eq_of_pos ht).symm⟩
    simp only [Nat.add_sub_cancel]
    have h := nat_jensen_pow Finset.univ
      (fun (xs : Fin s → W) =>
        (Finset.univ.filter fun y => ∀ i : Fin s, G.Adj (xs i) y).card) t'
    simp only [Finset.card_univ] at h
    convert h using 2
    rw [Fintype.card_fun, Fintype.card_fin]
    ring

  have hStar : (2 * G.edgeFinset.card) ^ s ≤ n ^ (s - 1) * homCountBip G s 1 := by


    have hfubini : homCountBip G s 1 = ∑ y : W, G.degree y ^ s := by
      simp only [homCountBip, pow_one]

      have key : ∀ (xs : Fin s → W),
          (Finset.univ.filter fun y => ∀ i : Fin s, G.Adj (xs i) y).card =
          ∑ y : W, if ∀ i : Fin s, G.Adj (xs i) y then 1 else 0 := by
        intro xs
        rw [Finset.card_filter]
      simp_rw [key]
      rw [Finset.sum_comm]
      congr 1; ext y

      rw [← Finset.card_filter]

      have heq : (Finset.univ.filter fun xs : Fin s → W => ∀ i, G.Adj (xs i) y) =
          Fintype.piFinset (fun _ : Fin s => G.neighborFinset y) := by
        ext xs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Fintype.mem_piFinset, SimpleGraph.mem_neighborFinset]
        exact forall_congr' (fun i => G.adj_comm (xs i) y)
      rw [heq, Fintype.card_piFinset]
      simp only [SimpleGraph.degree, Finset.prod_const, Finset.card_fin]

    rw [hfubini]
    have hhand : ∑ y : W, G.degree y = 2 * G.edgeFinset.card :=
      G.sum_degrees_eq_twice_card_edges
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
    simp only [Nat.add_sub_cancel]
    rw [← hhand]
    exact nat_jensen_pow Finset.univ (fun y => G.degree y) s'

  have h2st_le : s + t ≤ 2 * s * t := by nlinarith [hs, ht]
  have hexp : (s - 1) * t + s * (t - 1) = 2 * s * t - s - t := by
    suffices h : (s - 1) * t + s * (t - 1) + (s + t) = 2 * s * t by
      have hle : s + t ≤ 2 * s * t := h2st_le
      have hsc := Nat.sub_add_cancel hle


      omega
    nlinarith [@Nat.sub_add_cancel s 1 hs, @Nat.sub_add_cancel t 1 ht]
  calc (2 * G.edgeFinset.card) ^ (s * t)
      = ((2 * G.edgeFinset.card) ^ s) ^ t := by ring
    _ ≤ (n ^ (s - 1) * homCountBip G s 1) ^ t := Nat.pow_le_pow_left hStar t
    _ = n ^ ((s - 1) * t) * homCountBip G s 1 ^ t := by rw [Nat.mul_pow, pow_mul]
    _ ≤ n ^ ((s - 1) * t) * (n ^ (s * (t - 1)) * homCountBip G s t) :=
        Nat.mul_le_mul_left _ hJensen
    _ = n ^ ((s - 1) * t + s * (t - 1)) * homCountBip G s t := by ring
    _ = n ^ (2 * s * t - s - t) * homCountBip G s t := by
        rw [hexp]

/-- Theorem 10.3.6 (Sidorenko for complete bipartite graphs). For any graph $G$ on $n$
vertices and $m$ edges, the homomorphism density of $K_{s,t}$ in $G$ is bounded below by
the $(st)$-th power of the edge density:
$$ \frac{\mathrm{hom}(K_{s,t}, G)}{n^{s+t}} \ge \left( \frac{2m}{n^2} \right)^{st}. $$ -/
theorem sidorenko_completeBipartite (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hW : 0 < Fintype.card W) :
    (homCountBip G s t : ℝ) / (Fintype.card W : ℝ) ^ (s + t) ≥
      ((2 * (G.edgeFinset.card : ℝ)) / (Fintype.card W : ℝ) ^ 2) ^ (s * t) := by
  set n := Fintype.card W
  set m := G.edgeFinset.card
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hW
  by_cases hm : m = 0
  · simp only [hm, Nat.cast_zero, mul_zero, zero_div,
      zero_pow (Nat.mul_pos hs ht).ne']
    positivity
  · have key := key_inequality G s t hs ht hW
    have key_real : (2 * (m : ℝ)) ^ (s * t) ≤
        (n : ℝ) ^ (2 * s * t - s - t) * (homCountBip G s t : ℝ) := by
      exact_mod_cast key
    have h2st : s + t ≤ 2 * s * t := by nlinarith [hs, ht]
    rw [ge_iff_le, div_pow, ← pow_mul]
    rw [div_le_div_iff₀ (pow_pos hn_pos _) (pow_pos hn_pos _)]
    calc (2 * (m : ℝ)) ^ (s * t) * (n : ℝ) ^ (s + t)
        ≤ ((n : ℝ) ^ (2 * s * t - s - t) * (homCountBip G s t : ℝ)) *
          (n : ℝ) ^ (s + t) :=
          mul_le_mul_of_nonneg_right key_real (pow_nonneg (Nat.cast_nonneg _) _)
      _ = (homCountBip G s t : ℝ) *
          ((n : ℝ) ^ (2 * s * t - s - t) * (n : ℝ) ^ (s + t)) := by ring
      _ = (homCountBip G s t : ℝ) * (n : ℝ) ^ (2 * s * t - s - t + (s + t)) := by
          rw [← pow_add]
      _ = (homCountBip G s t : ℝ) * (n : ℝ) ^ (2 * (s * t)) := by
          congr 2
          have : 2 * s * t = s * t + s * t := by ring
          omega

end SidorenkoCompleteBipartite
