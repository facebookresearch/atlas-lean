/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Entropy
import Mathlib.Data.Finset.Card

open Finset BigOperators ShannonEntropy Real

namespace ShearerEntropy

/-- The marginal distribution of a joint PMF $p$ on `Fin n → Ω` restricted to coordinates in
$A \subseteq \{1,\dots,n\}$. -/
noncomputable def marginal {n : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : PMF (Fin n → Ω)) (A : Finset (Fin n)) : PMF (↥A → Ω) :=
  p.map (fun x (i : ↥A) => x i.val)

/-- The covering condition for Shearer's lemma: a family $\{A_j\}_{j=1}^s$ is a $k$-cover of
$\{1,\dots,n\}$ if every index appears in at least $k$ of the sets $A_j$. -/
def CoveringCondition {n s : ℕ} (A : Fin s → Finset (Fin n)) (k : ℕ) : Prop :=
  ∀ i : Fin n, k ≤ (Finset.univ.filter (fun j => i ∈ A j)).card

/-- Marginal composition: when $B \subseteq A$, marginalizing $p$ onto $B$ equals marginalizing
$p$ onto $A$ first and then restricting further to $B$. -/
lemma marginal_comp {n : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : PMF (Fin n → Ω)) (A B : Finset (Fin n)) (hBA : B ⊆ A) :
    marginal p B = (marginal p A).map (fun f (i : ↥B) => f ⟨i.val, hBA i.property⟩) := by
  unfold marginal
  rw [PMF.map_comp]
  rfl

/-- The Shannon entropy is non-increasing under deterministic maps: $H(f(X)) \le H(X)$. -/
theorem shannonEntropy_map_le {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    (q : PMF S) (f : S → T) :
    shannonEntropy (q.map f) ≤ shannonEntropy q := by
  classical
  simp only [shannonEntropy]

  have regroup : ∑ s : S, negMulLog (q s).toReal =
      ∑ t : T, ∑ s ∈ Finset.univ.filter (fun s => f s = t), negMulLog (q s).toReal := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext s
      simp [Finset.mem_biUnion, Finset.mem_filter]
    · intro t₁ _ t₂ _ hne
      exact Finset.disjoint_filter.mpr (fun s _ h₁ h₂ => hne (h₁.symm.trans h₂))
  rw [regroup]
  apply Finset.sum_le_sum
  intro t _


  have hfiber : ((q.map f) t).toReal =
      ∑ s ∈ Finset.univ.filter (fun s => f s = t), (q s).toReal := by
    have h1 : (q.map f) t = ∑ s ∈ Finset.univ.filter (fun s => f s = t), q s := by
      rw [PMF.map_apply, tsum_fintype]
      simp_rw [eq_comm (a := t)]
      rw [← Finset.sum_filter]
    rw [h1, ENNReal.toReal_sum (fun s _ => PMF.apply_ne_top q s)]
  rw [hfiber]


  set F := Finset.univ.filter (fun s => f s = t)
  by_cases hS : ∑ s ∈ F, (q s).toReal = 0
  ·
    have hall : ∀ s ∈ F, (q s).toReal = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ENNReal.toReal_nonneg)).mp hS
    rw [hS, negMulLog_zero]
    apply Finset.sum_nonneg
    intro s hs
    rw [hall s hs, negMulLog_zero]
  ·
    set S := ∑ s ∈ F, (q s).toReal
    have hS_pos : (0 : ℝ) < S := by
      apply lt_of_le_of_ne
      · exact Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg)
      · exact Ne.symm hS


    suffices h : ∀ s ∈ F, (q s).toReal / S * negMulLog S ≤ negMulLog (q s).toReal by
      calc negMulLog S
          = 1 * negMulLog S := (one_mul _).symm
        _ = (∑ s ∈ F, (q s).toReal / S) * negMulLog S := by
            congr 1; rw [← Finset.sum_div, div_self (ne_of_gt hS_pos)]
        _ = ∑ s ∈ F, (q s).toReal / S * negMulLog S :=
            Finset.sum_mul F (fun s => (q s).toReal / S) (negMulLog S)
        _ ≤ ∑ s ∈ F, negMulLog (q s).toReal := Finset.sum_le_sum h
    intro s hs
    have ha_nn : (0 : ℝ) ≤ (q s).toReal := ENNReal.toReal_nonneg
    have hS_nn : (0 : ℝ) ≤ S := le_of_lt hS_pos
    have hw : (0 : ℝ) ≤ (q s).toReal / S := div_nonneg ha_nn hS_nn
    have hw2 : (0 : ℝ) ≤ 1 - (q s).toReal / S := by
      rw [sub_nonneg]
      exact (div_le_one hS_pos).mpr
        (Finset.single_le_sum (fun i _ => ENNReal.toReal_nonneg) hs)
    have hw_sum : (q s).toReal / S + (1 - (q s).toReal / S) = 1 := by ring
    have hmem_S : S ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hS_nn
    have hmem_0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl

    have hconc := concaveOn_negMulLog.2 hmem_S hmem_0 hw hw2 hw_sum
    simp only [smul_eq_mul, negMulLog_zero, mul_zero, add_zero] at hconc


    have hdiv : (q s).toReal / S * S = (q s).toReal :=
      div_mul_cancel₀ _ (ne_of_gt hS_pos)
    rw [hdiv] at hconc
    exact hconc

/-- Monotonicity of marginal entropy: $H(p|_B) \le H(p|_A)$ whenever $B \subseteq A$. -/
theorem marginal_entropy_mono {n : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : PMF (Fin n → Ω)) (A B : Finset (Fin n)) (hBA : B ⊆ A) :
    shannonEntropy (marginal p B) ≤ shannonEntropy (marginal p A) := by
  rw [marginal_comp p A B hBA]
  exact shannonEntropy_map_le (marginal p A) _

end ShearerEntropy
