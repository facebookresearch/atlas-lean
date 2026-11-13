/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
set_option maxHeartbeats 400000

namespace DistinctSums

open Finset

/-- A set $S \subseteq \mathbb{N}$ has distinct subset sums if any two subsets
    with equal sums must be equal. -/
def HasDistinctSubsetSums (S : Finset ℕ) : Prop :=
  ∀ A B : Finset ℕ, A ⊆ S → B ⊆ S → A.sum id = B.sum id → A = B


end DistinctSums

namespace HarperIsoperimetric

/-- The $k$-dimensional Boolean hypercube $\{0,1\}^k$, represented as functions
    $\mathrm{Fin}\, k \to \mathrm{Bool}$. -/
abbrev Hypercube (k : ℕ) := Fin k → Bool

/-- Two vertices of the hypercube are adjacent if their Hamming distance is $1$,
    i.e. they differ in exactly one coordinate. -/
def Hypercube.Adjacent {k : ℕ} (x y : Hypercube k) : Prop :=
  hammingDist x y = 1

/-- Decidability instance for adjacency in the hypercube. -/
instance {k : ℕ} (x y : Hypercube k) : Decidable (Hypercube.Adjacent x y) :=
  inferInstanceAs (Decidable (hammingDist x y = 1))

/-- The vertex boundary of a set $A$ in the hypercube: vertices outside $A$ adjacent
    to some vertex in $A$. -/
def Hypercube.vertexBoundary {k : ℕ} (A : Finset (Hypercube k)) : Finset (Hypercube k) :=
  Finset.univ.filter fun v => v ∉ A ∧ ∃ u ∈ A, Hypercube.Adjacent u v


end HarperIsoperimetric

namespace DubroffFoxXu

open Finset BigOperators

/-- Weighted sum $\sum_{i : \varepsilon_i = \mathtt{true}} x_i$ selecting coordinates of $x$
    indicated by the Boolean string $\varepsilon$. -/
def weightedSum {k : ℕ} (x : Fin k → ℕ) (ε : Fin k → Bool) : ℕ :=
  ∑ i : Fin k, if ε i then x i else 0

/-- Coordinatewise Boolean complement of $\varepsilon \in \{0,1\}^k$. -/
def boolCompl {k : ℕ} (ε : Fin k → Bool) : Fin k → Bool := fun i => !ε i

/-- The subset of $\mathrm{Fin}\, k$ on which the Boolean function $\varepsilon$ is true. -/
def boolToFinset {k : ℕ} (ε : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun i => ε i = true)

/-- Variant of `HasDistinctSubsetSums` for tuples $x : \mathrm{Fin}\, k \to \mathbb{N}$:
    the map sending a subset $T$ to $\sum_{i \in T} x_i$ is injective. -/
def HasDistinctSubsetSumsFin {k : ℕ} (x : Fin k → ℕ) : Prop :=
  Function.Injective (fun T : Finset (Fin k) => ∑ i ∈ T, x i)

/-- Vertex boundary of $A$ in the hypercube $\{0,1\}^k$, formulated via differing in
    exactly one coordinate from some vertex in $A$. -/
def cubeBoundary {k : ℕ} (A : Finset (Fin k → Bool)) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun v => v ∉ A ∧
    ∃ u ∈ A, ∃ i : Fin k, (∀ j : Fin k, j ≠ i → v j = u j) ∧ v i ≠ u i)

/-- The map `boolToFinset` from Boolean strings to subsets of $\mathrm{Fin}\, k$ is injective. -/
lemma boolToFinset_injective {k : ℕ} : Function.Injective (@boolToFinset k) := by
  intro ε₁ ε₂ h
  funext i
  have hmem : (i ∈ boolToFinset ε₁) ↔ (i ∈ boolToFinset ε₂) := by rw [h]
  simp only [boolToFinset, mem_filter, mem_univ, true_and] at hmem
  cases h₁ : ε₁ i <;> cases h₂ : ε₂ i <;> simp_all

/-- Rewrites the weighted sum as a sum over the subset selected by $\varepsilon$. -/
lemma weightedSum_eq_sum {k : ℕ} (x : Fin k → ℕ) (ε : Fin k → Bool) :
    weightedSum x ε = ∑ i ∈ boolToFinset ε, x i := by
  unfold weightedSum boolToFinset
  rw [Finset.sum_filter]

/-- If $x$ has distinct subset sums, then the map $\varepsilon \mapsto \sum \varepsilon_i x_i$
    is injective on Boolean strings. -/
lemma weightedSum_injective {k : ℕ} {x : Fin k → ℕ}
    (hdist : HasDistinctSubsetSumsFin x) :
    Function.Injective (weightedSum x) := by
  intro ε₁ ε₂ h
  have h1 : ∑ i ∈ boolToFinset ε₁, x i = ∑ i ∈ boolToFinset ε₂, x i := by
    rw [← weightedSum_eq_sum, ← weightedSum_eq_sum, h]
  exact boolToFinset_injective (hdist h1)

/-- A Boolean string and its complement select disjoint pieces whose weighted sums add
    up to the total $\sum_i x_i$. -/
lemma weightedSum_add_compl {k : ℕ} (x : Fin k → ℕ) (ε : Fin k → Bool) :
    weightedSum x ε + weightedSum x (boolCompl ε) = ∑ i : Fin k, x i := by
  unfold weightedSum boolCompl
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases ε i <;> simp

/-- If two Boolean strings $\varepsilon, u$ agree off coordinate $i$ with
    $\varepsilon_i = \mathtt{true}$ and $u_i = \mathtt{false}$, then their weighted sums
    differ by $x_i$. -/
lemma weightedSum_neighbor {k : ℕ} (x : Fin k → ℕ) (ε u : Fin k → Bool) (i : Fin k)
    (hagree : ∀ j : Fin k, j ≠ i → ε j = u j)
    (hε_true : ε i = true) (hu_false : u i = false) :
    weightedSum x ε = weightedSum x u + x i := by
  unfold weightedSum
  have heq_rest : ∀ j ∈ Finset.univ.erase i, (if ε j = true then x j else 0) =
      (if u j = true then x j else 0) := fun j hj => by
    rw [Finset.mem_erase] at hj; rw [hagree j hj.1]
  have lhs : (∑ j : Fin k, if ε j = true then x j else 0) =
      x i + ∑ j ∈ Finset.univ.erase i, (if ε j = true then x j else 0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp [hε_true]
  have rhs : (∑ j : Fin k, if u j = true then x j else 0) =
      0 + ∑ j ∈ Finset.univ.erase i, (if u j = true then x j else 0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp [hu_false]
  rw [lhs, rhs]
  have := Finset.sum_congr rfl heq_rest
  omega




end DubroffFoxXu

namespace DistinctSumsBound

open Finset BigOperators Classical

/-- Sign encoding of a Boolean: $\mathtt{true} \mapsto +1$, $\mathtt{false} \mapsto -1$. -/
def boolSign (b : Bool) : ℤ := if b then 1 else -1

/-- Orthogonality of sign characters over $\{0,1\}^k$: the sum of
    $\mathrm{sgn}(\varepsilon_l)\,\mathrm{sgn}(\varepsilon_m)$ over all $\varepsilon$
    equals $2^k$ if $l = m$ and vanishes otherwise. -/
lemma sum_boolSign_prod (k : ℕ) (l m : Fin k) :
    ∑ ε : Fin k → Bool, boolSign (ε l) * boolSign (ε m) =
    if l = m then (2 ^ k : ℤ) else 0 := by
  split_ifs with h
  · subst h
    have hh : ∀ ε : Fin k → Bool, boolSign (ε l) * boolSign (ε l) = 1 := by
      intro ε; simp [boolSign]; cases ε l <;> simp
    simp only [hh, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp
  · apply Finset.sum_involution (fun (ε : Fin k → Bool) _ => Function.update ε l (!ε l))
    · intro ε _
      have hne : Function.update ε l (!ε l) m = ε m :=
        Function.update_of_ne (Ne.symm h) _ _
      simp only [boolSign, Function.update_self, hne]
      cases ε l <;> cases ε m <;> simp
    · intro ε _ _ heq
      have := congr_fun heq l; simp [Function.update] at this
    · intro _ _; exact Finset.mem_univ _
    · intro ε _; funext j; simp only [Function.update]
      split_ifs with h1
      · subst h1; simp
      · rfl

/-- Variance identity from second-moment method:
    $\sum_{\varepsilon \in \{\pm 1\}^k} \bigl(\sum_l \varepsilon_l x_l\bigr)^2 =
    2^k \sum_l x_l^2$. -/
lemma variance_identity (k : ℕ) (x : Fin k → ℤ) :
    ∑ ε : Fin k → Bool, (∑ l : Fin k, boolSign (ε l) * x l) ^ 2 =
    2 ^ k * ∑ l : Fin k, x l ^ 2 := by
  simp_rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext l; arg 2; ext m; arg 2; ext ε
    rw [show boolSign (ε l) * x l * (boolSign (ε m) * x m) =
      x l * x m * (boolSign (ε l) * boolSign (ε m)) from by ring]
  simp_rw [← Finset.mul_sum, sum_boolSign_prod]
  conv_lhs =>
    arg 2; ext l; arg 2; ext m
    rw [show x l * x m * (if l = m then (2 : ℤ) ^ k else 0) =
      if l = m then x l * x m * 2 ^ k else 0 from by split_ifs <;> ring]
  simp_rw [Finset.sum_ite_eq, mem_univ, if_true]
  rw [Finset.mul_sum]; congr 1; ext l; ring

/-- Conversion to signed sums:
    $2 \sum_{i : \varepsilon_i} x_i - \sum_i x_i = \sum_i \mathrm{sgn}(\varepsilon_i)\,x_i$. -/
lemma two_ws_minus_S_eq (k : ℕ) (x : Fin k → ℕ) (ε : Fin k → Bool) :
    (2 * (DubroffFoxXu.weightedSum x ε : ℤ) - (∑ i : Fin k, (x i : ℤ))) =
    ∑ i : Fin k, boolSign (ε i) * (x i : ℤ) := by
  simp only [DubroffFoxXu.weightedSum, boolSign]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1; ext i; cases ε i <;> simp; ring

/-- Dubroff–Fox–Xu second-moment bound (Theorem 4.6.6): for any $k$ positive integers
    $x_1,\dots,x_k \le n$ with distinct subset sums,
    $3 \cdot 2^k \le 8 n (\lfloor \sqrt{k} \rfloor + 1)$, yielding
    $n = \Omega(2^k / \sqrt{k})$. -/
theorem distinct_sums_bound {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (x : Fin k → ℕ)
    (hx_pos : ∀ i, 0 < x i) (hx_le : ∀ i, x i ≤ n)
    (hdist : DubroffFoxXu.HasDistinctSubsetSumsFin x) :
    3 * 2 ^ k ≤ 8 * n * (Nat.sqrt k + 1) := by
  set ws := DubroffFoxXu.weightedSum x
  set S := ∑ i : Fin k, x i
  set T := 2 * n * (Nat.sqrt k + 1) with hT_def

  set inside : Finset (Fin k → Bool) :=
    Finset.univ.filter (fun ε => ((2 * (ws ε : ℤ)) - (S : ℤ)).natAbs < T)
  set outside : Finset (Fin k → Bool) :=
    Finset.univ.filter (fun ε => T ≤ ((2 * (ws ε : ℤ)) - (S : ℤ)).natAbs)

  have hpart : inside.card + outside.card = 2 ^ k := by
    have h_union : inside ∪ outside = Finset.univ := by
      ext ε; simp only [inside, outside, mem_union, mem_filter, mem_univ, true_and, iff_true]
      exact Nat.lt_or_ge _ _
    have h_disj : Disjoint inside outside := by
      simp only [inside, outside]; rw [Finset.disjoint_filter]; intro _ _ h1 h2; omega
    rw [← Finset.card_union_of_disjoint h_disj, h_union,
        Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

  have hvar : ∑ ε : Fin k → Bool, ((2 * (ws ε : ℤ)) - (S : ℤ)) ^ 2 =
      (2 ^ k : ℤ) * ∑ i : Fin k, (x i : ℤ) ^ 2 := by
    have heq : ∀ ε, (2 * (ws ε : ℤ) - (S : ℤ)) =
        (2 * (DubroffFoxXu.weightedSum x ε : ℤ) - ∑ i, (x i : ℤ)) := by
      intro ε; simp [ws, S]
    simp_rw [heq, two_ws_minus_S_eq]
    exact variance_identity k (fun i => (x i : ℤ))

  have houtside_bound : outside.card * 4 ≤ 2 ^ k := by

    have hvar_ub : (outside.card : ℤ) * (4 * (n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2) ≤
        (2 ^ k : ℤ) * ((k : ℤ) * (n : ℤ) ^ 2) := by

      have h_lower : ∀ ε ∈ outside, (T : ℤ) ^ 2 ≤ ((2 * (ws ε : ℤ) - S) ^ 2) := by
        intro ε hε
        have hmem : T ≤ ((2 * (ws ε : ℤ)) - (S : ℤ)).natAbs := by
          simp only [outside, mem_filter, mem_univ, true_and] at hε; exact hε
        nlinarith [sq_abs (2 * (ws ε : ℤ) - S),
                   show (T : ℤ) ≤ |2 * (ws ε : ℤ) - S| from by
                     rw [Int.abs_eq_natAbs]; exact_mod_cast hmem]

      have h_markov : (outside.card : ℤ) * (T : ℤ) ^ 2 ≤
          ∑ ε : Fin k → Bool, ((2 * (ws ε : ℤ)) - S) ^ 2 := by
        calc (outside.card : ℤ) * (T : ℤ) ^ 2
            = ∑ _ ∈ outside, (T : ℤ) ^ 2 := by rw [Finset.sum_const]; push_cast; ring
          _ ≤ ∑ ε ∈ outside, ((2 * (ws ε : ℤ)) - S) ^ 2 := Finset.sum_le_sum h_lower
          _ ≤ ∑ ε : Fin k → Bool, ((2 * (ws ε : ℤ)) - S) ^ 2 :=
              Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)

      have hsum_sq : (∑ i : Fin k, (x i : ℤ) ^ 2) ≤ (k : ℤ) * (n : ℤ) ^ 2 := by
        calc ∑ i : Fin k, (x i : ℤ) ^ 2
            ≤ ∑ _ : Fin k, (n : ℤ) ^ 2 := by
              apply Finset.sum_le_sum; intro i _
              exact sq_le_sq' (by linarith [show (0 : ℤ) ≤ x i from by positivity])
                (by exact_mod_cast hx_le i)
          _ = k * (n : ℤ) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring

      have hT_sq : (T : ℤ) ^ 2 = 4 * (n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2 := by
        simp only [hT_def]; push_cast; ring
      nlinarith [h_markov, hvar, hsum_sq]

    suffices h : (outside.card : ℤ) * 4 ≤ (2 ^ k : ℤ) from by exact_mod_cast h
    by_contra h_neg; push_neg at h_neg
    have hk_lt : (k : ℤ) < ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2 := by
      push_cast; exact_mod_cast Nat.lt_succ_sqrt' k
    have step1 : (2 ^ k : ℤ) * ((n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2) <
        (outside.card : ℤ) * 4 * ((n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2) := by
      nlinarith [show (0 : ℤ) < (n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2 from by positivity]
    have step2 : (outside.card : ℤ) * 4 * ((n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2) ≤
        (2 ^ k : ℤ) * ((k : ℤ) * (n : ℤ) ^ 2) := by nlinarith [hvar_ub]
    have step3 : (2 ^ k : ℤ) * ((k : ℤ) * (n : ℤ) ^ 2) <
        (2 ^ k : ℤ) * ((n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2) := by
      nlinarith [show (0 : ℤ) < (2 ^ k : ℤ) * (n : ℤ) ^ 2 from by positivity, hk_lt]
    linarith

  have hinside_le : inside.card ≤ T := by
    have hinj := DubroffFoxXu.weightedSum_injective hdist
    suffices h : (inside.image ws).card ≤ T by
      rwa [Finset.card_image_of_injOn (hinj.injOn.mono (fun _ _ => trivial))] at h
    set hi := (S + T + 1) / 2
    set lo := hi - T
    apply le_trans (Finset.card_le_card _)
      (by rw [Nat.card_Ico]; omega : (Finset.Ico lo hi).card ≤ T)
    intro a ha
    rw [Finset.mem_image] at ha; obtain ⟨ε, hε, rfl⟩ := ha
    have habs : ((2 * (ws ε : ℤ)) - (S : ℤ)).natAbs < T := by
      simp only [inside, mem_filter, mem_univ, true_and] at hε; exact hε
    rw [Finset.mem_Ico]; constructor <;> omega

  have hinside_ge : 3 * 2 ^ k ≤ 4 * inside.card := by omega
  have h_final : 4 * inside.card ≤ 4 * T := by omega
  have hT_expand : 4 * T = 8 * n * (Nat.sqrt k + 1) := by
    show 4 * (2 * n * (Nat.sqrt k + 1)) = 8 * n * (Nat.sqrt k + 1); ring
  linarith

end DistinctSumsBound
