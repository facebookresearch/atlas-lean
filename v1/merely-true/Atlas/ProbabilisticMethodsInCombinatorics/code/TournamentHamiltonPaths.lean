/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Permanent
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Permanent
set_option maxHeartbeats 3200000

open Real Finset BigOperators

namespace TournamentHamiltonPaths

/-- A tournament on $n$ vertices: an irreflexive, complete, asymmetric directed-edge
relation on $\mathrm{Fin}\, n$, equipped with a decidability instance. -/
structure Tournament (n : ℕ) where
  edge : Fin n → Fin n → Prop
  irrefl : ∀ i, ¬ edge i i
  complete : ∀ i j, i ≠ j → (edge i j ∨ edge j i)
  antisymm : ∀ i j, edge i j → ¬ edge j i
  [decEdge : DecidableRel edge]

attribute [instance] Tournament.decEdge

/-- Number of Hamilton paths of $T$: permutations $\sigma$ of $\mathrm{Fin}\, n$ such that
every consecutive edge $\sigma(i) \to \sigma(i+1)$ lies in $T$. -/
noncomputable def Tournament.numHamiltonPaths {n : ℕ} (T : Tournament n) : ℕ := by
  classical
  exact (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ∀ i : Fin n, (h : i.val + 1 < n) → T.edge (σ i) (σ ⟨i.val + 1, h⟩)).card

/-- Number of Hamilton cycles of $T$: permutations $\sigma$ of $\mathrm{Fin}(n+1)$ such
that every cyclic edge $\sigma(i) \to \sigma(i+1)$ lies in $T$; zero if $n = 0$. -/
noncomputable def Tournament.numHamiltonCycles {n : ℕ} (T : Tournament n) : ℕ := by
  classical
  exact match n, T with
  | 0, _ => 0
  | n + 1, T =>
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) =>
      ∀ i : Fin (n + 1), T.edge (σ i) (σ (i + 1))).card

/-- Trivial bound: the number of Hamilton paths is at most $n!$, the total number of
permutations of $\mathrm{Fin}\, n$. -/
lemma numHamiltonPaths_le_factorial {n : ℕ} (T : Tournament n) :
    T.numHamiltonPaths ≤ n.factorial := by
  classical
  unfold Tournament.numHamiltonPaths
  calc (Finset.univ.filter _).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = Fintype.card (Equiv.Perm (Fin n)) := rfl
    _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]

/-- Adjacency matrix of a tournament as a real $0/1$-matrix: entry $(i, j)$ is $1$ if
$T$ has the edge $i \to j$, else $0$. -/
noncomputable def Tournament.adjMatrix {n : ℕ} (T : Tournament n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => if T.edge i j then (1 : ℝ) else 0)

/-- Every entry of the tournament's adjacency matrix is $0$ or $1$. -/
lemma Tournament.adjMatrix_zero_one {n : ℕ} (T : Tournament n) :
    ∀ i j, T.adjMatrix i j = 0 ∨ T.adjMatrix i j = 1 := by
  intro i j
  simp only [Tournament.adjMatrix, Matrix.of_apply]
  split_ifs <;> simp

/-- Successor permutation derived from $\sigma$: the conjugate $\sigma \circ (+1) \circ
\sigma^{-1}$, which sends $\sigma(j)$ to $\sigma(j + 1)$. -/
noncomputable def toSuccPerm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 1)) :=
  σ * Equiv.addRight (1 : Fin (n + 1)) * σ⁻¹

@[simp] private lemma toSuccPerm_apply {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1)) :
    toSuccPerm σ v = σ (σ⁻¹ v + 1) := by
  simp [toSuccPerm, Equiv.Perm.mul_apply, Equiv.addRight]

/-- Successor relation: $\sigma(j + 1) = (\mathrm{toSuccPerm}\,\sigma)(\sigma(j))$. -/
lemma successor_relation {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    σ (j + 1) = (toSuccPerm σ) (σ j) := by simp

/-- If $\sigma$ encodes a Hamilton cycle of $T$, then for every vertex $v$ the directed
edge $v \to (\mathrm{toSuccPerm}\,\sigma)(v)$ lies in $T$. -/
lemma toSuccPerm_valid {n : ℕ} (T : Tournament (n + 1))
    (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : ∀ i : Fin (n + 1), T.edge (σ i) (σ (i + 1))) :
    ∀ v : Fin (n + 1), T.edge v (toSuccPerm σ v) := by
  intro v; simp only [toSuccPerm_apply]
  have h := hσ (σ⁻¹ v); convert h using 2; simp

/-- Two permutations with the same successor permutation and the same value at $0$ must
be equal: induct on the index using the successor relation. -/
lemma fiber_eq_of_eq_at_zero {n : ℕ}
    (σ₁ σ₂ : Equiv.Perm (Fin (n + 1)))
    (heq : toSuccPerm σ₁ = toSuccPerm σ₂) (h0 : σ₁ 0 = σ₂ 0) : σ₁ = σ₂ := by
  set τ := toSuccPerm σ₁
  have h1 : ∀ j, σ₁ (j + 1) = τ (σ₁ j) := successor_relation σ₁
  have h2 : ∀ j, σ₂ (j + 1) = τ (σ₂ j) := by
    intro j; have := successor_relation σ₂ j; rw [← heq] at this; exact this
  apply Equiv.ext; intro ⟨i, hi⟩
  induction i with
  | zero => convert h0
  | succ k ih =>
    have hk : k < n + 1 := by omega
    have hfin : (⟨k + 1, hi⟩ : Fin (n + 1)) = (⟨k, hk⟩ : Fin (n + 1)) + 1 := by
      ext; show k + 1 = ((⟨k, hk⟩ : Fin (n + 1)) + 1).val
      simp [Fin.val_add, Nat.mod_eq_of_lt hi]
    rw [show σ₁ ⟨k + 1, hi⟩ = σ₁ ((⟨k, hk⟩ : Fin (n + 1)) + 1) from by rw [← hfin],
        show σ₂ ⟨k + 1, hi⟩ = σ₂ ((⟨k, hk⟩ : Fin (n + 1)) + 1) from by rw [← hfin],
        h1 ⟨k, hk⟩, h2 ⟨k, hk⟩, ih hk]

/-- Permanent lower bound: if $S$ is a set of permutations $\sigma$ with $A_{\sigma(i), i}
= 1$ for all $i$, then $\mathrm{perm}(A) \ge |S|$. -/
lemma permanent_ge_card_row {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (S : Finset (Equiv.Perm (Fin m)))
    (hS : ∀ σ ∈ S, ∀ i, A (σ i) i = 1) :
    (S.card : ℝ) ≤ A.permanent := by
  unfold Matrix.permanent
  calc (S.card : ℝ) = ∑ _ ∈ S, (1 : ℝ) := by rw [Finset.sum_const, Nat.smul_one_eq_cast]
    _ ≤ ∑ σ ∈ S, ∏ i : Fin m, A (σ i) i :=
        Finset.sum_le_sum (fun σ hσ => by rw [Finset.prod_eq_one (fun i _ => hS σ hσ i)])
    _ ≤ ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, A (σ i) i :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ => Finset.mem_univ _)
          (fun σ _ _ => Finset.prod_nonneg
            (fun i _ => by rcases hA (σ i) i with h | h <;> linarith))

/-- Adjacency-matrix entry is $1$ iff the corresponding tournament edge exists. -/
lemma adjMatrix_entry_one_iff {m : ℕ} (T : Tournament m) (i j : Fin m) :
    T.adjMatrix i j = 1 ↔ T.edge i j := by
  simp only [Tournament.adjMatrix, Matrix.of_apply]; split_ifs with h <;> simp [h]

/-- Key counting bound: the number of Hamilton cycles is at most $(n + 1) \cdot
\mathrm{perm}(A_T)$, where $A_T$ is the adjacency matrix of $T$. -/
theorem numHamiltonCycles_le_mul_permanent {n : ℕ} (T : Tournament (n + 1)) :
    (T.numHamiltonCycles : ℝ) ≤ (n + 1) * T.adjMatrix.permanent := by
  classical
  set S := Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
    ∀ i : Fin (n + 1), T.edge (σ i) (σ (i + 1)))
  have hnum : T.numHamiltonCycles = S.card := by
    unfold Tournament.numHamiltonCycles; rfl
  rw [hnum]
  have hS_prop : ∀ σ ∈ S, ∀ i : Fin (n + 1), T.edge (σ i) (σ (i + 1)) :=
    fun σ hσ => (Finset.mem_filter.mp hσ).2

  have h_fiber : ∀ τ ∈ Finset.image (toSuccPerm (n := n)) S,
      (S.filter (fun σ => toSuccPerm σ = τ)).card ≤ n + 1 := by
    intro τ _
    have hinj : Set.InjOn (fun σ : Equiv.Perm (Fin (n + 1)) => σ (0 : Fin (n + 1)))
        ↑(S.filter (fun σ => toSuccPerm σ = τ)) := by
      intro σ₁ hσ₁ σ₂ hσ₂ heq_val
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hσ₁ hσ₂
      exact fiber_eq_of_eq_at_zero σ₁ σ₂ (hσ₁.2.trans hσ₂.2.symm) heq_val
    calc (S.filter (fun σ => toSuccPerm σ = τ)).card
        ≤ (Finset.univ : Finset (Fin (n + 1))).card :=
          Finset.card_le_card_of_injOn (fun σ => σ 0) (fun _ _ => Finset.mem_univ _) hinj
      _ = n + 1 := Finset.card_fin _
  have h_bound : S.card ≤ (n + 1) * (Finset.image toSuccPerm S).card :=
    Finset.card_le_mul_card_image S (n + 1) h_fiber

  have h_image_valid : ∀ τ ∈ Finset.image (toSuccPerm (n := n)) S,
      ∀ v, T.adjMatrix v (τ v) = 1 := by
    intro τ hτ
    rw [Finset.mem_image] at hτ
    obtain ⟨σ, hσS, rfl⟩ := hτ
    intro v; rw [adjMatrix_entry_one_iff]
    exact toSuccPerm_valid T σ (hS_prop σ hσS) v
  let imgInv := (Finset.image toSuccPerm S).map
    ⟨fun σ => σ⁻¹, fun a b h => by simpa using congr_arg (·⁻¹) h⟩
  have h_imgInv_valid : ∀ σ ∈ imgInv, ∀ i, T.adjMatrix (σ i) i = 1 := by
    intro σ hσ
    simp only [imgInv, Finset.mem_map, Function.Embedding.coeFn_mk] at hσ
    obtain ⟨τ, hτ, rfl⟩ := hσ
    intro i; have := h_image_valid τ hτ (τ⁻¹ i); simp at this; exact this
  have h_imgInv_card : (Finset.image toSuccPerm S).card = imgInv.card := by simp [imgInv]
  have h_perm_ge : ((Finset.image toSuccPerm S).card : ℝ) ≤ T.adjMatrix.permanent := by
    rw [h_imgInv_card]
    exact permanent_ge_card_row T.adjMatrix T.adjMatrix_zero_one imgInv h_imgInv_valid

  have h_np1 : (↑(n + 1) : ℝ) = (↑n : ℝ) + 1 := by push_cast; ring
  calc (S.card : ℝ)
      ≤ ↑((n + 1) * (Finset.image toSuccPerm S).card) := by exact_mod_cast h_bound
    _ = (↑(n + 1) : ℝ) * ↑((Finset.image toSuccPerm S).card) := by push_cast; ring
    _ ≤ (↑(n + 1) : ℝ) * T.adjMatrix.permanent :=
        mul_le_mul_of_nonneg_left h_perm_ge (Nat.cast_nonneg' _)
    _ = ((↑n : ℝ) + 1) * T.adjMatrix.permanent := by rw [h_np1]






end TournamentHamiltonPaths
