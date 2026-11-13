/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Basic

namespace GraphMatrices

open Matrix SimpleGraph

section AdjMatrix

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable abbrev adjMatrix : Matrix V V ℝ :=
  G.adjMatrix ℝ

end AdjMatrix

section LaplacianEigenvalues

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open Finset Matrix

theorem laplacian_mulVec_ones_eq_zero :
    (G.lapMatrix ℝ).mulVec (fun _ => (1 : ℝ)) = 0 :=
  SimpleGraph.lapMatrix_mulVec_const_eq_zero G

theorem laplacian_posSemidef : PosSemidef (G.lapMatrix ℝ) :=
  SimpleGraph.posSemidef_lapMatrix ℝ G

theorem laplacian_proposition_6 :
    (G.lapMatrix ℝ).mulVec (fun _ => (1 : ℝ)) = 0 ∧ PosSemidef (G.lapMatrix ℝ) :=
  ⟨laplacian_mulVec_ones_eq_zero G, laplacian_posSemidef G⟩

end LaplacianEigenvalues

section SignedIncidenceMatrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

structure EdgeOrientation (G : SimpleGraph V) where
  orient : G.edgeSet → V × V
  edge_eq : ∀ e : G.edgeSet, s((orient e).1, (orient e).2) = (e : Sym2 V)

variable {G} [Fintype G.edgeSet]

lemma sum_incident_eq_degree (i : V) :
    (∑ e : G.edgeSet, if i ∈ (e : Sym2 V) then (1 : ℝ) else 0) = (G.degree i : ℝ) := by
  rw [Finset.sum_boole, Nat.cast_inj]
  rw [← SimpleGraph.card_incidenceSet_eq_degree, ← Fintype.card_subtype]
  apply Fintype.card_congr
  refine ⟨fun ⟨⟨e, he⟩, hm⟩ => ⟨e, he, hm⟩, fun ⟨e, he, hm⟩ => ⟨⟨e, he⟩, hm⟩, ?_, ?_⟩
  · intro ⟨⟨e, he⟩, hm⟩; rfl
  · intro ⟨e, he, hm⟩; rfl

variable (σ : EdgeOrientation G)

noncomputable def signedIncidenceMatrix : Matrix G.edgeSet V ℝ :=
  fun e v =>
    if v = (σ.orient e).1 then 1
    else if v = (σ.orient e).2 then -1
    else 0

theorem lapMatrix_eq_transpose_mul_signedIncMatrix :
    G.lapMatrix ℝ = (signedIncidenceMatrix σ)ᵀ * (signedIncidenceMatrix σ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, signedIncidenceMatrix]
  by_cases hij : i = j
  ·
    subst hij
    have hlap : G.lapMatrix ℝ i i = (G.degree i : ℝ) := by
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal_apply_eq,
        SimpleGraph.adjMatrix_apply]
    rw [hlap]
    have hconv : ∀ e : G.edgeSet,
        (if i = (σ.orient e).1 then (1 : ℝ) else if i = (σ.orient e).2 then -1 else 0) *
        (if i = (σ.orient e).1 then 1 else if i = (σ.orient e).2 then -1 else 0) =
        if i ∈ (e : Sym2 V) then 1 else 0 := by
      intro e
      have hmem : i ∈ (e : Sym2 V) ↔ i = (σ.orient e).1 ∨ i = (σ.orient e).2 := by
        rw [← σ.edge_eq e]; exact Sym2.mem_iff
      split_ifs with h1 h2 <;> simp_all
    simp_rw [hconv]
    exact (sum_incident_eq_degree i).symm
  ·
    have hlap : G.lapMatrix ℝ i j = if G.Adj i j then -1 else 0 := by
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix_apply, hij]
      split_ifs with h <;> ring
    rw [hlap]
    have hconv : ∀ e : G.edgeSet,
        (if i = (σ.orient e).1 then (1 : ℝ) else if i = (σ.orient e).2 then -1 else 0) *
        (if j = (σ.orient e).1 then 1 else if j = (σ.orient e).2 then -1 else 0) =
        if (e : Sym2 V) = s(i, j) then -1 else 0 := by
      intro e
      have hne : (σ.orient e).1 ≠ (σ.orient e).2 := by
        intro h; have := σ.edge_eq e; have he := e.prop
        rw [← this, SimpleGraph.mem_edgeSet, h] at he; exact he.ne rfl
      have hcond : (e : Sym2 V) = s(i, j) ↔
          ((σ.orient e).1 = i ∧ (σ.orient e).2 = j) ∨
          ((σ.orient e).1 = j ∧ (σ.orient e).2 = i) := by
        rw [← σ.edge_eq e]; exact Sym2.eq_iff
      split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp_all <;> tauto
    simp_rw [hconv]
    split_ifs with hadj
    ·
      have he : s(i, j) ∈ G.edgeSet := (SimpleGraph.mem_edgeSet G).mpr hadj
      rw [Finset.sum_eq_single ⟨s(i, j), he⟩]
      · simp
      · intro e _ hne
        simp only [ite_eq_right_iff, neg_eq_zero, one_ne_zero]
        intro heq; exact absurd (Subtype.ext heq) hne
      · intro h; exact absurd (Finset.mem_univ _) h
    ·
      symm; apply Finset.sum_eq_zero
      intro e _
      simp only [ite_eq_right_iff, neg_eq_zero, one_ne_zero]
      intro heq
      have : (e : Sym2 V) ∈ G.edgeSet := e.prop
      rw [heq, SimpleGraph.mem_edgeSet] at this
      exact absurd this hadj

end SignedIncidenceMatrix

section QuadraticFormEdges

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  [Fintype G.edgeSet]

open Finset Matrix

omit [DecidableEq V] [Fintype G.edgeSet] in
lemma double_sum_adj_eq_dart_sum (f : V → V → ℝ) :
    (∑ i : V, ∑ j : V, if G.Adj i j then f i j else 0) =
    ∑ d : G.Dart, f d.toProd.1 d.toProd.2 := by
  trans (∑ p : V × V, if G.Adj p.1 p.2 then f p.1 p.2 else 0)
  · rw [← Finset.sum_product']; rfl
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun (p : V × V) (hp : p ∈ Finset.univ.filter _) =>
    (⟨p, (Finset.mem_filter.mp hp).2⟩ : G.Dart))
  · intro a ha; exact Finset.mem_univ _
  · intro a₁ ha₁ a₂ ha₂ heq; exact congr_arg SimpleGraph.Dart.toProd heq
  · intro d _; refine ⟨d.toProd, by simp [Finset.mem_filter, d.adj], ?_⟩; cases d; rfl
  · intro a ha; rfl

lemma dart_sum_eq_twice_edge_sum (f : V → V → ℝ) (hf : ∀ a b, f a b = f b a) :
    ∑ d : G.Dart, f d.toProd.1 d.toProd.2 =
    2 * ∑ e ∈ G.edgeFinset, Sym2.lift ⟨f, fun a b => hf a b⟩ e := by
  have hfw : ∑ d : G.Dart, f d.toProd.1 d.toProd.2 =
      ∑ e ∈ G.edgeFinset, ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.edge = e),
        f d.toProd.1 d.toProd.2 := by
    rw [← sum_fiberwise_of_maps_to (g := SimpleGraph.Dart.edge)]
    intro d _; exact mem_edgeFinset.mpr (SimpleGraph.Dart.edge_mem d)
  rw [hfw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  revert he
  refine Sym2.ind (fun a b he => ?_) e
  rw [mem_edgeFinset] at he
  set d : G.Dart := ⟨(a, b), he⟩
  have hfilt : (Finset.univ.filter (fun d' : G.Dart => d'.edge = s(a, b))) = {d, d.symm} :=
    d.edge_fiber
  rw [hfilt, Finset.sum_insert, Finset.sum_singleton]
  · simp only [Sym2.lift_mk]
    change f a b + f b a = 2 * f a b
    rw [hf b a]; ring
  · rw [Finset.mem_singleton]; exact d.symm_ne.symm

lemma sum_adj_div_two_eq_sum_edges (f : V → V → ℝ) (hf : ∀ a b, f a b = f b a) :
    (∑ i : V, ∑ j : V, if G.Adj i j then f i j else 0) / 2 =
    ∑ e ∈ G.edgeFinset, Sym2.lift ⟨f, fun a b => hf a b⟩ e := by
  rw [double_sum_adj_eq_dart_sum G f, dart_sum_eq_twice_edge_sum G f hf,
      mul_div_cancel_left₀]
  exact two_ne_zero

theorem lapMatrix_quadForm_eq_sum_edges (x : V → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ).mulVec x =
    ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun i j => (x i - x j) ^ 2, fun a b => by ring⟩ e := by
  rw [← Matrix.toLinearMap₂'_apply' (T := ℝ)]
  rw [SimpleGraph.lapMatrix_toLinearMap₂' ℝ G x]
  exact sum_adj_div_two_eq_sum_edges G (fun i j => (x i - x j) ^ 2) (fun a b => by ring)

theorem lapMatrix_quadForm_nonneg (x : V → ℝ) :
    0 ≤ x ⬝ᵥ (G.lapMatrix ℝ).mulVec x := by
  rw [lapMatrix_quadForm_eq_sum_edges G x]
  apply Finset.sum_nonneg
  intro e _
  exact Sym2.ind (fun a b => sq_nonneg _) e

end QuadraticFormEdges

end GraphMatrices
