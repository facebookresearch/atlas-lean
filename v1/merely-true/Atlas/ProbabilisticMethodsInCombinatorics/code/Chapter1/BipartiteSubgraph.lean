/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset BigOperators SimpleGraph

namespace BipartiteSubgraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Boolean inequality `!=` is symmetric: $(f(a) \neq f(b)) = (f(b) \neq f(a))$. -/
lemma bne_symm {V : Type*} (f : V → Bool) (a b : V) :
    (f a != f b) = (f b != f a) := by
  rcases Bool.eq_false_or_eq_true (f a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (f b) with hb | hb <;> simp [ha, hb]

/-- For a Boolean labelling `f : V → Bool`, `boolCut f e` returns `true` when the
unordered pair `e = s(u, v)` is a cut edge, i.e. `f u ≠ f v`. -/
def boolCut (f : V → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨fun u v => f u != f v, bne_symm f⟩

omit [Fintype V] [DecidableEq V] in
/-- Evaluation of `boolCut` on an explicit pair `s(u, v)`. -/
@[simp] lemma boolCut_mk (f : V → Bool) (u v : V) :
    boolCut f s(u, v) = (f u != f v) :=
  Sym2.lift_mk _ u v

/-- `flipAt v f` is the Boolean labelling obtained from `f` by negating its value at `v`. -/
def flipAt {V : Type*} [DecidableEq V] (v : V) (f : V → Bool) : V → Bool :=
  Function.update f v (!f v)

/-- Flipping the value at `v` twice returns the original labelling. -/
lemma flipAt_involutive {V : Type*} [DecidableEq V] (v : V) :
    Function.Involutive (flipAt v : (V → Bool) → (V → Bool)) := by
  intro f; ext w; simp only [flipAt, Function.update]; split_ifs with h <;> simp_all

/-- If `u ≠ v`, then flipping `f` at `v` toggles whether the edge `{u, v}` is a cut edge. -/
lemma flipAt_bne_eq_not {V : Type*} [DecidableEq V]
    {u v : V} (huv : u ≠ v) (f : V → Bool) :
    (flipAt v f u != flipAt v f v) = !(f u != f v) := by
  simp only [flipAt, Function.update_of_ne huv, Function.update_self]
  rcases Bool.eq_false_or_eq_true (f u) with h | h <;>
    rcases Bool.eq_false_or_eq_true (f v) with h' | h' <;> simp [h, h']

/-- Exactly half of the Boolean labellings `f : V → Bool` separate the pair `{u, v}`
when `u ≠ v`; equivalently, twice that count equals the total number of labellings. -/
lemma two_mul_card_filter_bne (u v : V) (huv : u ≠ v) :
    2 * ((univ : Finset (V → Bool)).filter (fun f => f u != f v)).card =
    Fintype.card (V → Bool) := by
  classical
  set S := univ.filter (fun f : V → Bool => f u != f v)
  set T := univ.filter (fun f : V → Bool => !(f u != f v))
  have hST : S.card + T.card = Fintype.card (V → Bool) := by
    rw [← card_univ (α := V → Bool), ← card_union_of_disjoint]
    · congr 1; ext f; simp [S, T]; tauto
    · exact disjoint_filter.mpr (fun f _ h => by simp [h])
  suffices h : S.card = T.card by omega
  apply card_nbij (flipAt v)
  · intro f hf
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, S] at hf
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, T]
    rw [flipAt_bne_eq_not huv, hf]; rfl
  · intro f₁ _ f₂ _ heq; exact (flipAt_involutive v).injective heq
  · intro f hf
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, T] at hf
    refine ⟨flipAt v f, ?_, flipAt_involutive v f⟩
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, S]
    rw [flipAt_bne_eq_not huv]; simp only [Bool.not_eq_true'] at hf; rw [hf]; rfl

/-- Double-counting identity: summing the number of cut edges over all Boolean labellings
equals half of `|E(G)| · 2^{|V|}`. -/
lemma double_count_sum (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * ∑ f : V → Bool, (G.edgeFinset.filter (fun e => boolCut f e)).card =
    G.edgeFinset.card * Fintype.card (V → Bool) := by

  simp_rw [card_filter]

  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]

  rw [Finset.sum_comm (s := univ) (t := G.edgeFinset)]

  simp_rw [← Finset.mul_sum, ← card_filter]

  rw [Finset.mul_sum]

  rw [show G.edgeFinset.card * Fintype.card (V → Bool) =
    G.edgeFinset.card • Fintype.card (V → Bool) from (smul_eq_mul _ _).symm]
  apply Finset.sum_eq_card_nsmul
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | h u v =>
    simp only [boolCut_mk]
    exact two_mul_card_filter_bne u v he.ne

/-- (Theorem 1.0.1, first form) There exists a Boolean labelling $f : V \to \{0,1\}$
whose cut contains at least $\lfloor |E(G)|/2 \rfloor$ edges. -/
theorem exists_bipartite_subgraph_half_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ f : V → Bool, G.edgeFinset.card / 2 ≤
      (G.edgeFinset.filter (fun e => boolCut f e)).card := by

  by_contra h
  push Not at h

  have hN : (univ : Finset (V → Bool)).Nonempty := ⟨fun _ => true, mem_univ _⟩
  have hsum_lt := sum_lt_sum_of_nonempty hN (fun f _ => h f)
  simp only [sum_const, smul_eq_mul, card_univ] at hsum_lt


  nlinarith [double_count_sum G, Nat.mul_div_le G.edgeFinset.card 2]

/-- The cut subgraph of `G` induced by a Boolean labelling `f`: the subgraph consisting
of edges `{u, v}` of `G` with `f u ≠ f v`. -/
def cutGraph {V : Type*} (G : SimpleGraph V) (f : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ f u ≠ f v
  symm _ _ := fun ⟨h1, h2⟩ => ⟨G.symm h1, Ne.symm h2⟩
  loopless := ⟨fun _ h => absurd rfl h.2⟩

omit [Fintype V] [DecidableEq V] in
/-- The cut subgraph `cutGraph G f` is a subgraph of `G`. -/
lemma cutGraph_le (G : SimpleGraph V) (f : V → Bool) : cutGraph G f ≤ G :=
  fun _ _ h => h.1

omit [Fintype V] [DecidableEq V] in
/-- The cut subgraph `cutGraph G f` is bipartite (2-colorable), using `f` as the coloring. -/
lemma cutGraph_isBipartite (G : SimpleGraph V) (f : V → Bool) :
    (cutGraph G f).Colorable 2 := by
  refine ⟨⟨fun v => if f v then 0 else 1, fun {u v} h => ?_⟩⟩
  obtain ⟨_, hne⟩ := h
  rcases Bool.eq_false_or_eq_true (f u) with hu | hu <;>
    rcases Bool.eq_false_or_eq_true (f v) with hv | hv <;>
    simp_all

/-- The edge set of `cutGraph G f` is precisely the set of cut edges of `G` under `f`. -/
lemma cutGraph_edgeFinset_eq (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Bool)
    [Fintype (cutGraph G f).edgeSet] :
    (cutGraph G f).edgeFinset = G.edgeFinset.filter (fun e => boolCut f e) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_filter]
  constructor
  · intro he
    induction e using Sym2.ind with
    | h u v => exact ⟨he.1, by simp [boolCut_mk, bne_iff_ne, he.2]⟩
  · intro ⟨he, hcut⟩
    induction e using Sym2.ind with
    | h u v =>
      simp [boolCut_mk, bne_iff_ne] at hcut
      exact ⟨he, hcut⟩

/-- (Theorem 1.0.1) Every graph $G$ with $m$ edges has a bipartite subgraph $H \le G$
with at least $\lfloor m/2 \rfloor$ edges. -/
theorem exists_bipartite_subgraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.Colorable 2 ∧
      ∀ [Fintype H.edgeSet],
        G.edgeFinset.card / 2 ≤ H.edgeFinset.card := by
  obtain ⟨f, hf⟩ := exists_bipartite_subgraph_half_edges G
  refine ⟨cutGraph G f, cutGraph_le G f, cutGraph_isBipartite G f, fun {_} => ?_⟩
  rw [cutGraph_edgeFinset_eq]
  exact hf

end BipartiteSubgraph
