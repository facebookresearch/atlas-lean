/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable

set_option maxHeartbeats 800000

namespace ListChromatic

open Finset

/-- `IsKChoosable n k` says that the complete bipartite graph $K_{n,n}$ is $k$-choosable
in the combinatorial sense: for any color set $C$ and any pair of list assignments
$L, R : [n] \to \binom{C}{\ge k}$, there exist representatives $cL_i \in L_i$ and
$cR_j \in R_j$ with $cL_i \ne cR_j$ for all $i, j$. -/
def IsKChoosable (n k : ℕ) : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C] (L R : Fin n → Finset C),
    (∀ i, k ≤ (L i).card) →
    (∀ j, k ≤ (R j).card) →
    ∃ (cL : Fin n → C) (cR : Fin n → C),
      (∀ i, cL i ∈ L i) ∧
      (∀ j, cR j ∈ R j) ∧
      (∀ i j, cL i ≠ cR j)

/-- Key combinatorial lemma behind Theorem 1.4.2: when $n < 2^{k-1}$ and all lists have
size at least $k$, there exists a subset $A$ of colors hitting every left list and
missing at least one element of every right list. -/
theorem exists_good_subset {n k : ℕ} {C : Type} [Fintype C] [DecidableEq C]
    (L R : Fin n → Finset C)
    (hL : ∀ i, k ≤ (L i).card)
    (hR : ∀ j, k ≤ (R j).card)
    (hn : n < 2 ^ (k - 1)) :
    ∃ (A : Finset C),
      (∀ i, (L i ∩ A).Nonempty) ∧
      (∀ j, (R j \ A).Nonempty) := by
  classical

  by_contra h_all_bad
  simp only [not_exists, not_and, not_forall] at h_all_bad

  set d := Fintype.card C

  have hn_pos : 0 < n := by
    by_contra h
    push_neg at h
    interval_cases n
    have := h_all_bad ∅ (fun i => Fin.elim0 i)
    obtain ⟨j, _⟩ := this
    exact Fin.elim0 j
  have hdk : k ≤ d := by
    have : (L ⟨0, hn_pos⟩).card ≤ d := (L ⟨0, hn_pos⟩).card_le_univ
    linarith [hL ⟨0, hn_pos⟩]


  have h_every_bad : ∀ A : Finset C,
      (∃ i : Fin n, L i ∩ A = ∅) ∨ (∃ j : Fin n, R j ⊆ A) := by
    intro A
    by_cases hLA : ∀ i, (L i ∩ A).Nonempty
    · right
      obtain ⟨j, hj⟩ := h_all_bad A hLA
      exact ⟨j, sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp hj)⟩
    · left
      push_neg at hLA
      obtain ⟨i, hi⟩ := hLA
      exact ⟨i, hi⟩

  have h_left_count : ∀ i : Fin n,
      ((univ : Finset (Finset C)).filter (fun A => L i ∩ A = ∅)).card ≤ 2 ^ (d - k) := by
    intro i
    have h_sub : (univ.filter (fun A => L i ∩ A = ∅) : Finset (Finset C)) ⊆
        (Finset.univ \ L i).powerset := by
      intro A hA
      simp only [mem_filter, mem_univ, true_and] at hA
      rw [mem_powerset]
      intro x hxA
      rw [mem_sdiff]
      refine ⟨mem_univ x, fun hxL => ?_⟩
      have : x ∈ L i ∩ A := mem_inter.mpr ⟨hxL, hxA⟩
      rw [hA] at this
      simp at this
    calc ((univ : Finset (Finset C)).filter (fun A => L i ∩ A = ∅)).card
        ≤ ((Finset.univ \ L i).powerset).card := card_le_card h_sub
      _ = 2 ^ (Finset.univ \ L i).card := card_powerset _
      _ = 2 ^ (d - (L i).card) := by
          rw [card_sdiff_of_subset (subset_univ _), card_univ]
      _ ≤ 2 ^ (d - k) := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left (hL i) d)


  have h_right_count : ∀ j : Fin n,
      ((univ : Finset (Finset C)).filter (fun A => R j ⊆ A)).card ≤ 2 ^ (d - k) := by
    intro j
    have h_sub : (univ.filter (fun A => R j ⊆ A) : Finset (Finset C)) ⊆
        ((Finset.univ \ R j).powerset).image (· ∪ R j) := by
      intro A hA
      simp only [mem_filter, mem_univ, true_and] at hA
      rw [mem_image]
      refine ⟨A \ R j, ?_, ?_⟩
      · rw [mem_powerset]
        exact sdiff_subset_sdiff (subset_univ _) Subset.rfl
      · exact sdiff_union_of_subset hA
    calc ((univ : Finset (Finset C)).filter (fun A => R j ⊆ A)).card
        ≤ (((Finset.univ \ R j).powerset).image (· ∪ R j)).card := card_le_card h_sub
      _ ≤ ((Finset.univ \ R j).powerset).card := card_image_le
      _ = 2 ^ (Finset.univ \ R j).card := card_powerset _
      _ = 2 ^ (d - (R j).card) := by
          rw [card_sdiff_of_subset (subset_univ _), card_univ]
      _ ≤ 2 ^ (d - k) := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left (hR j) d)

  have h_cover : (univ : Finset (Finset C)) ⊆
      (Finset.univ.biUnion (fun i : Fin n => univ.filter (fun A => L i ∩ A = ∅))) ∪
      (Finset.univ.biUnion (fun j : Fin n => univ.filter (fun A => R j ⊆ A))) := by
    intro A _
    rw [mem_union, mem_biUnion, mem_biUnion]
    rcases h_every_bad A with ⟨i, hi⟩ | ⟨j, hj⟩
    · left; exact ⟨i, mem_univ _, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    · right; exact ⟨j, mem_univ _, mem_filter.mpr ⟨mem_univ _, hj⟩⟩

  have h_total : (univ : Finset (Finset C)).card = 2 ^ d := by
    rw [card_univ, Fintype.card_finset]
  have h_bound : (2 ^ d : ℕ) ≤ 2 * n * 2 ^ (d - k) := by
    calc (2 ^ d : ℕ)
        = (univ : Finset (Finset C)).card := h_total.symm
      _ ≤ ((Finset.univ.biUnion (fun i : Fin n => univ.filter (fun A => L i ∩ A = ∅))) ∪
          (Finset.univ.biUnion (fun j : Fin n => univ.filter (fun A => R j ⊆ A)))).card :=
          card_le_card h_cover
      _ ≤ (Finset.univ.biUnion (fun i : Fin n => univ.filter (fun A => L i ∩ A = ∅))).card +
          (Finset.univ.biUnion (fun j : Fin n => univ.filter (fun A => R j ⊆ A))).card :=
          card_union_le _ _
      _ ≤ n * 2 ^ (d - k) + n * 2 ^ (d - k) := by
          apply Nat.add_le_add
          · calc _ ≤ ∑ i : Fin n, (univ.filter (fun A => L i ∩ A = ∅)).card := card_biUnion_le
              _ ≤ ∑ _ : Fin n, 2 ^ (d - k) := sum_le_sum (fun i _ => h_left_count i)
              _ = n * 2 ^ (d - k) := by simp [sum_const, card_univ, Fintype.card_fin]
          · calc _ ≤ ∑ j : Fin n, (univ.filter (fun A => R j ⊆ A)).card := card_biUnion_le
              _ ≤ ∑ _ : Fin n, 2 ^ (d - k) := sum_le_sum (fun j _ => h_right_count j)
              _ = n * 2 ^ (d - k) := by simp [sum_const, card_univ, Fintype.card_fin]
      _ = 2 * n * 2 ^ (d - k) := by ring

  have h2n : 2 * n < 2 ^ k := by
    have h1 : n < 2 ^ (k - 1) := hn
    have h2 : 2 * 2 ^ (k - 1) = 2 ^ k := by
      cases k with
      | zero => omega
      | succ m => simp [pow_succ, mul_comm]
    linarith
  have h_contra : 2 * n * 2 ^ (d - k) < 2 ^ d := by
    have hpos : (0 : ℕ) < 2 ^ (d - k) := Nat.pos_of_ne_zero (Nat.two_pow_pos (d - k)).ne'
    calc 2 * n * 2 ^ (d - k)
        < 2 ^ k * 2 ^ (d - k) := by
          exact Nat.mul_lt_mul_of_pos_right h2n hpos
      _ = 2 ^ (k + (d - k)) := (pow_add 2 k (d - k)).symm
      _ = 2 ^ d := by congr 1; omega
  linarith

/-- (Theorem 1.4.2) If $n < 2^{k-1}$ and $k \ge 1$, then $K_{n,n}$ is $k$-choosable. -/
theorem knn_choosable (n k : ℕ) (_hk : 0 < k) (hn : n < 2 ^ (k - 1)) :
    IsKChoosable n k := by
  intro C _ _ L R hL hR
  obtain ⟨A, hA_left, hA_right⟩ := exists_good_subset L R hL hR hn
  have hcL : ∀ i, ∃ c, c ∈ L i ∧ c ∈ A := fun i => by
    obtain ⟨c, hc⟩ := hA_left i
    exact ⟨c, (mem_inter.mp hc).1, (mem_inter.mp hc).2⟩
  have hcR : ∀ j, ∃ c, c ∈ R j ∧ c ∉ A := fun j => by
    obtain ⟨c, hc⟩ := hA_right j
    exact ⟨c, (mem_sdiff.mp hc).1, (mem_sdiff.mp hc).2⟩
  refine ⟨fun i => (hcL i).choose, fun j => (hcR j).choose, ?_, ?_, ?_⟩
  · intro i; exact (hcL i).choose_spec.1
  · intro j; exact (hcR j).choose_spec.1
  · intro i j
    have hi : (hcL i).choose ∈ A := (hcL i).choose_spec.2
    have hj : (hcR j).choose ∉ A := (hcR j).choose_spec.2
    intro heq
    apply hj
    have : (fun i => (hcL i).choose) i = (fun j => (hcR j).choose) j := heq
    simp only at this
    rw [← this]
    exact hi

/-- Translation lemma used for the lower bound on $ch(K_{n,n})$: a $k$-uniform
hypergraph on $n$ edges that is not 2-colorable witnesses that $K_{n,n}$ is not
$k$-choosable. -/
theorem hypergraph_implies_not_choosable
    {V : Type*} [Fintype V] [DecidableEq V]
    (k n : ℕ) (_hk : 2 ≤ k)
    (E : TwoColorableHypergraph.Hypergraph V)
    (hE_unif : TwoColorableHypergraph.IsKUniform E k)
    (hE_edges : E.card = n)
    (hE_not_2col : ¬TwoColorableHypergraph.IsTwoColorable E) :
    ¬IsKChoosable n k := by
  classical
  intro h_choosable

  have : 0 < n := by
    by_contra h
    push Not at h
    interval_cases n
    simp only [Finset.card_eq_zero] at hE_edges
    exact hE_not_2col ⟨fun _ => true, fun e he => absurd he (by simp [hE_edges])⟩

  have hcard_eq : Fintype.card (Fin n) = Fintype.card ↥E := by
    rw [Fintype.card_fin, Fintype.card_coe]
    exact hE_edges.symm
  let edge_equiv : Fin n ≃ ↥E := Fintype.equivOfCardEq hcard_eq

  let edgeOf : Fin n → Finset V := fun i => (edge_equiv i).val
  have hedge_mem : ∀ i, edgeOf i ∈ E := fun i => (edge_equiv i).prop
  have hL_card : ∀ i, k ≤ (edgeOf i).card := by
    intro i
    have := hE_unif (edgeOf i) (hedge_mem i)
    omega

  let ι : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let edgeOf' : Fin n → Finset (Fin (Fintype.card V)) := fun i => (edgeOf i).map ι.toEmbedding
  have hL_card' : ∀ i, k ≤ (edgeOf' i).card := by
    intro i; simp only [edgeOf', Finset.card_map]; exact hL_card i
  obtain ⟨cL', cR', hcL_mem', hcR_mem', hcLR'⟩ :=
    h_choosable (Fin (Fintype.card V)) edgeOf' edgeOf' hL_card' hL_card'

  let cL : Fin n → V := fun i => ι.symm (cL' i)
  let cR : Fin n → V := fun i => ι.symm (cR' i)
  have mem_edgeOf_of_mem_edgeOf' : ∀ (f : Fin n → Fin (Fintype.card V)),
      (∀ i, f i ∈ edgeOf' i) → ∀ i, ι.symm (f i) ∈ edgeOf i := by
    intro f hf i
    have h := hf i
    simp only [edgeOf', Finset.mem_map, Equiv.toEmbedding_apply] at h
    obtain ⟨v, hv_in, hv_eq⟩ := h
    rw [← hv_eq, Equiv.symm_apply_apply]
    exact hv_in
  have hcL_mem : ∀ i, cL i ∈ edgeOf i := mem_edgeOf_of_mem_edgeOf' cL' hcL_mem'
  have hcR_mem : ∀ i, cR i ∈ edgeOf i := mem_edgeOf_of_mem_edgeOf' cR' hcR_mem'
  have hcLR : ∀ i j, cL i ≠ cR j := by
    intro i j h
    apply hcLR' i j
    show cL' i = cR' j
    have : ι (cL i) = ι (cR j) := congr_arg ι h
    simp only [cL, cR, Equiv.apply_symm_apply] at this
    exact this

  let c : V → Bool := fun v => if ∃ i, cL i = v then true else false

  apply hE_not_2col
  refine ⟨c, fun e he => ?_⟩

  let i := edge_equiv.symm ⟨e, he⟩
  have hi_eq : edgeOf i = e := by
    simp only [edgeOf, i]
    exact congr_arg Subtype.val (Equiv.apply_symm_apply edge_equiv ⟨e, he⟩)
  have hcLi_in_e : cL i ∈ e := hi_eq ▸ hcL_mem i
  have hc_cLi : c (cL i) = true := by
    simp only [c]
    rw [if_pos ⟨i, rfl⟩]
  have hcRi_in_e : cR i ∈ e := hi_eq ▸ hcR_mem i
  have hc_cRi : c (cR i) = false := by
    simp only [c]
    rw [if_neg]
    push Not
    intro j
    exact hcLR j i

  intro hmono
  simp only [TwoColorableHypergraph.IsMonochromatic] at hmono
  rcases hmono with h_all_true | h_all_false
  · exact Bool.noConfusion (hc_cRi ▸ h_all_true (cR i) hcRi_in_e)
  · exact Bool.noConfusion (hc_cLi ▸ h_all_false (cL i) hcLi_in_e)

end ListChromatic

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A list assignment on a vertex set `V` is a function assigning each vertex a finite
list of available colors. -/
abbrev ListAssignment (V : Type*) (C : Type*) := V → Finset C

/-- `G.IsListColorable' L` says that there is a proper coloring of `G` choosing each
vertex's color from its list `L v`. -/
def IsListColorable' {C : Type*} (L : ListAssignment V C) : Prop :=
  ∃ f : V → C, (∀ v, f v ∈ L v) ∧ (∀ v w, G.Adj v w → f v ≠ f w)

/-- A graph is $k$-choosable if every list assignment with lists of size at least $k$
admits a proper list coloring. -/
def IsKChoosable' (k : ℕ) : Prop :=
  ∀ (C : Type) [Fintype C] (L : ListAssignment V C),
    (∀ v, k ≤ (L v).card) → G.IsListColorable' L

/-- The list chromatic number $ch(G)$ of a graph $G$: the smallest $k$ for which $G$
is $k$-choosable, as an element of $\mathbb{N} \cup \{\infty\}$. -/
noncomputable def listChromaticNumber : ℕ∞ :=
  ⨅ k ∈ {n : ℕ | G.IsKChoosable' n}, (k : ℕ∞)

/-- The average degree of a finite graph $G$, i.e. $\frac{1}{|V|} \sum_{v} \deg(v)$
(or $0$ when $V$ is empty). -/
noncomputable def averageDegree [Fintype V] [DecidableRel G.Adj] : ℝ :=
  if Fintype.card V = 0 then 0
  else (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ)

end SimpleGraph


open SimpleGraph in
/-- Decidability of adjacency in the complete bipartite graph, when both vertex
types have decidable equality. -/
instance instDecidableRelAdjCompleteBipartiteGraph {V W : Type*} [DecidableEq V] [DecidableEq W] :
    DecidableRel (completeBipartiteGraph V W).Adj := by
  intro v w; simp only [completeBipartiteGraph_adj]; infer_instance

/-- Every vertex of $K_{n,n}$ has degree exactly $n$. -/
lemma completeBipartiteGraph_degree_eq (n : ℕ) (v : Fin n ⊕ Fin n) :
    (completeBipartiteGraph (Fin n) (Fin n)).degree v = n := by
  cases v with
  | inl i =>
    simp only [SimpleGraph.degree]
    have h : (completeBipartiteGraph (Fin n) (Fin n)).neighborFinset (Sum.inl i) =
           Finset.univ.image Sum.inr := by
      ext v
      simp only [SimpleGraph.mem_neighborFinset, completeBipartiteGraph_adj, Finset.mem_image,
                 Finset.mem_univ, true_and]
      constructor
      · intro hadj; cases v with | inl j => simp at hadj | inr j => exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩; simp
    rw [h, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin]
  | inr j =>
    simp only [SimpleGraph.degree]
    have h : (completeBipartiteGraph (Fin n) (Fin n)).neighborFinset (Sum.inr j) =
           Finset.univ.image Sum.inl := by
      ext v
      simp only [SimpleGraph.mem_neighborFinset, completeBipartiteGraph_adj, Finset.mem_image,
                 Finset.mem_univ, true_and]
      constructor
      · intro hadj; cases v with | inl i => exact ⟨i, rfl⟩ | inr i => simp at hadj
      · rintro ⟨i, rfl⟩; simp
    rw [h, Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ, Fintype.card_fin]

/-- The average degree of $K_{n,n}$ is $n$. -/
lemma completeBipartiteGraph_averageDegree (n : ℕ) (hn : 0 < n) :
    (completeBipartiteGraph (Fin n) (Fin n)).averageDegree = (n : ℝ) := by
  unfold SimpleGraph.averageDegree
  have hcard : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
    simp [Fintype.card_sum, Fintype.card_fin, two_mul]
  have hcard_ne : Fintype.card (Fin n ⊕ Fin n) ≠ 0 := by rw [hcard]; omega
  rw [if_neg hcard_ne]
  have hsum : (∑ v : Fin n ⊕ Fin n,
      ((completeBipartiteGraph (Fin n) (Fin n)).degree v : ℝ)) = 2 * ↑n * (↑n : ℝ) := by
    simp only [completeBipartiteGraph_degree_eq]
    rw [Finset.sum_const, Finset.card_univ, hcard]
    ring
  rw [hsum, hcard, show (↑(2 * n) : ℝ) = 2 * ↑n from by push_cast; ring]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp



/-- The combinatorial `IsKChoosable n k` condition implies that $K_{n,n}$
is $k$-choosable in the graph-theoretic sense. -/
lemma knn_IsKChoosable'_of_IsKChoosable (n k : ℕ)
    (h : ListChromatic.IsKChoosable n k) :
    (completeBipartiteGraph (Fin n) (Fin n)).IsKChoosable' k := by
  intro C _inst Lf hLf
  classical
  set L : Fin n → Finset C := fun i => Lf (Sum.inl i)
  set R : Fin n → Finset C := fun j => Lf (Sum.inr j)
  have hL : ∀ i, k ≤ (L i).card := fun i => hLf (Sum.inl i)
  have hR : ∀ j, k ≤ (R j).card := fun j => hLf (Sum.inr j)
  obtain ⟨cL, cR, hcL_mem, hcR_mem, hcLR⟩ := h C L R hL hR
  refine ⟨Sum.elim cL cR, ?_, ?_⟩
  · intro v
    cases v with
    | inl i => exact hcL_mem i
    | inr j => exact hcR_mem j
  · intro v w hadj
    cases v with
    | inl i =>
      cases w with
      | inl j => exfalso; simp [completeBipartiteGraph] at hadj
      | inr j =>
        simp only [Sum.elim_inl, Sum.elim_inr]
        exact hcLR i j
    | inr i =>
      cases w with
      | inl j =>
        simp only [Sum.elim_inr, Sum.elim_inl]
        exact Ne.symm (hcLR j i)
      | inr j => exfalso; simp [completeBipartiteGraph] at hadj

/-- If $G$ is $k$-choosable then its list chromatic number is at most $k$. -/
lemma SimpleGraph.listChromaticNumber_le_of_isKChoosable' {V : Type*}
    (G : SimpleGraph V) (k : ℕ) (h : G.IsKChoosable' k) :
    G.listChromaticNumber ≤ (k : ℕ∞) := by
  unfold SimpleGraph.listChromaticNumber
  apply iInf₂_le
  exact h

/-- Auxiliary inequality: for $n > 1$ with $\log_2 n > 1/\varepsilon$, we have
$n < 2^{\lceil (1 + \varepsilon)\log_2 n \rceil - 1}$, allowing application of the
$k$-choosability bound. -/
lemma aux_n_lt_pow_ceil_sub_one {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hn_gt_one : 1 < n)
    (hlogn_large : 1 / ε < Real.log ↑n / Real.log 2) :
    n < 2 ^ (Nat.ceil ((1 + ε) * (Real.log ↑n / Real.log 2)) - 1) := by
  set logb2n := Real.log ↑n / Real.log 2
  set k := Nat.ceil ((1 + ε) * logb2n)
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlogn_pos : 0 < Real.log (↑n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn_gt_one)
  have hlogb2n_pos : 0 < logb2n := div_pos hlogn_pos hlog2_pos
  have hkval_pos : 0 < (1 + ε) * logb2n := by positivity
  have hk_ge_one : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hkval_pos).ne'
  have hk_lb : (1 + ε) * logb2n ≤ (k : ℝ) := Nat.le_ceil _

  have heps_logn : 1 < ε * logb2n := by
    have h1 : 1 / ε < logb2n := hlogn_large
    have h2 : 0 < ε := hε
    rw [div_lt_iff₀ h2] at h1
    linarith
  have hk_sub_gt : logb2n < (↑(k - 1) : ℝ) := by
    rw [Nat.cast_sub hk_ge_one]


    have h1 : logb2n + ε * logb2n ≤ (k : ℝ) := by linarith [hk_lb, show (1 + ε) * logb2n = logb2n + ε * logb2n from by ring]
    linarith [show (1 : ℝ) = (↑(1 : ℕ) : ℝ) from by norm_cast]


  have hlog_lt : Real.log (↑n : ℝ) < ↑(k - 1) * Real.log 2 := by
    have heq : Real.log (↑n : ℝ) = logb2n * Real.log 2 := by
      simp only [logb2n]
      rw [div_mul_cancel₀ (Real.log ↑n) (ne_of_gt hlog2_pos)]
    rw [heq]
    exact mul_lt_mul_of_pos_right hk_sub_gt hlog2_pos
  have hlt : (↑n : ℝ) < (2 : ℝ) ^ (k - 1 : ℕ) :=
    Real.lt_pow_of_log_lt (by norm_num : (0 : ℝ) < 2) hlog_lt
  exact_mod_cast hlt

/-- (Half of Corollary 1.4.4, upper direction) Asymptotic upper bound
$ch(K_{n,n}) \le (1 + \varepsilon) \log_2 n$ for all sufficiently large $n$. -/
theorem ch_knn_asymptotic_upper :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (completeBipartiteGraph (Fin n) (Fin n)).listChromaticNumber ≤
          (Nat.ceil ((1 + ε) * (Real.log ↑n / Real.log 2)) : ℕ∞) := by
  intro ε hε

  use Nat.ceil ((2 : ℝ) ^ (1 / ε)) + 2
  intro n hn
  have hn_gt_one : 1 < n := by
    have : (2 : ℕ) ≤ Nat.ceil ((2 : ℝ) ^ (1 / ε)) + 2 := Nat.le_add_left 2 _
    omega
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlogn_pos : 0 < Real.log (↑n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn_gt_one)

  have hlogn_large : 1 / ε < Real.log ↑n / Real.log 2 := by
    have hn_large : (2 : ℝ) ^ (1 / ε) < (n : ℝ) := by
      have h1 : (2 : ℝ) ^ (1 / ε) ≤ (Nat.ceil ((2 : ℝ) ^ (1 / ε)) : ℝ) := Nat.le_ceil _
      have h2 : (↑(Nat.ceil ((2 : ℝ) ^ (1 / ε)) + 2) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast at h2
      linarith
    have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (1 / ε) := by positivity
    have hlog_ineq : (1 / ε) * Real.log 2 < Real.log (↑n : ℝ) := by
      calc (1 / ε) * Real.log 2
          = Real.log ((2 : ℝ) ^ (1 / ε)) := by
            rw [Real.log_rpow (by norm_num : (0:ℝ) < 2)]
        _ < Real.log (↑n : ℝ) := Real.log_lt_log h2_pos hn_large


    rwa [lt_div_iff₀ hlog2_pos]

  have hk_val_pos : 0 < (1 + ε) * (Real.log ↑n / Real.log 2) := by positivity
  have hk_ge_one : 1 ≤ Nat.ceil ((1 + ε) * (Real.log ↑n / Real.log 2)) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hk_val_pos).ne'
  have hk_pos : 0 < Nat.ceil ((1 + ε) * (Real.log ↑n / Real.log 2)) := by omega
  have hn_lt := aux_n_lt_pow_ceil_sub_one hε hn_gt_one hlogn_large
  have h_choosable := ListChromatic.knn_choosable n _ hk_pos hn_lt
  have h_choosable' := knn_IsKChoosable'_of_IsKChoosable n _ h_choosable
  exact SimpleGraph.listChromaticNumber_le_of_isKChoosable' _ _ h_choosable'

