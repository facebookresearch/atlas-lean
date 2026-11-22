/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Algebra.Ring.Real
set_option maxHeartbeats 400000

open scoped Classical
open Finset BigOperators Filter Topology

namespace CliqueNumber

/-- Expected number of $k$-cliques in the random graph $G(n, 1/2)$,
    equal to $\binom{n}{k} \cdot 2^{-\binom{k}{2}}$. -/
noncomputable def expectedKCliques (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (2 : ℝ) ^ (-(k.choose 2 : ℤ))

/-- Rewrites the expected number of $k$-cliques as the quotient
    $\binom{n}{k} / 2^{\binom{k}{2}}$. -/
lemma expectedKCliques_eq_div (n k : ℕ) :
    expectedKCliques n k = (n.choose k : ℝ) / (2 : ℝ) ^ (k.choose 2) := by
  unfold expectedKCliques
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- Probability under the uniform measure on simple graphs on $\{1,\dots,n\}$
    (equivalently $G(n, 1/2)$) that the graph contains a clique of size at least $k$. -/
noncomputable def probCliqueGe (n k : ℕ) : ℝ :=
  ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => ¬G.CliqueFree k)).card : ℝ) /
  (Fintype.card (SimpleGraph (Fin n)) : ℝ)

/-- The probability `probCliqueGe n k` is nonnegative. -/
lemma probCliqueGe_nonneg (n k : ℕ) : 0 ≤ probCliqueGe n k := by
  unfold probCliqueGe; positivity

/-- In a Boolean algebra, if $H \le a$ and $K \le a^c$, then $(H \sqcup K) \sqcap a = H$. -/
lemma ba_sup_inf_right {α : Type*} [BooleanAlgebra α] {a H K : α}
    (hH : H ≤ a) (hK : K ≤ aᶜ) : (H ⊔ K) ⊓ a = H := by
  rw [inf_sup_right, le_bot_iff.mp (le_trans (inf_le_inf_right a hK) (by simp)),
    inf_of_le_left hH, sup_bot_eq]

/-- In a Boolean algebra, if $H \le a$ and $K \le a^c$, then $(H \sqcup K) \sqcap a^c = K$. -/
lemma ba_sup_inf_compl {α : Type*} [BooleanAlgebra α] {a H K : α}
    (hH : H ≤ a) (hK : K ≤ aᶜ) : (H ⊔ K) ⊓ aᶜ = K := by
  rw [inf_sup_right, le_bot_iff.mp (le_trans (inf_le_inf_right aᶜ hH) (by simp)),
    inf_of_le_left hK, bot_sup_eq]

/-- Equivalence decomposing a Boolean algebra $\alpha$ as the product
    $[\bot, a] \times [\bot, a^c]$ via the map $x \mapsto (x \sqcap a, x \sqcap a^c)$. -/
noncomputable def boolAlgDecomp {α : Type*} [BooleanAlgebra α] (a : α) :
    α ≃ Set.Iic a × Set.Iic aᶜ where
  toFun x := ⟨⟨x ⊓ a, inf_le_right⟩, ⟨x ⊓ aᶜ, inf_le_right⟩⟩
  invFun p := (p.1 : α) ⊔ (p.2 : α)
  left_inv x := by
    show x ⊓ a ⊔ x ⊓ aᶜ = x
    rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
  right_inv p := by
    ext
    · exact ba_sup_inf_right p.1.2 p.2.2
    · exact ba_sup_inf_compl p.1.2 p.2.2

/-- Equivalence between the upper set $[a, \top]$ and the lower set $[\bot, a^c]$
    in a Boolean algebra, given by complementation. -/
noncomputable def iciEquivIicCompl {α : Type*} [BooleanAlgebra α] (a : α) :
    Set.Ici a ≃ Set.Iic aᶜ where
  toFun x := ⟨(x : α)ᶜ, compl_le_compl x.2⟩
  invFun y := ⟨(y : α)ᶜ, compl_le_compl_iff_le.mp (by rw [compl_compl]; exact y.2)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

/-- In a finite Boolean algebra, the cardinality factors as
    $|\alpha| = |[\bot, a]| \cdot |[a, \top]|$. -/
lemma card_eq_Iic_mul_Ici {α : Type*} [BooleanAlgebra α] [Fintype α] (a : α) :
    Fintype.card α = Fintype.card (Set.Iic a) * Fintype.card (Set.Ici a) := by
  conv_rhs => rw [Fintype.card_congr (iciEquivIicCompl a)]
  rw [← Fintype.card_prod]
  exact Fintype.card_congr (boolAlgDecomp a)

/-- Equivalence between subgraphs of a simple graph $a$ on $V$ and Boolean functions on its
    edge set: a subgraph corresponds to the indicator on whether each edge is kept. -/
noncomputable def iicEquivBoolFn {V : Type*} [Fintype V] [DecidableEq V]
    (a : SimpleGraph V) : Set.Iic a ≃ (↥(a.edgeFinset) → Bool) where
  toFun G e := decide ((e : Sym2 V) ∈ (G : SimpleGraph V).edgeSet)
  invFun f := ⟨SimpleGraph.fromEdgeSet
    {e : Sym2 V | ∃ h : e ∈ a.edgeFinset, f ⟨e, h⟩ = true}, by
    simp only [Set.mem_Iic, ← SimpleGraph.edgeSet_subset_edgeSet,
      SimpleGraph.edgeSet_fromEdgeSet]
    intro e he
    simp only [Set.mem_diff, Set.mem_setOf_eq] at he
    exact SimpleGraph.mem_edgeFinset.mp he.1.choose⟩
  left_inv G := by
    ext v w
    change (SimpleGraph.fromEdgeSet _).Adj v w ↔ (G : SimpleGraph V).Adj v w
    rw [SimpleGraph.fromEdgeSet_adj]
    constructor
    · intro ⟨hset, _⟩
      simp only [Set.mem_setOf_eq] at hset
      obtain ⟨_, hf⟩ := hset
      rw [decide_eq_true_iff, SimpleGraph.mem_edgeSet] at hf; exact hf
    · intro hadj
      refine ⟨?_, (G : SimpleGraph V).ne_of_adj hadj⟩
      simp only [Set.mem_setOf_eq]
      exact ⟨SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_subset_edgeSet.mpr G.2 hadj),
             by rw [decide_eq_true_iff, SimpleGraph.mem_edgeSet]; exact hadj⟩
  right_inv f := by
    funext ⟨e, he⟩
    simp only [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_setOf_eq]
    have hnd : e ∉ Sym2.diagSet :=
      a.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)
    simp only [hnd, not_false_eq_true, and_true]
    simp only [show (∃ h : e ∈ a.edgeFinset, f ⟨e, h⟩ = true) ↔ f ⟨e, he⟩ = true from
      ⟨fun ⟨_, hf⟩ => by convert hf, fun hf => ⟨he, hf⟩⟩]
    simp

/-- The number of subgraphs of a simple graph $a$ equals $2^{|E(a)|}$, the number
    of subsets of its edge set. -/
lemma card_Iic_eq_pow_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (a : SimpleGraph V) : Fintype.card (Set.Iic a) = 2 ^ a.edgeFinset.card := by
  rw [Fintype.card_congr (iicEquivBoolFn a)]
  simp [Fintype.card_bool]

set_option maxHeartbeats 600000 in
/-- Markov's (first moment) inequality for the clique number in $G(n, 1/2)$:
    $\Pr[\omega(G) \ge k] \le \mathbb{E}[X_k] = \binom{n}{k} 2^{-\binom{k}{2}}$,
    where $X_k$ counts the $k$-cliques. -/
theorem markov_bound (n k : ℕ) : probCliqueGe n k ≤ expectedKCliques n k := by
  unfold probCliqueGe
  rw [expectedKCliques_eq_div]
  have htotal_pos : (0 : ℝ) < (Fintype.card (SimpleGraph (Fin n)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (k.choose 2) := by positivity
  rw [div_le_div_iff₀ htotal_pos h2pow_pos]
  suffices hnat : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ¬G.CliqueFree k)).card *
      2 ^ (k.choose 2) ≤ n.choose k * Fintype.card (SimpleGraph (Fin n)) by
    exact_mod_cast hnat
  let completeOn (s : Finset (Fin n)) : SimpleGraph (Fin n) :=
    ⟨fun u v => u ∈ s ∧ v ∈ s ∧ u ≠ v,
     fun _ _ ⟨hu, hv, huv⟩ => ⟨hv, hu, huv.symm⟩, ⟨fun _ h => h.2.2 rfl⟩⟩
  have hunion : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ¬G.CliqueFree k)).card ≤
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (Finset.univ.filter (fun G : SimpleGraph (Fin n) => completeOn s ≤ G)).card := by
    apply le_trans (Finset.card_le_card _) Finset.card_biUnion_le
    intro G hG
    rw [Finset.mem_filter] at hG
    rw [Finset.mem_biUnion]
    have hncf := hG.2
    rw [SimpleGraph.CliqueFree] at hncf
    push Not at hncf
    obtain ⟨s, hs⟩ := hncf
    refine ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hs.card_eq⟩, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun u v ⟨hu, hv, huv⟩ => hs.isClique hu hv huv⟩
  have hIci_bound : ∀ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (Finset.univ.filter (fun G : SimpleGraph (Fin n) => completeOn s ≤ G)).card *
        2 ^ (k.choose 2) ≤ Fintype.card (SimpleGraph (Fin n)) := by
    intro s hs
    have hscard : s.card = k := (Finset.mem_powersetCard.mp hs).2
    have hfilt_eq : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => completeOn s ≤ G)).card =
        Fintype.card (Set.Ici (completeOn s)) := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (by
        intro G; simp [Finset.mem_filter, Set.mem_Ici]))
    rw [hfilt_eq]
    have hdecomp := card_eq_Iic_mul_Ici (completeOn s)
    have hIic := card_Iic_eq_pow_edgeFinset (completeOn s)
    calc Fintype.card (Set.Ici (completeOn s)) * 2 ^ k.choose 2
        ≤ Fintype.card (Set.Ici (completeOn s)) * Fintype.card (Set.Iic (completeOn s)) := by
          apply Nat.mul_le_mul_left
          rw [hIic]
          apply Nat.pow_le_pow_right (by norm_num)
          rw [← hscard]
          have : s.card.choose 2 ≤ Fintype.card ↑(completeOn s).edgeSet := by
            rw [show s.card.choose 2 = Fintype.card {e : Sym2 ↥s // ¬e.IsDiag} from by
              rw [Sym2.card_subtype_not_diag, Fintype.card_coe]]
            exact Fintype.card_le_of_injective
              (fun (e : {e : Sym2 ↥s // ¬e.IsDiag}) =>
                (⟨Sym2.map (Subtype.val) e.1, by
                  have hnd := e.2
                  revert hnd
                  refine Sym2.ind (fun a b hnd => ?_) e.1
                  simp only [Sym2.map_mk, SimpleGraph.mem_edgeSet, completeOn]
                  exact ⟨a.2, b.2, fun h => hnd (Sym2.mk_isDiag_iff.mpr (Subtype.ext h))⟩
                ⟩ : ↑(completeOn s).edgeSet))
              (fun ⟨e1, he1⟩ ⟨e2, he2⟩ heq => by
                simp only [Subtype.mk.injEq] at heq
                exact Subtype.ext (Sym2.map.injective Subtype.val_injective heq))
          exact le_trans this (by convert (SimpleGraph.edgeFinset_card (G := completeOn s)).symm.le)
      _ = Fintype.card (SimpleGraph (Fin n)) := by linarith [hdecomp]
  calc (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ¬G.CliqueFree k)).card *
        2 ^ k.choose 2
      ≤ (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          (Finset.univ.filter (fun G : SimpleGraph (Fin n) => completeOn s ≤ G)).card) *
        2 ^ k.choose 2 := Nat.mul_le_mul_right _ hunion
    _ = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => completeOn s ≤ G)).card *
            2 ^ k.choose 2) := by rw [Finset.sum_mul]
    _ ≤ ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          Fintype.card (SimpleGraph (Fin n)) :=
        Finset.sum_le_sum hIci_bound
    _ = ((Finset.univ : Finset (Fin n)).powersetCard k).card *
          Fintype.card (SimpleGraph (Fin n)) := by rw [Finset.sum_const, smul_eq_mul]
    _ = n.choose k * Fintype.card (SimpleGraph (Fin n)) := by
        congr 1; rw [Finset.card_powersetCard]; simp [Fintype.card_fin]

/-- First moment direction of the two-point concentration (cf. Theorem 4.4.3):
    if the expected number of $k(n)$-cliques tends to $0$, then with high probability
    $G(n, 1/2)$ has no clique of size $k(n)$. -/
theorem clique_number_first_moment_bound
    (k : ℕ → ℕ)
    (hf : Tendsto (fun n => expectedKCliques n (k n)) atTop (𝓝 0)) :
    Tendsto (fun n => probCliqueGe n (k n)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf
    (fun n => probCliqueGe_nonneg n (k n)) (fun n => markov_bound n (k n))



end CliqueNumber
