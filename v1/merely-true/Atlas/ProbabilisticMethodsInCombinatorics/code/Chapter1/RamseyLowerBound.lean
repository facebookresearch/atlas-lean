/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
namespace RamseyLowerBound

open Finset Fintype

/-- An edge of the complete graph $K_n$: an unordered, non-diagonal pair of vertices. -/
abbrev Edge (n : ℕ) := {e : Sym2 (Fin n) // ¬e.IsDiag}

/-- The complete graph $K_n$ has $\binom{n}{2}$ edges. -/
lemma card_edge (n : ℕ) : Fintype.card (Edge n) = n.choose 2 := by
  rw [Sym2.card_subtype_not_diag, Fintype.card_fin]

/-- `edgesWithin n S` is the set of edges of $K_n$ whose endpoints both lie in `S`. -/
def edgesWithin (n : ℕ) (S : Finset (Fin n)) : Finset (Edge n) :=
  Finset.univ.filter (fun e => e.val ∈ S.sym2)

/-- The number of off-diagonal unordered pairs from a finite set $S$ is $\binom{|S|}{2}$. -/
lemma card_offDiag_sym2 {α : Type*} [DecidableEq α] (S : Finset α) :
    (S.sym2.filter (fun e => ¬e.IsDiag)).card = S.card.choose 2 := by
  have hdiag : (S.sym2.filter (·.IsDiag)).card = S.card := by
    have heq : S.sym2.filter (·.IsDiag) = S.image Sym2.diag := by
      ext e; simp only [mem_filter, Finset.mem_sym2_iff, mem_image]
      constructor
      · intro ⟨hmem, hdiag⟩
        induction e using Sym2.ind with
        | _ a b => rw [Sym2.mk_isDiag_iff] at hdiag; subst hdiag
                   exact ⟨a, hmem a (Sym2.mem_iff.mpr (Or.inl rfl)), rfl⟩
      · intro ⟨a, ha, he⟩; subst he; constructor
        · intro b hb; change b ∈ s(a, a) at hb
          rw [Sym2.mem_iff] at hb; rcases hb with rfl | rfl <;> exact ha
        · exact Sym2.diag_isDiag a
    rw [heq, card_image_of_injective _ Sym2.diag_injective]
  have h := @Finset.card_filter_add_card_filter_not _ (s := S.sym2) Sym2.IsDiag
    (Sym2.IsDiag.decidablePred _) (fun x => instDecidableNot)
  rw [hdiag, card_sym2] at h
  linarith [show (S.card + 1).choose 2 = S.card + S.card.choose 2 by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]]

/-- The vertex-set $S$ spans exactly $\binom{|S|}{2}$ edges in $K_n$. -/
lemma card_edgesWithin (n : ℕ) (S : Finset (Fin n)) :
    (edgesWithin n S).card = S.card.choose 2 := by
  have h_eq : (edgesWithin n S).map ⟨Subtype.val, Subtype.val_injective⟩ =
      S.sym2.filter (fun e => ¬e.IsDiag) := by
    ext e; simp only [mem_map, mem_filter, mem_univ, true_and,
      Function.Embedding.coeFn_mk, edgesWithin]
    constructor
    · rintro ⟨⟨e', he'⟩, hmem, rfl⟩; exact ⟨hmem, he'⟩
    · intro ⟨hmem, hnotdiag⟩; exact ⟨⟨e, hnotdiag⟩, hmem, rfl⟩
  rw [← card_map ⟨Subtype.val, Subtype.val_injective⟩, h_eq, card_offDiag_sym2]

/-- Equivalence between Boolean labellings of $\alpha$ that are constantly $b$ on $s$
and arbitrary Boolean labellings of the complement $\{x : \alpha \mid x \notin s\}$. -/
noncomputable def constrainedEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : Bool) :
    {f : α → Bool // ∀ x ∈ s, f x = b} ≃ ({x : α // x ∉ s} → Bool) where
  toFun f := fun ⟨x, hx⟩ => f.val x
  invFun g := ⟨fun x => if h : x ∈ s then b else g ⟨x, h⟩,
    by intro x hx; simp [hx]⟩
  left_inv := by
    intro ⟨f, hf⟩; simp only [Subtype.mk.injEq]; ext x
    by_cases h : x ∈ s
    · simp [h, hf x h]
    · simp [h]
  right_inv := by intro g; ext ⟨x, hx⟩; simp [hx]

/-- Counting Boolean labellings constrained to take value $b$ on a set $s$:
there are exactly $2^{|\alpha| - |s|}$ such labellings. -/
lemma card_constrained {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : Bool) :
    Fintype.card {f : α → Bool // ∀ x ∈ s, f x = b} =
    2 ^ (Fintype.card α - s.card) := by
  rw [Fintype.card_congr (constrainedEquiv s b), Fintype.card_fun,
    Fintype.card_bool, Fintype.card_subtype_compl]; simp

/-- The number of 2-colorings of $K_n$ that are constant of value $b$ on the edges
inside $S$ is $2^{\binom{n}{2} - \binom{|S|}{2}}$. -/
lemma card_monoSet (n : ℕ) (S : Finset (Fin n)) (b : Bool) :
    (Finset.univ.filter (fun c : Edge n → Bool =>
      ∀ e ∈ edgesWithin n S, c e = b)).card =
    2 ^ (n.choose 2 - S.card.choose 2) := by
  rw [← Fintype.card_subtype, card_constrained (edgesWithin n S) b,
    card_edge, card_edgesWithin]

/-- Converts the real-valued Erdős–Ramsey hypothesis $\binom{n}{k} 2^{1-\binom{k}{2}} < 1$
into the natural-number inequality $2 \binom{n}{k} < 2^{\binom{k}{2}}$. -/
lemma hyp_to_nat {n k : ℕ}
    (h : (n.choose k : ℝ) * (2 : ℝ) ^ ((1 : ℝ) - (k.choose 2 : ℝ)) < 1) :
    n.choose k * 2 < 2 ^ k.choose 2 := by
  rw [Real.rpow_sub_natCast (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] at h
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ k.choose 2 := by positivity
  have h2 : (↑(n.choose k) : ℝ) * 2 < (2 : ℝ) ^ k.choose 2 := by
    have := h; rw [mul_div_assoc'] at this; rwa [div_lt_one h2pos] at this
  exact_mod_cast h2

/-- From $2\binom{n}{k} < 2^{\binom{k}{2}}$ deduce
$2\binom{n}{k} \cdot 2^{\binom{n}{2} - \binom{k}{2}} < 2^{\binom{n}{2}}$, which expresses
that the expected number of monochromatic $k$-cliques is strictly less than the number
of 2-colorings. -/
lemma bound_step {n k : ℕ} (hkn : k ≤ n)
    (h : n.choose k * 2 < 2 ^ k.choose 2) :
    n.choose k * 2 * 2 ^ (n.choose 2 - k.choose 2) < 2 ^ n.choose 2 := by
  have hck : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
  have hpow_pos : 0 < 2 ^ (n.choose 2 - k.choose 2) :=
    Nat.pos_of_ne_zero (by positivity)
  calc n.choose k * 2 * 2 ^ (n.choose 2 - k.choose 2)
      < 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) :=
        Nat.mul_lt_mul_of_pos_right h hpow_pos
    _ = 2 ^ n.choose 2 := by rw [← pow_add, Nat.add_sub_cancel' hck]

/-- The simple graph on $[n]$ whose edges are those colored `true` by a given 2-coloring
`c` of $K_n$. -/
noncomputable def coloringToGraph {n : ℕ} (c : Edge n → Bool) :
    SimpleGraph (Fin n) where
  Adj v w :=
    if h : v = w then False
    else c ⟨s(v, w), by rw [Sym2.mk_isDiag_iff]; exact h⟩ = true
  symm v w := by
    simp only; split_ifs with h1 h2 h2
    · exact id
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · intro hc; convert hc using 2; congr 1; exact Sym2.eq_swap
  loopless := ⟨fun v h => by simp at h⟩

/-- If $S$ is a clique in `coloringToGraph c`, then every edge inside $S$ is colored
`true` by `c`. -/
lemma clique_implies_all_true {n : ℕ} {c : Edge n → Bool}
    {S : Finset (Fin n)}
    (hclique : (coloringToGraph c).IsClique (S : Set (Fin n))) :
    ∀ e ∈ edgesWithin n S, c e = true := by
  intro ⟨e, hne⟩ he
  simp only [edgesWithin, mem_filter, mem_univ, true_and] at he
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at hne
    have ha : a ∈ S := by
      rw [Finset.mem_sym2_iff] at he
      exact he a (Sym2.mem_iff.mpr (Or.inl rfl))
    have hb : b ∈ S := by
      rw [Finset.mem_sym2_iff] at he
      exact he b (Sym2.mem_iff.mpr (Or.inr rfl))
    have hadj := hclique ha hb hne
    unfold coloringToGraph at hadj; simp [hne] at hadj
    convert hadj using 2

/-- If $S$ is a clique in the complement graph of `coloringToGraph c`, then every edge
inside $S$ is colored `false` by `c`. -/
lemma compl_clique_implies_all_false {n : ℕ} {c : Edge n → Bool}
    {S : Finset (Fin n)}
    (hclique : (coloringToGraph c)ᶜ.IsClique (S : Set (Fin n))) :
    ∀ e ∈ edgesWithin n S, c e = false := by
  intro ⟨e, hne⟩ he
  simp only [edgesWithin, mem_filter, mem_univ, true_and] at he
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at hne
    have ha : a ∈ S := by
      rw [Finset.mem_sym2_iff] at he
      exact he a (Sym2.mem_iff.mpr (Or.inl rfl))
    have hb : b ∈ S := by
      rw [Finset.mem_sym2_iff] at he
      exact he b (Sym2.mem_iff.mpr (Or.inr rfl))
    have hadj := hclique ha hb hne
    simp only [SimpleGraph.compl_adj] at hadj
    unfold coloringToGraph at hadj; simp [hne] at hadj
    convert hadj using 2

/-- (Erdős 1947, Ramsey lower bound) If $\binom{n}{k} \cdot 2^{1 - \binom{k}{2}} < 1$,
then there exists a graph on $n$ vertices with no $k$-clique in $G$ or $G^c$, so
$R(k, k) > n$. -/
theorem erdos_1947_ramsey_lower_bound (n k : ℕ)
    (h : (n.choose k : ℝ) * (2 : ℝ) ^ ((1 : ℝ) - (k.choose 2 : ℝ)) < 1) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  by_cases hkn : k ≤ n
  ·
    have hnat := hyp_to_nat h
    have hbound := bound_step hkn hnat

    let I := (Finset.univ : Finset (Fin n)).powersetCard k ×ˢ
             (Finset.univ : Finset Bool)

    let monoFor : Finset (Fin n) × Bool → Finset (Edge n → Bool) :=
      fun ⟨S, b⟩ => Finset.univ.filter
        (fun c => ∀ e ∈ edgesWithin n S, c e = b)

    let badSet := I.biUnion monoFor

    have hbad_lt : badSet.card < Fintype.card (Edge n → Bool) := by
      calc badSet.card
          ≤ ∑ p ∈ I, (monoFor p).card := Finset.card_biUnion_le
        _ = I.card * 2 ^ (n.choose 2 - k.choose 2) := by
            apply Finset.sum_eq_card_nsmul
            intro ⟨S, b⟩ hmem
            simp only [I, mem_product, mem_powersetCard, mem_univ,
              and_true] at hmem
            show (Finset.univ.filter (fun c : Edge n → Bool =>
              ∀ e ∈ edgesWithin n S, c e = b)).card = _
            rw [card_monoSet, hmem.2]
        _ = n.choose k * 2 * 2 ^ (n.choose 2 - k.choose 2) := by
            simp [I, card_product, card_powersetCard, card_univ,
              Fintype.card_fin]
        _ < 2 ^ n.choose 2 := hbound
        _ = Fintype.card (Edge n → Bool) := by
            rw [Fintype.card_fun, Fintype.card_bool, card_edge]

    have ⟨c, hc⟩ : ∃ c : Edge n → Bool, c ∉ badSet := by
      by_contra hall; push Not at hall
      have : badSet = Finset.univ := by ext x; simp [hall x]
      rw [this, card_univ] at hbad_lt
      exact Nat.lt_irrefl _ hbad_lt

    refine ⟨coloringToGraph c, ?_, ?_⟩
    ·
      intro S hS
      have htrue := clique_implies_all_true hS.isClique
      have hmem_bad : c ∈ badSet := mem_biUnion.mpr
        ⟨(S, true),
         mem_product.mpr ⟨mem_powersetCard.mpr
           ⟨Finset.subset_univ _, hS.card_eq⟩, mem_univ _⟩,
         mem_filter.mpr ⟨mem_univ _, htrue⟩⟩
      exact absurd hmem_bad hc
    ·
      intro S hS
      have hfalse := compl_clique_implies_all_false hS.isClique
      have hmem_bad : c ∈ badSet := mem_biUnion.mpr
        ⟨(S, false),
         mem_product.mpr ⟨mem_powersetCard.mpr
           ⟨Finset.subset_univ _, hS.card_eq⟩, mem_univ _⟩,
         mem_filter.mpr ⟨mem_univ _, hfalse⟩⟩
      exact absurd hmem_bad hc
  ·
    push Not at hkn
    refine ⟨⊥, ?_, ?_⟩ <;> {
      intro s hs
      have h1 : s.card ≤ n := by
        simpa [Fintype.card_fin] using s.card_le_univ
      have h2 := hs.card_eq
      omega
    }

end RamseyLowerBound
