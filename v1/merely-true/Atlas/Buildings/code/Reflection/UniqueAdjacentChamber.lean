/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Reflection.HyperplaneChambers
import Atlas.Buildings.code.Reflection.WallSeparation

set_option maxHeartbeats 0

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- *Hyperplane carriers are closed*: the carrier $\{x : \langle n, x\rangle = d\}$ of an
affine hyperplane is the preimage of a singleton under a continuous map, hence closed. -/
theorem hyperplane_carrier_isClosed' (η : AffineHyperplane E) :
    IsClosed η.carrier := by
  simp only [AffineHyperplane.carrier]
  exact isClosed_eq (Continuous.inner continuous_const continuous_id) continuous_const

/-- *Hyperplane carriers have empty interior*: if $η.carrier$ contained an open ball around
some $x$, then moving $x$ slightly in the direction $η.normal$ would change the inner product
$\langle η.normal, \cdot\rangle$ but stay inside the carrier — a contradiction. -/
theorem hyperplane_carrier_interior_empty' (η : AffineHyperplane E) :
    interior η.carrier = ∅ := by
  by_contra h_ne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h_ne
  rw [mem_interior] at hx
  obtain ⟨U, hU_sub, hU_open, hx_mem⟩ := hx
  have hn_norm_pos : 0 < ‖η.normal‖ := norm_pos_iff.mpr η.normal_ne_zero
  rw [Metric.isOpen_iff] at hU_open
  obtain ⟨ε, hε_pos, hball⟩ := hU_open x hx_mem
  set t := ε / (2 * ‖η.normal‖)
  have ht_pos : 0 < t := div_pos hε_pos (mul_pos two_pos hn_norm_pos)
  have h_in_ball : x + t • η.normal ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
    calc t * ‖η.normal‖ = ε / (2 * ‖η.normal‖) * ‖η.normal‖ := rfl
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  have h_on_hyp : ⟪η.normal, x + t • η.normal⟫_ℝ = η.offset := by
    have := hU_sub (hball h_in_ball)
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at this
    exact this
  have h_base : ⟪η.normal, x⟫_ℝ = η.offset := by
    have := hU_sub (hball (Metric.mem_ball_self hε_pos))
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at this
    exact this
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, h_base] at h_on_hyp
  linarith [mul_pos ht_pos (pow_pos hn_norm_pos 2)]

/-- *Baire-style fact*: a finite union of closed nowhere-dense sets has empty interior. Proof
by induction: peel off one closed set `new`; if some open subset $U$ of the union meets the
complement of `new`, $U \setminus \text{new}$ is open inside the remaining union and lies in
its interior (which is empty by IH); otherwise $U \subseteq \text{interior}\,\text{new} =
\emptyset$. -/
theorem finite_iUnion_empty_interior' {X : Type*} [TopologicalSpace X]
    (S : Finset (Set X)) (hclosed : ∀ s ∈ S, IsClosed s) (hint : ∀ s ∈ S, interior s = ∅) :
    interior (⋃ s ∈ S, s) = ∅ := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons new rest h_not_in ih =>
    have hc_rest : ∀ s ∈ rest, IsClosed s :=
      fun s hs => hclosed s (Finset.mem_cons.mpr (Or.inr hs))
    have hi_rest : ∀ s ∈ rest, interior s = ∅ :=
      fun s hs => hint s (Finset.mem_cons.mpr (Or.inr hs))
    have ih_result := ih hc_rest hi_rest
    have hc_new : IsClosed new := hclosed new (Finset.mem_cons_self _ _)
    have hi_new : interior new = ∅ := hint new (Finset.mem_cons_self _ _)
    have h_eq : (⋃ s ∈ (Finset.cons new rest h_not_in), s) = new ∪ ⋃ s ∈ rest, s := by
      ext x; simp only [Finset.mem_cons, Set.mem_iUnion, Set.mem_union, exists_prop]
      exact ⟨fun ⟨s, hs, hx⟩ => hs.elim (fun h => h ▸ Or.inl hx) (fun h => Or.inr ⟨s, h, hx⟩),
             fun h => h.elim (fun hx => ⟨new, Or.inl rfl, hx⟩)
               (fun ⟨s, hs, hx⟩ => ⟨s, Or.inr hs, hx⟩)⟩
    rw [h_eq]
    by_contra h_ne
    have h_nonempty : (interior (new ∪ ⋃ s ∈ rest, s)).Nonempty := by
      rwa [Set.nonempty_iff_ne_empty]
    obtain ⟨x, hx⟩ := h_nonempty
    rw [mem_interior] at hx
    obtain ⟨U, hU_sub, hU_open, hx_mem⟩ := hx
    have hU_diff_open : IsOpen (U \ new) := hU_open.sdiff hc_new
    by_cases h_diff_ne : (U \ new).Nonempty
    · have hU_diff_sub : U \ new ⊆ ⋃ s ∈ rest, s := by
        intro y hy; exact (hU_sub hy.1).resolve_left hy.2
      have hsub : U \ new ⊆ interior (⋃ s ∈ rest, s) :=
        interior_maximal hU_diff_sub hU_diff_open
      rw [ih_result] at hsub
      exact h_diff_ne.ne_empty (Set.subset_eq_empty hsub rfl)
    · rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h_diff_ne
      have hsub : U ⊆ interior new := interior_maximal h_diff_ne hU_open
      rw [hi_new] at hsub
      exact Set.Nonempty.ne_empty ⟨x, hx_mem⟩ (Set.subset_eq_empty hsub rfl)

/-- *Affine hyperplanes have empty interior* (raw-data form): the affine hyperplane
$\{x : \langle n, x\rangle = d\}$ for nonzero $n$ has empty interior. Equivalently its
complement is dense; the proof shows any open set $U$ meets the complement by perturbing in
the direction $n$. -/
lemma interior_hyperplane_eq_empty (n : E) (d : ℝ) (hn : n ≠ 0) :
    interior {x : E | ⟪n, x⟫_ℝ = d} = ∅ := by
  rw [interior_eq_empty_iff_dense_compl, dense_iff_inter_open]
  intro U hU ⟨x, hx⟩
  by_cases hxn : ⟪n, x⟫_ℝ ≠ d
  · exact ⟨x, hx, hxn⟩
  · push Not at hxn
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
    have hn_pos : (0 : ℝ) < ‖n‖ := norm_pos_iff.mpr hn
    have ht_pos : (0 : ℝ) < ε / (2 * ‖n‖) := div_pos hε (mul_pos two_pos hn_pos)
    refine ⟨x + (ε / (2 * ‖n‖)) • n, hball (Metric.mem_ball.mpr ?_), ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht_pos.le]
      calc ε / (2 * ‖n‖) * ‖n‖ = ε / 2 := by field_simp
        _ < ε := half_lt_self hε
    · simp only [mem_compl_iff, mem_setOf_eq, inner_add_right, inner_smul_right, hxn]
      intro h
      have h1 : ε / (2 * ‖n‖) * ⟪n, n⟫_ℝ = 0 := by linarith
      have h2 : (0 : ℝ) < ⟪n, n⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]; exact sq_pos_of_pos hn_pos
      linarith [mul_pos ht_pos h2]

/-- *The complement of an affine hyperplane is dense*: equivalent reformulation of
`interior_hyperplane_eq_empty` via the standard duality $\text{interior}\,A = \emptyset
\iff A^c$ dense. -/
lemma dense_compl_hyperplane (n : E) (d : ℝ) (hn : n ≠ 0) :
    Dense ({x : E | ⟪n, x⟫_ℝ = d}ᶜ) :=
  interior_eq_empty_iff_dense_compl.mp (interior_hyperplane_eq_empty n d hn)

/-- *A connected set disjoint from a hyperplane lies in one open half-space*: a connected
$C$ avoiding $\{\langle n, x\rangle = d\}$ is contained in $\{> d\}$ or $\{< d\}$. The two
half-spaces are disjoint open sets covering $C$; preconnectedness forces $C$ into one. -/
lemma connected_subset_halfspace {C : Set E} {n : E} {d : ℝ}
    (hC : IsConnected C) (hC_disj : Disjoint C {x | ⟪n, x⟫_ℝ = d}) :
    C ⊆ {x | ⟪n, x⟫_ℝ > d} ∨ C ⊆ {x | ⟪n, x⟫_ℝ < d} := by
  have hC_sub : C ⊆ {x | ⟪n, x⟫_ℝ > d} ∪ {x | ⟪n, x⟫_ℝ < d} := by
    intro x hx
    have hne : ⟪n, x⟫_ℝ ≠ d := fun heq => (Set.disjoint_left.mp hC_disj hx) heq
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr h
    · exact Or.inl h
  have h_pos_open : IsOpen {x : E | ⟪n, x⟫_ℝ > d} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have h_neg_open : IsOpen {x : E | ⟪n, x⟫_ℝ < d} :=
    isOpen_lt (continuous_const.inner continuous_id) continuous_const
  have h_disj : Disjoint {x : E | ⟪n, x⟫_ℝ > d} {x | ⟪n, x⟫_ℝ < d} := by
    rw [Set.disjoint_iff]; intro x ⟨hx1, hx2⟩; simp only [mem_setOf_eq] at *; linarith
  by_cases hpos : (C ∩ {x | ⟪n, x⟫_ℝ > d}).Nonempty
  · left
    exact hC.isPreconnected.subset_left_of_subset_union h_pos_open h_neg_open h_disj hC_sub hpos
  · right
    rw [not_nonempty_iff_eq_empty] at hpos
    have hneg : (C ∩ {x | ⟪n, x⟫_ℝ < d}).Nonempty := by
      obtain ⟨x, hx⟩ := hC.nonempty
      rcases hC_sub hx with h | h
      · exfalso
        have : x ∈ C ∩ {x | ⟪n, x⟫_ℝ > d} := ⟨hx, h⟩
        rw [hpos] at this; exact this
      · exact ⟨x, hx, h⟩
    exact hC.isPreconnected.subset_left_of_subset_union h_neg_open h_pos_open h_disj.symm
      (fun x hx => by rcases hC_sub hx with h | h; exact Or.inr h; exact Or.inl h) hneg

/-- *Every point of the complement lies in some chamber*: given $p \in arr.complement$ (i.e.
on no hyperplane), there exists a chamber $C$ containing $p$. The proof uses Zorn's lemma on
the family of connected subsets of the complement containing $p$, with the union of a chain
serving as an upper bound via `IsPreconnected.sUnion_directed`. -/
lemma chamber_of_mem_complement (arr : HyperplaneArrangement E) (p : E)
    (hp : p ∈ arr.complement) : ∃ C : arr.Chamber, p ∈ C.set := by
  let S : Set (Set E) := {T | p ∈ T ∧ T ⊆ arr.complement ∧ IsConnected T}
  have hp_singleton : {p} ∈ S :=
    ⟨mem_singleton p,
     fun x hx => by rw [mem_singleton_iff.mp hx]; exact hp,
     isConnected_singleton⟩
  have chain_bound : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hchain hc_ne
    refine ⟨⋃₀ c, ?_, fun s hs => subset_sUnion_of_mem hs⟩
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨s, hs⟩ := hc_ne
      exact mem_sUnion.mpr ⟨s, hs, (hcS hs).1⟩
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := mem_sUnion.mp hx
      exact (hcS hs).2.1 hxs
    · exact ⟨⟨p, by obtain ⟨s, hs⟩ := hc_ne; exact mem_sUnion.mpr ⟨s, hs, (hcS hs).1⟩⟩,
        IsPreconnected.sUnion_directed
          (fun s hs t ht => by
            rcases hchain.total hs ht with h | h
            · exact ⟨t, ht, h, Subset.rfl⟩
            · exact ⟨s, hs, Subset.rfl, h⟩)
          (fun s hs => (hcS hs).2.2.isPreconnected)⟩
  obtain ⟨M, hpM, hM_max⟩ := zorn_subset_nonempty S chain_bound {p} hp_singleton
  have hpM' : p ∈ M := hpM (mem_singleton p)
  obtain ⟨⟨_, hM_compl, hM_conn⟩, hM_max'⟩ := hM_max
  exact ⟨⟨M, hM_compl, hM_conn, fun T hT_sub hT_conn hMT =>
    hM_max' ⟨hMT hpM', hT_sub, hT_conn⟩ hMT⟩, hpM'⟩

/-- *Avoidance lemma for a finite list of affine hyperplanes*: given an open nonempty $V$ and
a list of affine hyperplane data $(n_i, d_i)$ with $n_i \ne 0$, there exists $x \in V$ avoiding
every hyperplane $\langle n_i, x\rangle = d_i$. Proof by induction on the list: at each step,
intersect $V$ with the dense open complement of the next hyperplane and recurse. -/
theorem avoidance_list :
    ∀ (hyps : List (E × ℝ)) (V : Set E), IsOpen V → V.Nonempty →
    (∀ p ∈ hyps, (p : E × ℝ).1 ≠ 0) →
    ∃ x ∈ V, ∀ p ∈ hyps, ⟪(p : E × ℝ).1, x⟫_ℝ ≠ p.2 := by
  intro hyps
  induction hyps with
  | nil =>
    intro V _ hVne _
    obtain ⟨x, hx⟩ := hVne
    exact ⟨x, hx, fun _ hp => absurd hp List.not_mem_nil⟩
  | cons hd tl ih =>
    intro V hV_open hV_ne h_ne
    have hhd_ne : hd.1 ≠ 0 := h_ne hd List.mem_cons_self
    have htl_ne : ∀ p ∈ tl, (p : E × ℝ).1 ≠ 0 :=
      fun p hp => h_ne p (List.mem_cons_of_mem hd hp)
    set cs := {x : E | ⟪hd.1, x⟫_ℝ = hd.2}
    have hdense : Dense csᶜ :=
      dense_compl_hyperplane hd.1 hd.2 hhd_ne
    have hW_open : IsOpen (V ∩ csᶜ) := hV_open.inter
      ((isClosed_eq (continuous_const.inner continuous_id) continuous_const).isOpen_compl)
    obtain ⟨x, hxW, hx_avoid⟩ := ih (V ∩ csᶜ) hW_open
      (hdense.inter_open_nonempty V hV_open hV_ne) htl_ne
    exact ⟨x, hxW.1, fun p hp => by
      rcases List.mem_cons.mp hp with rfl | h
      · exact hxW.2
      · exact hx_avoid p h⟩





