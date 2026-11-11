/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Atlas.Buildings.code.BNPair.ParabolicDefs
import Atlas.Buildings.code.BNPair.CellCoverProof
import Atlas.Buildings.code.BNPair.CellDisjointProof
import Atlas.Buildings.code.BNPair.CellMulParabolicProof
import Atlas.Buildings.code.BNPair.CellInvProof
import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

namespace SubgroupOverB

open BNPair CellCover CellDisjoint

/-- If $B \leq P$ and some $g \in BwB$ lies in $P$, then the whole Bruhat cell $BwB$ is
contained in $P$. Proof: factor $g$ in $BnB$ form, deduce $n \in P$, then any other lift
$n'$ of $w$ differs from $n$ by a $T \subseteq B \subseteq P$ element. -/
lemma cell_sub_of_mem (bp : BNPair G M) (P : Subgroup G) (hBP : bp.B ≤ P)
    (w : M.Group) (g : G) (hgP : g ∈ (P : Set G)) (hgW : g ∈ bp.bruhatCell w) :
    bp.bruhatCell w ⊆ (P : Set G) := by
  intro h hh
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hgW
  obtain ⟨⟨b₁', hb₁'⟩, n', ⟨b₂', hb₂'⟩, hπ', hh_eq⟩ := hh

  have hn_P : (n : G) ∈ (P : Set G) := by
    have : (n : G) = (b₁ : G)⁻¹ * g * (b₂ : G)⁻¹ := by rw [hg_eq]; group
    rw [this]
    exact P.mul_mem (P.mul_mem (P.inv_mem (hBP hb₁)) hgP) (P.inv_mem (hBP hb₂))

  have hπ_diff : bp.π (n' * n⁻¹) = 1 := by
    rw [map_mul, map_inv, hπ', hπ, mul_inv_cancel]
  have hdiff_in_T : ((n' * n⁻¹ : bp.N) : G) ∈ bp.T := (bp.π_ker _).mp hπ_diff
  have hdiff_in_B : ((n' * n⁻¹ : bp.N) : G) ∈ bp.B := by
    rw [bp.T_eq] at hdiff_in_T; exact (Subgroup.mem_inf.mp hdiff_in_T).1

  have hn'_P : (n' : G) ∈ (P : Set G) := by
    have : (n' : G) = ((n' * n⁻¹ : bp.N) : G) * (n : G) := by
      simp [Subgroup.coe_mul]
    rw [this]
    exact P.mul_mem (hBP hdiff_in_B) hn_P

  rw [hh_eq]
  exact P.mul_mem (P.mul_mem (hBP hb₁') hn'_P) (hBP hb₂')

/-- If every simple cell $BsB$ for $s \in S'$ is contained in $P$, and $B \leq P$, then
every $N$-lift $n$ of any $w \in W_{S'}$ lies in $P$. Proof by induction on a reduced
expression of $w$ in the simple reflections of $S'$. -/
lemma N_rep_mem_P_of_parabolicW (bp : BNPair G M) (P : Subgroup G) (hBP : bp.B ≤ P)
    (S' : Set B_idx) (hS' : ∀ s ∈ S', bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆ (P : Set G))
    (w : M.Group) (hw : w ∈ bp.parabolicSubgroupW S')
    (n : bp.N) (hn : bp.π n = w) : (n : G) ∈ (P : Set G) := by
  let cs := M.toCoxeterSystem
  unfold parabolicSubgroupW at hw


  revert n
  revert w
  suffices ∀ (w : M.Group), w ∈ Subgroup.closure (cs.simple '' S') →
      ∀ (n : bp.N), bp.π n = w → (n : G) ∈ (P : Set G) by
    intro w hw; exact this w hw
  intro w' hw'
  refine Subgroup.closure_induction_right
    (p := fun (w₀ : M.Group) _ => ∀ (n : bp.N), bp.π n = w₀ → (n : G) ∈ (P : Set G))
    ?one ?mul_right ?mul_inv hw'
  ·
    intro n hn_eq
    have n_in_T : (n : G) ∈ bp.T := (bp.π_ker n).mp hn_eq
    have n_in_B : (n : G) ∈ bp.B := by
      rw [bp.T_eq] at n_in_T; exact (Subgroup.mem_inf.mp n_in_T).1
    exact hBP n_in_B
  ·
    intro w₀ _hw₀ si hsi IH n hn_eq
    obtain ⟨i, hi, rfl⟩ := hsi

    obtain ⟨n_w₀, hn_w₀⟩ := bp.π_surj w₀
    obtain ⟨n_i, hn_i⟩ := bp.π_surj (cs.simple i)
    have hπ_prod : bp.π (n_w₀ * n_i) = w₀ * cs.simple i := by
      rw [map_mul, hn_w₀, hn_i]
    have hπ_diff : bp.π (n * (n_w₀ * n_i)⁻¹) = 1 := by
      rw [map_mul, map_inv, hn_eq, hπ_prod, mul_inv_cancel]
    have t_in_T : ((n * (n_w₀ * n_i)⁻¹ : bp.N) : G) ∈ bp.T := (bp.π_ker _).mp hπ_diff
    have t_in_B : ((n * (n_w₀ * n_i)⁻¹ : bp.N) : G) ∈ bp.B := by
      rw [bp.T_eq] at t_in_T; exact (Subgroup.mem_inf.mp t_in_T).1
    have hn_eq' : (n : G) = ((n * (n_w₀ * n_i)⁻¹ : bp.N) : G) * (n_w₀ : G) * (n_i : G) := by
      simp [Subgroup.coe_mul]; group
    rw [hn_eq']
    exact P.mul_mem (P.mul_mem (hBP t_in_B) (IH n_w₀ hn_w₀))
      (hS' i hi ⟨⟨1, bp.B.one_mem⟩, n_i, ⟨1, bp.B.one_mem⟩, hn_i, by simp⟩)
  ·
    intro w₀ _hw₀ si hsi IH n hn_eq
    obtain ⟨i, hi, rfl⟩ := hsi
    have simple_inv : (cs.simple i)⁻¹ = cs.simple i :=
      CellDisjoint.simple_inv_eq cs i

    obtain ⟨n_w₀, hn_w₀⟩ := bp.π_surj w₀
    obtain ⟨n_i, hn_i⟩ := bp.π_surj (cs.simple i)
    have hπ_prod : bp.π (n_w₀ * n_i) = w₀ * cs.simple i := by
      rw [map_mul, hn_w₀, hn_i]

    have hn_eq' : bp.π n = w₀ * cs.simple i := by rw [hn_eq, simple_inv]
    have hπ_diff : bp.π (n * (n_w₀ * n_i)⁻¹) = 1 := by
      rw [map_mul, map_inv, hn_eq', hπ_prod, mul_inv_cancel]
    have t_in_T : ((n * (n_w₀ * n_i)⁻¹ : bp.N) : G) ∈ bp.T := (bp.π_ker _).mp hπ_diff
    have t_in_B : ((n * (n_w₀ * n_i)⁻¹ : bp.N) : G) ∈ bp.B := by
      rw [bp.T_eq] at t_in_T; exact (Subgroup.mem_inf.mp t_in_T).1
    have hn_decomp : (n : G) = ((n * (n_w₀ * n_i)⁻¹ : bp.N) : G) * (n_w₀ : G) * (n_i : G) := by
      simp [Subgroup.coe_mul]; group
    rw [hn_decomp]
    exact P.mul_mem (P.mul_mem (hBP t_in_B) (IH n_w₀ hn_w₀))
      (hS' i hi ⟨⟨1, bp.B.one_mem⟩, n_i, ⟨1, bp.B.one_mem⟩, hn_i, by simp⟩)

/-- $P_{S'} \subseteq P$ whenever $B \leq P$ and every simple cell $BsB$ for $s \in S'$
is in $P$: combine `N_rep_mem_P_of_parabolicW` with the $BwB$ factorization. -/
lemma standardParabolic_sub (bp : BNPair G M) (P : Subgroup G) (hBP : bp.B ≤ P)
    (S' : Set B_idx) (hS' : ∀ s ∈ S', bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆ (P : Set G)) :
    bp.standardParabolic S' ⊆ (P : Set G) := by
  intro g hg
  rw [standardParabolic, Set.mem_iUnion₂] at hg
  obtain ⟨w, hw, hgw⟩ := hg
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hgw
  rw [hg_eq]
  exact P.mul_mem (P.mul_mem (hBP hb₁) (N_rep_mem_P_of_parabolicW bp P hBP S' hS' w hw n hπ))
    (hBP hb₂)

/-- **Concrete consequence of axiom BN3:** for each simple reflection $s$ there exist
$x, y \in BsB$ with $x^{-1} y \in BsB$. Uses the BN-pair axiom that some $b_0 \in B$ has
$n_s b_0 n_s^{-1} \notin B$, hence the product $(n_s)^{-1} (b_0 n_s^{-1})$ produces an
element living in $BsB$ rather than collapsing to $B$. -/
lemma bn3_gives_element_in_BsB (bp : BNPair G M) (ax : BNPairAxioms bp)
    (s : B_idx) (n_s : bp.N) (hn_s : bp.π n_s = M.toCoxeterSystem.simple s) :
    ∃ x : G, x ∈ bp.bruhatCell (M.toCoxeterSystem.simple s) ∧
    ∃ y : G, y ∈ bp.bruhatCell (M.toCoxeterSystem.simple s) ∧
    x⁻¹ * y ∈ bp.bruhatCell (M.toCoxeterSystem.simple s) := by
  let cs := M.toCoxeterSystem

  obtain ⟨b₀, hb₀_not_B⟩ := ax.conjugate_not_sub s n_s hn_s

  have hns_cell : (n_s : G) ∈ bp.bruhatCell (cs.simple s) :=
    ⟨⟨1, bp.B.one_mem⟩, n_s, ⟨1, bp.B.one_mem⟩, hn_s, by simp⟩
  have hns_inv_cell : (n_s : G)⁻¹ ∈ bp.bruhatCell (cs.simple s) :=
    CellDisjoint.inv_mem_bruhatCell_simple bp hns_cell

  have hnsb₀ : (n_s : G) * (b₀ : G) ∈ bp.bruhatCell (cs.simple s) :=
    ⟨⟨1, bp.B.one_mem⟩, n_s, ⟨(b₀ : G), b₀.prop⟩, hn_s, by simp⟩

  have hy_cell : (b₀ : G) * (n_s : G)⁻¹ ∈ bp.bruhatCell (cs.simple s) :=
    CellMulParabolic.bruhatCell_mul_B_left bp b₀.prop hns_inv_cell


  have hprod_eq : ((n_s : G)⁻¹)⁻¹ * ((b₀ : G) * (n_s : G)⁻¹) =
      (n_s : G) * (b₀ : G) * (n_s : G)⁻¹ := by group

  have hconj_in_prod : (n_s : G) * (b₀ : G) * (n_s : G)⁻¹ ∈
      setMul (bp.bruhatCell (cs.simple s)) (bp.bruhatCell (cs.simple s)) :=
    ⟨(n_s : G) * (b₀ : G), hnsb₀, (n_s : G)⁻¹, hns_inv_cell, by group⟩

  have hlen_ss : cs.length (cs.simple s * cs.simple s) < cs.length (cs.simple s) := by
    rw [cs.simple_mul_simple_self s, cs.length_one, cs.length_simple]; omega
  have hprod_sub := ax.cell_mul_length_decreasing (cs.simple s) s hlen_ss
  have hconj_in_union := hprod_sub hconj_in_prod
  rw [cs.simple_mul_simple_self] at hconj_in_union
  rcases hconj_in_union with hconj_B1B | hconj_BsB
  ·
    exfalso
    exact hb₀_not_B (CellDisjoint.bruhatCell_one_sub_B' bp hconj_B1B)
  ·
    exact ⟨(n_s : G)⁻¹, hns_inv_cell, (b₀ : G) * (n_s : G)⁻¹, hy_cell,
      hprod_eq ▸ hconj_BsB⟩

/-- **Reverse direction of the classification of subgroups over $B$.** If $BwB \subseteq P$
(with $B \leq P$), then $w \in W_{S'}$ where $S' = \{s : BsB \subseteq P\}$. Proof by strong
induction on $\ell(w)$: pick a right descent $s$, observe that $BsB \subseteq P$ via
`bn3_gives_element_in_BsB` and `cell_sub_of_mem`, then deduce $B(ws)B \subseteq P$ and
apply the induction hypothesis to $ws$. -/
lemma w_mem_parabolicW_of_cell_sub (bp : BNPair G M) (ax : BNPairAxioms bp)
    (P : Subgroup G) (hBP : bp.B ≤ P) (S' : Set B_idx)
    (hS'_def : S' = { s : B_idx | bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆ (P : Set G) })
    (w : M.Group) (hw : bp.bruhatCell w ⊆ (P : Set G)) :
    w ∈ bp.parabolicSubgroupW S' := by
  let cs := M.toCoxeterSystem

  suffices ∀ (k : ℕ) (w : M.Group), cs.length w = k →
      bp.bruhatCell w ⊆ (P : Set G) → w ∈ bp.parabolicSubgroupW S' from
    this (cs.length w) w rfl hw
  intro k
  induction k using Nat.strongRecOn with
  | _ k IH =>
  intro w hlen hw_sub
  by_cases hlen0 : k = 0
  ·
    subst hlen0
    have hw1 : w = 1 := cs.length_eq_zero_iff.mp hlen
    rw [hw1]
    exact (bp.parabolicSubgroupW S').one_mem
  ·
    have hne1 : w ≠ 1 := by
      intro heq; rw [heq, cs.length_one] at hlen; exact hlen0 hlen.symm
    obtain ⟨s, hs_descent⟩ := cs.exists_rightDescent_of_ne_one hne1

    have hlen_ws : cs.length (w * cs.simple s) + 1 = cs.length w :=
      cs.isRightDescent_iff.mp hs_descent
    have hlen_ws_lt : cs.length (w * cs.simple s) < cs.length w := by omega

    have hlen_wss : cs.length (w * cs.simple s * cs.simple s) >
        cs.length (w * cs.simple s) := by
      rw [mul_assoc, cs.simple_mul_simple_self, mul_one]; omega

    have cell_ws_s_sub : ∀ a b : G,
        a ∈ bp.bruhatCell (w * cs.simple s) → b ∈ bp.bruhatCell (cs.simple s) →
        a * b ∈ (P : Set G) := by
      intro a b ha hb
      have hab : a * b ∈ setMul (bp.bruhatCell (w * cs.simple s))
          (bp.bruhatCell (cs.simple s)) := ⟨a, ha, b, hb, rfl⟩
      have hab_cell := ax.cell_mul_length_increasing (w * cs.simple s) s hlen_wss hab
      rw [mul_assoc, cs.simple_mul_simple_self, mul_one] at hab_cell
      exact hw_sub hab_cell

    obtain ⟨n_s, hn_s⟩ := bp.π_surj (cs.simple s)
    obtain ⟨x, hx_cell, y, hy_cell, hxy_cell⟩ :=
      bn3_gives_element_in_BsB bp ax s n_s hn_s
    obtain ⟨a₀, ha₀⟩ := exists_mem_bruhatCell bp (w * cs.simple s)

    have ha₀x : a₀ * x ∈ (P : Set G) := cell_ws_s_sub a₀ x ha₀ hx_cell
    have ha₀y : a₀ * y ∈ (P : Set G) := cell_ws_s_sub a₀ y ha₀ hy_cell

    have hxy_P : x⁻¹ * y ∈ (P : Set G) := by
      have : x⁻¹ * y = (a₀ * x)⁻¹ * (a₀ * y) := by group
      rw [this]
      exact P.mul_mem (P.inv_mem ha₀x) ha₀y

    have hBsB_sub_P : bp.bruhatCell (cs.simple s) ⊆ (P : Set G) :=
      cell_sub_of_mem bp P hBP (cs.simple s) (x⁻¹ * y) hxy_P hxy_cell
    have hs_mem_S' : s ∈ S' := by rw [hS'_def]; exact hBsB_sub_P

    have hBwsB_sub_P : bp.bruhatCell (w * cs.simple s) ⊆ (P : Set G) := by
      intro a ha
      obtain ⟨b₀, hb₀⟩ := exists_mem_bruhatCell bp (cs.simple s)
      have hab : a * b₀ ∈ (P : Set G) := cell_ws_s_sub a b₀ ha hb₀
      have hb₀_P : b₀ ∈ (P : Set G) := hBsB_sub_P hb₀
      have : a = (a * b₀) * b₀⁻¹ := by group
      rw [this]
      exact P.mul_mem hab (P.inv_mem hb₀_P)

    have hws_mem : w * cs.simple s ∈ bp.parabolicSubgroupW S' :=
      IH (cs.length (w * cs.simple s)) (by omega) (w * cs.simple s) rfl hBwsB_sub_P

    have hs_simple_mem : cs.simple s ∈ bp.parabolicSubgroupW S' := by
      apply Subgroup.subset_closure
      exact ⟨s, hs_mem_S', rfl⟩
    have hw_eq : w = (w * cs.simple s) * cs.simple s := by
      rw [mul_assoc, cs.simple_mul_simple_self, mul_one]
    rw [hw_eq]
    exact (bp.parabolicSubgroupW S').mul_mem hws_mem hs_simple_mem

/-- **Classification of subgroups containing $B$ (Bourbaki §IV.2.6, Theorem 3).** Every
subgroup $P \leq G$ with $B \leq P$ equals the standard parabolic $P_{S'}$ where
$S' = \{s \in S : BsB \subseteq P\}$. Combines `cell_sub_of_mem`,
`w_mem_parabolicW_of_cell_sub`, and `standardParabolic_sub`. -/
theorem subgroup_over_B_eq_parabolic_from_bnpair
    (bp : BNPair G M) (ax : BNPairAxioms bp) :
    ∀ P : Subgroup G, bp.B ≤ P →
    ∃ S' : Set B_idx, (P : Set G) = bp.standardParabolic S' := by
  intro P hBP
  let S' : Set B_idx := { s : B_idx | bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆ (P : Set G) }
  use S'
  ext g
  constructor
  ·
    intro hgP
    obtain ⟨w, hgw⟩ := CellCover.cell_cover_from_bnpair bp ax g
    have hw_sub : bp.bruhatCell w ⊆ (P : Set G) :=
      cell_sub_of_mem bp P hBP w g hgP hgw
    have hw_mem : w ∈ bp.parabolicSubgroupW S' :=
      w_mem_parabolicW_of_cell_sub bp ax P hBP S' rfl w hw_sub
    exact Set.mem_iUnion₂.mpr ⟨w, hw_mem, hgw⟩
  ·
    intro hg
    exact standardParabolic_sub bp P hBP S' (fun s hs => hs) hg

end SubgroupOverB
