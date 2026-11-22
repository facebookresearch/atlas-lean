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
import Atlas.Buildings.code.BNPair.SubgroupOverBProof
import Atlas.Buildings.code.BNPair.CellDisjointHelpers
import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

namespace NormalizerParabolic

open BNPair CellCover CellDisjoint SubgroupOverB

/-- $B \subseteq P_{S'}$ via the trivial cell $B = B \cdot 1 \cdot B$ in
$P_{S'} = \bigcup_{w \in W_{S'}} BwB$. -/
lemma B_sub_standardParabolic (bp : BNPair G M) (S' : Set B_idx) :
    (bp.B : Set G) ⊆ bp.standardParabolic S' := by
  intro b hb
  rw [standardParabolic, Set.mem_iUnion₂]
  refine ⟨1, (bp.parabolicSubgroupW S').one_mem, ?_⟩
  obtain ⟨n₀, hn₀⟩ := bp.π_surj (1 : M.Group)
  have n₀_in_T : (n₀ : G) ∈ bp.T := (bp.π_ker n₀).mp hn₀
  have n₀_in_B : (n₀ : G) ∈ bp.B := by
    rw [bp.T_eq] at n₀_in_T; exact (Subgroup.mem_inf.mp n₀_in_T).1
  exact ⟨⟨b * (↑n₀)⁻¹, bp.B.mul_mem hb (bp.B.inv_mem n₀_in_B)⟩,
         n₀, ⟨1, bp.B.one_mem⟩, hn₀, by simp⟩

/-- Standard parabolics are closed under multiplication: $P_{S'} \cdot P_{S'} \subseteq P_{S'}$.
Follows from `CellMulParabolic.cell_mul_in_parabolic_from_bnpair`. -/
lemma standardParabolic_mul (bp : BNPair G M) (ax : BNPairAxioms bp)
    (S' : Set B_idx) {x y : G}
    (hx : x ∈ bp.standardParabolic S') (hy : y ∈ bp.standardParabolic S') :
    x * y ∈ bp.standardParabolic S' := by
  rw [standardParabolic, Set.mem_iUnion₂] at hx hy ⊢
  obtain ⟨w₁, hw₁, hxw₁⟩ := hx
  obtain ⟨w₂, hw₂, hyw₂⟩ := hy
  obtain ⟨u, hu, hxyu⟩ :=
    CellMulParabolic.cell_mul_in_parabolic_from_bnpair bp ax S' w₁ w₂ hw₁ hw₂ x y hxw₁ hyw₂
  exact ⟨u, hu, hxyu⟩

/-- Standard parabolics are closed under inversion: if $x \in BwB \subseteq P_{S'}$ then
$x^{-1} \in Bw^{-1}B$, and $w^{-1} \in W_{S'}$ still. -/
lemma standardParabolic_inv (bp : BNPair G M)
    (S' : Set B_idx) {x : G} (hx : x ∈ bp.standardParabolic S') :
    x⁻¹ ∈ bp.standardParabolic S' := by
  rw [standardParabolic, Set.mem_iUnion₂] at hx ⊢
  obtain ⟨w, hw, hxw⟩ := hx
  exact ⟨w⁻¹, (bp.parabolicSubgroupW S').inv_mem hw,
    BNPair.cell_inv_from_bnpair bp w x hxw⟩

/-- **Key technical lemma for self-normalization.** Let $Q$ be a subgroup containing $B$,
and let $n$ be an $N$-lift of $w \in W$ such that $nBn^{-1} \subseteq Q$. Then $n \in Q$.
Proved by induction on the length of $w$, using a "BN3"-style trick: descend by a simple
reflection and use that conjugates of the cell of a simple reflection produce $B$ or
$BsB$ elements that already lie in $Q$. -/
lemma N_lift_mem_subgroup_of_conj (bp : BNPair G M) (ax : BNPairAxioms bp)
    (Q : Subgroup G) (hBQ : bp.B ≤ Q)
    (w : M.Group) (n : bp.N) (hn : bp.π n = w)
    (hn_conj : ∀ b ∈ bp.B, (n : G) * b * (n : G)⁻¹ ∈ (Q : Set G)) :
    (n : G) ∈ (Q : Set G) := by
  let cs := M.toCoxeterSystem

  suffices ∀ (k : ℕ) (w : M.Group) (n : bp.N), cs.length w = k →
      bp.π n = w →
      (∀ b ∈ bp.B, (n : G) * b * (n : G)⁻¹ ∈ (Q : Set G)) →
      (n : G) ∈ (Q : Set G) from
    this (cs.length w) w n rfl hn hn_conj
  intro k
  induction k using Nat.strongRecOn with
  | _ k IH =>
  intro w n hlen hn_eq hn_conj'
  by_cases hk0 : k = 0
  ·
    subst hk0
    have hw1 : w = 1 := cs.length_eq_zero_iff.mp hlen
    have hn1 : bp.π n = 1 := by rw [hn_eq, hw1]
    have n_in_T : (n : G) ∈ bp.T := (bp.π_ker n).mp hn1
    exact hBQ (by rw [bp.T_eq] at n_in_T; exact (Subgroup.mem_inf.mp n_in_T).1)
  ·
    have hne1 : w ≠ 1 := by
      intro heq; rw [heq, cs.length_one] at hlen; exact hk0 hlen.symm
    obtain ⟨s, hs_descent⟩ := cs.exists_rightDescent_of_ne_one hne1
    have hlen_ws : cs.length (w * cs.simple s) + 1 = cs.length w :=
      cs.isRightDescent_iff.mp hs_descent
    have hlen_ws_lt : cs.length (w * cs.simple s) < k := by omega

    obtain ⟨n_s, hn_s⟩ := bp.π_surj (cs.simple s)

    let A : bp.N := n * n_s
    have hA_eq : bp.π A = w * cs.simple s := by
      show bp.π (n * n_s) = w * cs.simple s
      rw [map_mul, hn_eq, hn_s]


    have hlen_wss : cs.length (w * cs.simple s * cs.simple s) >
        cs.length (w * cs.simple s) := by
      rw [mul_assoc, cs.simple_mul_simple_self, mul_one]; omega

    obtain ⟨x, hx_cell, y, hy_cell, hxy_cell⟩ :=
      bn3_gives_element_in_BsB bp ax s n_s hn_s

    obtain ⟨a₀, ha₀⟩ := exists_mem_bruhatCell bp (w * cs.simple s)

    have ha₀x_in_BwB : a₀ * x ∈ bp.bruhatCell w := by
      have h : a₀ * x ∈ setMul (bp.bruhatCell (w * cs.simple s))
          (bp.bruhatCell (cs.simple s)) := ⟨a₀, ha₀, x, hx_cell, rfl⟩
      have := ax.cell_mul_length_increasing (w * cs.simple s) s hlen_wss h
      rwa [mul_assoc, cs.simple_mul_simple_self, mul_one] at this
    have ha₀y_in_BwB : a₀ * y ∈ bp.bruhatCell w := by
      have h : a₀ * y ∈ setMul (bp.bruhatCell (w * cs.simple s))
          (bp.bruhatCell (cs.simple s)) := ⟨a₀, ha₀, y, hy_cell, rfl⟩
      have := ax.cell_mul_length_increasing (w * cs.simple s) s hlen_wss h
      rwa [mul_assoc, cs.simple_mul_simple_self, mul_one] at this

    obtain ⟨⟨b₁x, hb₁x⟩, n'x, ⟨b₂x, hb₂x⟩, hπx, heqx⟩ := ha₀x_in_BwB
    obtain ⟨⟨b₁y, hb₁y⟩, n'y, ⟨b₂y, hb₂y⟩, hπy, heqy⟩ := ha₀y_in_BwB


    have hn'x_eq : bp.π (n'x * n⁻¹) = 1 := by
      rw [map_mul, map_inv, hπx, hn_eq, mul_inv_cancel]
    have hn'x_T : ((n'x * n⁻¹ : bp.N) : G) ∈ bp.T := (bp.π_ker _).mp hn'x_eq
    have hn'x_B : ((n'x * n⁻¹ : bp.N) : G) ∈ bp.B := by
      rw [bp.T_eq] at hn'x_T; exact (Subgroup.mem_inf.mp hn'x_T).1
    have ha₀x_n_inv : a₀ * x * (n : G)⁻¹ ∈ (Q : Set G) := by
      have key : a₀ * x * (n : G)⁻¹ =
          (b₁x : G) * ((n'x * n⁻¹ : bp.N) : G) * ((n : G) * b₂x * (n : G)⁻¹) := by
        rw [heqx]; simp [Subgroup.coe_mul]; group
      rw [key]
      exact Q.mul_mem (Q.mul_mem (hBQ hb₁x) (hBQ hn'x_B))
        (hn_conj' b₂x hb₂x)

    have hn'y_eq : bp.π (n'y * n⁻¹) = 1 := by
      rw [map_mul, map_inv, hπy, hn_eq, mul_inv_cancel]
    have hn'y_T : ((n'y * n⁻¹ : bp.N) : G) ∈ bp.T := (bp.π_ker _).mp hn'y_eq
    have hn'y_B : ((n'y * n⁻¹ : bp.N) : G) ∈ bp.B := by
      rw [bp.T_eq] at hn'y_T; exact (Subgroup.mem_inf.mp hn'y_T).1
    have ha₀y_n_inv : a₀ * y * (n : G)⁻¹ ∈ (Q : Set G) := by
      have key : a₀ * y * (n : G)⁻¹ =
          (b₁y : G) * ((n'y * n⁻¹ : bp.N) : G) * ((n : G) * b₂y * (n : G)⁻¹) := by
        rw [heqy]; simp [Subgroup.coe_mul]; group
      rw [key]
      exact Q.mul_mem (Q.mul_mem (hBQ hb₁y) (hBQ hn'y_B))
        (hn_conj' b₂y hb₂y)

    have hn_xy_n_inv : (n : G) * (x⁻¹ * y) * (n : G)⁻¹ ∈ (Q : Set G) := by
      have key : (n : G) * (x⁻¹ * y) * (n : G)⁻¹ =
          (a₀ * x * (n : G)⁻¹)⁻¹ * (a₀ * y * (n : G)⁻¹) := by group
      rw [key]
      exact Q.mul_mem (Q.inv_mem ha₀x_n_inv) ha₀y_n_inv

    obtain ⟨⟨b₁s, hb₁s⟩, n_s', ⟨b₂s, hb₂s⟩, hπs, heqs⟩ := hxy_cell

    have hn_ns'_n_inv : (n : G) * (n_s' : G) * (n : G)⁻¹ ∈ (Q : Set G) := by
      have key : (n : G) * (n_s' : G) * (n : G)⁻¹ =
          ((n : G) * b₁s * (n : G)⁻¹)⁻¹ *
          ((n : G) * (x⁻¹ * y) * (n : G)⁻¹) *
          ((n : G) * b₂s * (n : G)⁻¹)⁻¹ := by
        rw [heqs]; group
      rw [key]
      exact Q.mul_mem (Q.mul_mem (Q.inv_mem (hn_conj' b₁s hb₁s)) hn_xy_n_inv)
        (Q.inv_mem (hn_conj' b₂s hb₂s))


    have hA_conj : ∀ b ∈ bp.B,
        (n : G) * (n_s' : G) * b * ((n_s' : G)⁻¹ * (n : G)⁻¹) ∈ (Q : Set G) := by
      intro b hb


      have hns'_cell : (n_s' : G) ∈ bp.bruhatCell (cs.simple s) :=
        ⟨⟨1, bp.B.one_mem⟩, n_s', ⟨1, bp.B.one_mem⟩, hπs, by simp⟩
      have hns'_inv_cell : (n_s' : G)⁻¹ ∈ bp.bruhatCell (cs.simple s) :=
        CellDisjoint.inv_mem_bruhatCell_simple bp hns'_cell
      have hns'b_cell : (n_s' : G) * b ∈ bp.bruhatCell (cs.simple s) :=
        CellMulParabolic.bruhatCell_mul_B_right bp hns'_cell hb
      have hconj_in_prod : (n_s' : G) * b * (n_s' : G)⁻¹ ∈
          setMul (bp.bruhatCell (cs.simple s)) (bp.bruhatCell (cs.simple s)) :=
        ⟨(n_s' : G) * b, hns'b_cell, (n_s' : G)⁻¹, hns'_inv_cell, by group⟩
      have hlen_ss : cs.length (cs.simple s * cs.simple s) < cs.length (cs.simple s) := by
        rw [cs.simple_mul_simple_self s, cs.length_one, cs.length_simple]; omega
      have hprod_sub := ax.cell_mul_length_decreasing (cs.simple s) s hlen_ss
      rcases hprod_sub hconj_in_prod with hcase_B | hcase_BsB
      ·
        rw [cs.simple_mul_simple_self] at hcase_B
        have hb' := CellDisjoint.bruhatCell_one_sub_B' bp hcase_B
        have : (n : G) * (n_s' : G) * b * ((n_s' : G)⁻¹ * (n : G)⁻¹) =
            (n : G) * ((n_s' : G) * b * (n_s' : G)⁻¹) * (n : G)⁻¹ := by group
        rw [this]
        exact hn_conj' _ hb'
      ·
        obtain ⟨⟨β₁, hβ₁⟩, n_s'', ⟨β₂, hβ₂⟩, hπs'', heq_conj⟩ := hcase_BsB

        have hπ_diff : bp.π (n_s'' * n_s'⁻¹) = 1 := by
          rw [map_mul, map_inv, hπs'', hπs, mul_inv_cancel]
        have hdiff_T : ((n_s'' * n_s'⁻¹ : bp.N) : G) ∈ bp.T := (bp.π_ker _).mp hπ_diff
        have hdiff_B : ((n_s'' * n_s'⁻¹ : bp.N) : G) ∈ bp.B := by
          rw [bp.T_eq] at hdiff_T; exact (Subgroup.mem_inf.mp hdiff_T).1

        have hn_ns''_n_inv : (n : G) * (n_s'' : G) * (n : G)⁻¹ ∈ (Q : Set G) := by
          have : (n_s'' : G) = ((n_s'' * n_s'⁻¹ : bp.N) : G) * (n_s' : G) := by
            simp [Subgroup.coe_mul]
          rw [this]
          have : (n : G) * (((n_s'' * n_s'⁻¹ : bp.N) : G) * (n_s' : G)) * (n : G)⁻¹ =
              ((n : G) * ((n_s'' * n_s'⁻¹ : bp.N) : G) * (n : G)⁻¹) *
              ((n : G) * (n_s' : G) * (n : G)⁻¹) := by group
          rw [this]
          exact Q.mul_mem (hn_conj' _ hdiff_B) hn_ns'_n_inv


        have : (n : G) * (n_s' : G) * b * ((n_s' : G)⁻¹ * (n : G)⁻¹) =
            ((n : G) * β₁ * (n : G)⁻¹) *
            ((n : G) * (n_s'' : G) * (n : G)⁻¹) *
            ((n : G) * β₂ * (n : G)⁻¹) := by
          have : (n_s' : G) * b * (n_s' : G)⁻¹ = β₁ * (n_s'' : G) * β₂ := heq_conj
          calc (n : G) * (n_s' : G) * b * ((n_s' : G)⁻¹ * (n : G)⁻¹)
              = (n : G) * ((n_s' : G) * b * (n_s' : G)⁻¹) * (n : G)⁻¹ := by group
            _ = (n : G) * (β₁ * (n_s'' : G) * β₂) * (n : G)⁻¹ := by
                rw [heq_conj]
            _ = _ := by group
        rw [this]
        exact Q.mul_mem (Q.mul_mem (hn_conj' β₁ hβ₁) hn_ns''_n_inv) (hn_conj' β₂ hβ₂)


    have hπ_ns_diff : bp.π (n_s * n_s'⁻¹) = 1 := by
      rw [map_mul, map_inv, hn_s, hπs, mul_inv_cancel]
    have hns_diff_T : ((n_s * n_s'⁻¹ : bp.N) : G) ∈ bp.T := (bp.π_ker _).mp hπ_ns_diff
    have hns_diff_B : ((n_s * n_s'⁻¹ : bp.N) : G) ∈ bp.B := by
      rw [bp.T_eq] at hns_diff_T; exact (Subgroup.mem_inf.mp hns_diff_T).1

    have hn_ns_n_inv : (n : G) * (n_s : G) * (n : G)⁻¹ ∈ (Q : Set G) := by
      have : (n_s : G) = ((n_s * n_s'⁻¹ : bp.N) : G) * (n_s' : G) := by
        simp [Subgroup.coe_mul]
      rw [this]
      have : (n : G) * (((n_s * n_s'⁻¹ : bp.N) : G) * (n_s' : G)) * (n : G)⁻¹ =
          ((n : G) * ((n_s * n_s'⁻¹ : bp.N) : G) * (n : G)⁻¹) *
          ((n : G) * (n_s' : G) * (n : G)⁻¹) := by group
      rw [this]
      exact Q.mul_mem (hn_conj' _ hns_diff_B) hn_ns'_n_inv


    let A' : bp.N := n * n_s'
    have hA'_eq : bp.π A' = w * cs.simple s := by
      show bp.π (n * n_s') = w * cs.simple s
      rw [map_mul, hn_eq, hπs]
    have hA'_conj : ∀ b ∈ bp.B, (A' : G) * b * (A' : G)⁻¹ ∈ (Q : Set G) := by
      intro b hb
      change (n : G) * (n_s' : G) * b * ((n : G) * (n_s' : G))⁻¹ ∈ (Q : Set G)
      rw [mul_inv_rev]
      exact hA_conj b hb
    have hA'_in_Q : (A' : G) ∈ (Q : Set G) :=
      IH (cs.length (w * cs.simple s)) hlen_ws_lt (w * cs.simple s) A' rfl hA'_eq hA'_conj

    have hn_inv_in_Q : (n : G)⁻¹ ∈ (Q : Set G) := by
      have key : (n : G)⁻¹ = (A' : G)⁻¹ * ((n : G) * (n_s' : G) * (n : G)⁻¹) := by
        change (n : G)⁻¹ = ((n : G) * (n_s' : G))⁻¹ * ((n : G) * (n_s' : G) * (n : G)⁻¹)
        group
      rw [key]
      exact Q.mul_mem (Q.inv_mem hA'_in_Q) hn_ns'_n_inv
    exact (inv_inv (n : G) ▸ Q.inv_mem hn_inv_in_Q : (n : G) ∈ ↑Q)

/-- Strengthening of `N_lift_mem_subgroup_of_conj`: under the same hypotheses, the entire
Bruhat cell $BwB$ is contained in $Q$, not just the chosen lift $n$. -/
lemma bruhatCell_sub_of_conj (bp : BNPair G M) (ax : BNPairAxioms bp)
    (Q : Subgroup G) (hBQ : bp.B ≤ Q)
    (w : M.Group) (n : bp.N) (hn : bp.π n = w)
    (hn_conj : ∀ b ∈ bp.B, (n : G) * b * (n : G)⁻¹ ∈ (Q : Set G)) :
    bp.bruhatCell w ⊆ (Q : Set G) := by
  have hn_Q := N_lift_mem_subgroup_of_conj bp ax Q hBQ w n hn hn_conj

  have hn_BwB : (n : G) ∈ bp.bruhatCell w :=
    ⟨⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, hn, by simp⟩
  exact cell_sub_of_mem bp Q hBQ w (n : G) hn_Q hn_BwB

/-- **Standard parabolics are self-normalizing.** If $g \in G$ satisfies
$gP_{S'}g^{-1} = P_{S'}$ in the sense that conjugation by $g$ preserves membership in
$P_{S'}$, then $g \in P_{S'}$. Equivalently $N_G(P_{S'}) = P_{S'}$.
Proof: write $g = b_1 n b_2$ by Bruhat, deduce that $n$ normalizes $B$ modulo $P_{S'}$,
and apply `bruhatCell_sub_of_conj` to conclude that the entire cell $BwB$ (and hence $g$)
lies in $P_{S'}$. -/
theorem normalizer_in_parabolic_from_bnpair
    (bp : BNPair G M) (ax : BNPairAxioms bp) :
    ∀ S' : Set B_idx, ∀ g : G,
    (∀ x, x ∈ bp.standardParabolic S' ↔
      g * x * g⁻¹ ∈ bp.standardParabolic S') →
    g ∈ bp.standardParabolic S' := by
  intro S' g hnorm
  let cs := M.toCoxeterSystem
  let PS := bp.standardParabolic S'


  let Q : Subgroup G :=
  { carrier := PS
    mul_mem' := fun hx hy => standardParabolic_mul bp ax S' hx hy
    one_mem' := B_sub_standardParabolic bp S' bp.B.one_mem
    inv_mem' := fun hx => standardParabolic_inv bp S' hx }
  have hBQ : bp.B ≤ Q := B_sub_standardParabolic bp S'

  obtain ⟨w, hwg⟩ := CellCover.cell_cover_from_bnpair bp ax g

  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hwg


  have hn_conj : ∀ b' ∈ bp.B, (n : G) * b' * (n : G)⁻¹ ∈ (Q : Set G) := by
    intro b' hb'

    have hb'' : (b₂ : G)⁻¹ * b' * b₂ ∈ bp.B :=
      bp.B.mul_mem (bp.B.mul_mem (bp.B.inv_mem hb₂) hb') hb₂

    have hconj : g * ((b₂ : G)⁻¹ * b' * b₂) * g⁻¹ ∈ PS :=
      (hnorm _).mp (hBQ hb'')

    have heq : g * ((b₂ : G)⁻¹ * b' * b₂) * g⁻¹ =
        (b₁ : G) * ((n : G) * b' * (n : G)⁻¹) * (b₁ : G)⁻¹ := by
      rw [hg_eq]; group
    rw [heq] at hconj


    have hb₁_Q : b₁ ∈ (Q : Set G) := hBQ hb₁
    have hb₁_inv_Q : b₁⁻¹ ∈ (Q : Set G) := Q.inv_mem hb₁_Q
    have hconj_Q : b₁ * ((n : G) * b' * (n : G)⁻¹) * b₁⁻¹ ∈ (Q : Set G) := hconj

    have key : (n : G) * b' * (n : G)⁻¹ =
        b₁⁻¹ * (b₁ * ((n : G) * b' * (n : G)⁻¹) * b₁⁻¹) * b₁ := by group
    rw [key]
    exact Q.mul_mem (Q.mul_mem hb₁_inv_Q hconj_Q) hb₁_Q

  have hBwB_sub : bp.bruhatCell w ⊆ PS :=
    bruhatCell_sub_of_conj bp ax Q hBQ w n hπ hn_conj


  exact hBwB_sub ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩

/-- The Borel $B$ is contained in the subgroup generated by any Bruhat cell $BwB$:
write $b = n^{-1} \cdot (nb)$ where $n$ and $nb$ both lie in the cell. -/
lemma B_le_closure_bruhatCell (bp : BNPair G M) (w : M.Group) :
    bp.B ≤ Subgroup.closure (bp.bruhatCell w) := by
  intro b hb
  obtain ⟨n, hn⟩ := bp.π_surj w
  have hn_mem : (n : G) ∈ bp.bruhatCell w :=
    ⟨⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, hn, by simp⟩
  have hnb_mem : (n : G) * b ∈ bp.bruhatCell w :=
    ⟨⟨1, bp.B.one_mem⟩, n, ⟨b, hb⟩, hn, by simp⟩
  have hn_cl := Subgroup.subset_closure hn_mem
  have hnb_cl := Subgroup.subset_closure hnb_mem
  have : b = (n : G)⁻¹ * ((n : G) * b) := by group
  rw [this]
  exact (Subgroup.closure (bp.bruhatCell w)).mul_mem
    ((Subgroup.closure (bp.bruhatCell w)).inv_mem hn_cl) hnb_cl

/-- If $BwB \subseteq Q$ for a subgroup $Q$ containing $B$, then $w \in W_{S_Q}$ where
$S_Q = \{s : BsB \subseteq Q\}$. Specialization of `w_mem_parabolicW_of_cell_sub` to the
canonical $S' = S_Q$. -/
theorem bruhatCell_generators_in_subgroup
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (Q : Subgroup G) (w : M.Group)
    (hBwB : bp.bruhatCell w ⊆ (Q : Set G))
    (hBQ : bp.B ≤ Q) :
    w ∈ bp.parabolicSubgroupW { s : B_idx | bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆ (Q : Set G) } :=
  w_mem_parabolicW_of_cell_sub bp ax Q hBQ _ rfl w hBwB

/-- Specializing `bruhatCell_generators_in_subgroup` to $Q = \langle BwB \rangle$: the
element $w$ lies in the parabolic Weyl subgroup generated by those simple reflections $s$
whose cell $BsB$ is already inside $\langle BwB \rangle$. -/
theorem generators_in_closure_bruhatCell
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (w : M.Group) :
    w ∈ bp.parabolicSubgroupW
      { s : B_idx | bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆
        (Subgroup.closure (bp.bruhatCell w) : Set G) } := by
  apply bruhatCell_generators_in_subgroup bp ax
  · exact Subgroup.subset_closure
  · exact B_le_closure_bruhatCell bp w

/-- An $N$-lift of a simple reflection $s$ lies in $\langle BwB \rangle$ whenever the
simple cell $BsB$ does. Direct from `lift_mem_bruhatCell`. -/
theorem N_lift_in_closure_bruhatCell
    (bp : BNPair G M) (w : M.Group)
    (s : B_idx) (hs : bp.bruhatCell (M.toCoxeterSystem.simple s) ⊆
      (Subgroup.closure (bp.bruhatCell w) : Set G))
    (n : bp.N) (hn : bp.π n = M.toCoxeterSystem.simple s) :
    (n : G) ∈ (Subgroup.closure (bp.bruhatCell w) : Set G) := by
  apply hs
  exact ⟨⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, hn, by simp⟩

/-- The conjugate Borel $n^{-1} B n = \{n^{-1} b n : b \in B\}$ as a subset of $G$, used to
present $\langle BwB \rangle$ as $\langle B \cup n^{-1}Bn \rangle$. -/
def conjB (bp : BNPair G M) (n : bp.N) : Set G :=
  { g : G | ∃ b ∈ bp.B, g = (n : G)⁻¹ * b * (n : G) }

/-- One inclusion of the equality $\langle BwB \rangle = \langle B \cup n^{-1}Bn \rangle$:
every element of $BwB$ already lies in $\langle B \cup n^{-1}Bn \rangle$. Uses
`N_lift_mem_subgroup_of_conj` applied to $n^{-1}$. -/
theorem bruhatCell_sub_closure_B_conjB
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (w : M.Group) (n : bp.N) (hn : bp.π n = w) :
    bp.bruhatCell w ⊆
      (Subgroup.closure ((bp.B : Set G) ∪ conjB bp n) : Set G) := by
  set Q := Subgroup.closure ((bp.B : Set G) ∪ conjB bp n)
  have hBQ : bp.B ≤ Q := by
    intro b hb
    exact Subgroup.subset_closure (Set.mem_union_left _ hb)
  have hconjQ : ∀ b ∈ bp.B, (n : G)⁻¹ * b * (n : G) ∈ (Q : Set G) := by
    intro b hb
    apply Subgroup.subset_closure
    right
    exact ⟨b, hb, rfl⟩
  have hn_inv_conj : ∀ b ∈ bp.B, (n⁻¹ : bp.N) * b * ((n⁻¹ : bp.N) : G)⁻¹ ∈ (Q : Set G) := by
    intro b hb
    simp only [Subgroup.coe_inv, inv_inv]
    exact hconjQ b hb
  have hπ_inv : bp.π (n⁻¹) = w⁻¹ := by
    rw [map_inv, hn]
  have hn_inv_Q : ((n⁻¹ : bp.N) : G) ∈ (Q : Set G) :=
    N_lift_mem_subgroup_of_conj bp ax Q hBQ w⁻¹ n⁻¹ hπ_inv hn_inv_conj
  have hn_Q : (n : G) ∈ (Q : Set G) := by
    have : (n : G) = ((n⁻¹ : bp.N) : G)⁻¹ := by simp
    rw [this]
    exact Q.inv_mem hn_inv_Q
  intro g hg
  obtain ⟨⟨b₁, hb₁⟩, n', ⟨b₂, hb₂⟩, hπ', hg_eq⟩ := hg
  have hπ_diff : bp.π (n' * n⁻¹) = 1 := by
    rw [map_mul, map_inv, hπ', hn, mul_inv_cancel]
  have hdiff_T : ((n' * n⁻¹ : bp.N) : G) ∈ bp.T := (bp.π_ker _).mp hπ_diff
  have hdiff_B : ((n' * n⁻¹ : bp.N) : G) ∈ bp.B := by
    rw [bp.T_eq] at hdiff_T; exact (Subgroup.mem_inf.mp hdiff_T).1
  have hn'_Q : (n' : G) ∈ (Q : Set G) := by
    have : (n' : G) = ((n' * n⁻¹ : bp.N) : G) * (n : G) := by
      simp [Subgroup.coe_mul]
    rw [this]
    exact Q.mul_mem (hBQ hdiff_B) hn_Q
  rw [hg_eq]
  exact Q.mul_mem (Q.mul_mem (hBQ hb₁) hn'_Q) (hBQ hb₂)

/-- The other inclusion: $\langle B \cup n^{-1}Bn \rangle \leq \langle BwB \rangle$. Both
generating sets lie in $\langle BwB \rangle$ since $n \in BwB$ and $B \subseteq \langle BwB \rangle$. -/
theorem closure_B_conjB_sub_closure_bruhatCell
    (bp : BNPair G M) (w : M.Group) (n : bp.N) (hn : bp.π n = w) :
    Subgroup.closure ((bp.B : Set G) ∪ conjB bp n) ≤
      Subgroup.closure (bp.bruhatCell w) := by
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with hg_B | hg_conj
  · exact B_le_closure_bruhatCell bp w hg_B
  · obtain ⟨b, hb, hg_eq⟩ := hg_conj
    rw [hg_eq]
    have hn_mem : (n : G) ∈ bp.bruhatCell w :=
      ⟨⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, hn, by simp⟩
    have hn_cl := Subgroup.subset_closure hn_mem
    have hn_inv_cl := (Subgroup.closure (bp.bruhatCell w)).inv_mem hn_cl
    have hb_cl := B_le_closure_bruhatCell bp w hb
    exact (Subgroup.closure (bp.bruhatCell w)).mul_mem
      ((Subgroup.closure (bp.bruhatCell w)).mul_mem hn_inv_cl hb_cl) hn_cl

/-- **Generating description of $\langle BwB \rangle$.** The subgroup of $G$ generated by
the Bruhat cell $BwB$ coincides with the subgroup generated by $B \cup n^{-1}Bn$, for any
choice of $N$-lift $n$ of $w$. Combines `bruhatCell_sub_closure_B_conjB` and
`closure_B_conjB_sub_closure_bruhatCell`. -/
theorem closure_bruhatCell_eq_closure_B_conjB
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (w : M.Group) (n : bp.N) (hn : bp.π n = w) :
    Subgroup.closure (bp.bruhatCell w) =
      Subgroup.closure ((bp.B : Set G) ∪ conjB bp n) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact bruhatCell_sub_closure_B_conjB bp ax w n hn
  · exact closure_B_conjB_sub_closure_bruhatCell bp w n hn

end NormalizerParabolic
