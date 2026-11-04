/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.CellDisjointHelpers
import Atlas.Buildings.code.BNPair.CellCoverProof
import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

namespace CellDisjoint

open BNPair

/-- Simple reflections are involutions: $s^{-1} = s$. -/
lemma simple_inv_eq (cs : CoxeterSystem M M.Group) (s : B_idx) :
    (cs.simple s)⁻¹ = cs.simple s :=
  mul_left_cancel (a := cs.simple s) (by rw [cs.simple_mul_simple_self s, mul_inv_cancel])

/-- Simple reflections have length one, hence are nontrivial: $s \neq 1$. -/
lemma simple_ne_one (cs : CoxeterSystem M M.Group) (s : B_idx) :
    cs.simple s ≠ 1 := by
  intro h; have := cs.length_simple s; rw [h, cs.length_one] at this; omega

/-- If $g \in B \cap C(w)$ then $w = 1$. The unique cell containing $B$-elements is $C(1)$. -/
lemma eq_one_of_mem_B_and_bruhatCell (bp : BNPair G M) {g : G} {w : M.Group}
    (hg_B : g ∈ bp.B) (hg_w : g ∈ bp.bruhatCell w) : w = 1 := by
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg_w
  have hn_in_B : (n : G) ∈ bp.B := by
    have : (n : G) = b₁⁻¹ * g * b₂⁻¹ := by rw [hg_eq]; group
    rw [this]; exact bp.B.mul_mem (bp.B.mul_mem (bp.B.inv_mem hb₁) hg_B) (bp.B.inv_mem hb₂)
  have hn_in_T : (n : G) ∈ bp.T := by
    rw [bp.T_eq]; exact Subgroup.mem_inf.mpr ⟨hn_in_B, n.prop⟩
  rw [← hπ]; exact (bp.π_ker n).mpr hn_in_T

/-- The identity Bruhat cell coincides with $B$: $C(1) \subseteq B$. -/
lemma bruhatCell_one_sub_B' (bp : BNPair G M) {g : G}
    (hg : g ∈ bp.bruhatCell 1) : g ∈ bp.B := by
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπn, hg_eq⟩ := hg
  have hn_in_T : (n : G) ∈ bp.T := (bp.π_ker n).mp hπn
  have hn_in_B : (n : G) ∈ bp.B := by
    rw [bp.T_eq] at hn_in_T; exact (Subgroup.mem_inf.mp hn_in_T).1
  rw [hg_eq]; exact bp.B.mul_mem (bp.B.mul_mem hb₁ hn_in_B) hb₂

/-- Double simple cancellation: $w \cdot s \cdot s = w$ for any simple reflection $s$. -/
lemma mul_simple_simple_self (cs : CoxeterSystem M M.Group) (w : M.Group)
    (s : B_idx) : w * cs.simple s * cs.simple s = w := by
  rw [mul_assoc, cs.simple_mul_simple_self, mul_one]

/-- Cell decomposition: when $\ell(ws) < \ell(w)$, every $g \in C(w)$ factors as $g = a \cdot b$
with $a \in C(ws)$ and $b \in C(s)$. -/
lemma cell_decomp (bp : BNPair G M) {w : M.Group} {g : G}
    (hg : g ∈ bp.bruhatCell w) (s : B_idx)
    (_hlen : M.toCoxeterSystem.length (w * M.toCoxeterSystem.simple s) <
             M.toCoxeterSystem.length w) :
    ∃ a ∈ bp.bruhatCell (w * M.toCoxeterSystem.simple s),
    ∃ b ∈ bp.bruhatCell (M.toCoxeterSystem.simple s),
    g = a * b := by
  let cs := M.toCoxeterSystem
  obtain ⟨⟨b₁, hb₁⟩, nw, ⟨b₂, hb₂⟩, hπw, hg_eq⟩ := hg
  obtain ⟨n_ws, hn_ws⟩ := bp.π_surj (w * cs.simple s)
  obtain ⟨ns, hns⟩ := bp.π_surj (cs.simple s)

  have hπ_prod : bp.π (n_ws * ns) = w := by
    rw [map_mul, hn_ws, hns, mul_assoc, cs.simple_mul_simple_self, mul_one]

  have hπ_diff : bp.π (nw⁻¹ * (n_ws * ns)) = 1 := by
    rw [map_mul, map_inv, hπw, hπ_prod, inv_mul_cancel]
  have hdiff_in_T : ((nw⁻¹ * (n_ws * ns) : bp.N) : G) ∈ bp.T :=
    (bp.π_ker _).mp hπ_diff
  have hdiff_in_B : ((nw⁻¹ * (n_ws * ns) : bp.N) : G) ∈ bp.B := by
    rw [bp.T_eq] at hdiff_in_T; exact (Subgroup.mem_inf.mp hdiff_in_T).1


  let cG : G := (nw : G)⁻¹ * ((n_ws : G) * (ns : G))
  have hcG_eq : cG = (nw : G)⁻¹ * ((n_ws : G) * (ns : G)) := rfl
  have hcG_B : cG ∈ bp.B := by
    show (nw : G)⁻¹ * ((n_ws : G) * (ns : G)) ∈ bp.B

    have : ((nw⁻¹ * (n_ws * ns) : bp.N) : G) = (nw : G)⁻¹ * ((n_ws : G) * (ns : G)) := by
      simp [Subgroup.coe_mul]
    rw [← this]; exact hdiff_in_B
  have hnw_eq : (nw : G) = (n_ws : G) * (ns : G) * cG⁻¹ := by
    rw [hcG_eq]; group

  have hg_decomp : g = (b₁ * (n_ws : G)) * ((ns : G) * (cG⁻¹ * b₂)) := by
    rw [hg_eq, hnw_eq]; group
  have ha : b₁ * (n_ws : G) ∈ bp.bruhatCell (w * cs.simple s) :=
    ⟨⟨b₁, hb₁⟩, n_ws, ⟨1, bp.B.one_mem⟩, hn_ws, by simp⟩
  have hb : (ns : G) * (cG⁻¹ * b₂) ∈ bp.bruhatCell (cs.simple s) :=
    ⟨⟨1, bp.B.one_mem⟩, ns, ⟨cG⁻¹ * b₂,
      bp.B.mul_mem (bp.B.inv_mem hcG_B) hb₂⟩, hns, by simp⟩
  exact ⟨_, ha, _, hb, hg_decomp⟩

/-- $C(s)$ is closed under inversion since $s^{-1} = s$: $b \in C(s) \Rightarrow b^{-1} \in C(s)$. -/
lemma inv_mem_bruhatCell_simple (bp : BNPair G M) {b : G} {s : B_idx}
    (hb : b ∈ bp.bruhatCell (M.toCoxeterSystem.simple s)) :
    b⁻¹ ∈ bp.bruhatCell (M.toCoxeterSystem.simple s) := by
  have := bp.cell_inv_from_bnpair _ b hb
  rwa [simple_inv_eq] at this

/-- Trivial packaging: $xy \in C(w) \cdot C(s)$ when $x \in C(w)$ and $y \in C(s)$. -/
lemma mem_setMul_of_mem_cells (bp : BNPair G M) {w : M.Group} {s : B_idx}
    {x y : G} (hx : x ∈ bp.bruhatCell w)
    (hy : y ∈ bp.bruhatCell (M.toCoxeterSystem.simple s)) :
    x * y ∈ setMul (bp.bruhatCell w)
      (bp.bruhatCell (M.toCoxeterSystem.simple s)) :=
  ⟨x, hx, y, hy, rfl⟩

/-- *Bruhat cell disjointness*: distinct Bruhat cells are disjoint, i.e.
$C(w) \cap C(w') \neq \emptyset \Rightarrow w = w'$. Together with `cell_cover_from_bnpair`,
this yields $G = \bigsqcup_{w \in W} BwB$. -/
theorem cell_disjoint_from_bnpair (bp : BNPair G M) (ax : BNPairAxioms bp)
    (w w' : M.Group) (h : (bp.bruhatCell w ∩ bp.bruhatCell w').Nonempty) :
    w = w' := by
  let cs := M.toCoxeterSystem

  suffices key : ∀ (n : ℕ) (w w' : M.Group) (g : G),
      cs.length w ≤ n →
      g ∈ bp.bruhatCell w → g ∈ bp.bruhatCell w' → w = w' by
    obtain ⟨g, hgw, hgw'⟩ := h
    exact key _ w w' g le_rfl hgw hgw'
  intro n
  induction n with
  | zero =>
    intro w w' g hle hw hw'
    have hw1 : w = 1 := cs.length_eq_zero_iff.mp (by omega)
    subst hw1
    have g_in_B := bruhatCell_one_sub_B' bp hw
    exact (eq_one_of_mem_B_and_bruhatCell bp g_in_B hw').symm
  | succ n ih =>
    intro w w' g hle hw hw'
    by_cases hw1 : w = 1
    · subst hw1
      have g_in_B := bruhatCell_one_sub_B' bp hw
      exact (eq_one_of_mem_B_and_bruhatCell bp g_in_B hw').symm
    ·
      obtain ⟨s, hs⟩ := cs.exists_rightDescent_of_ne_one hw1
      have hlen_ws : cs.length (w * cs.simple s) < cs.length w := hs

      obtain ⟨a, ha_ws, b, hb_s, hg_eq⟩ := cell_decomp bp hw s hlen_ws

      have hb_inv : b⁻¹ ∈ bp.bruhatCell (cs.simple s) := inv_mem_bruhatCell_simple bp hb_s

      have ha_eq : a = g * b⁻¹ := by rw [hg_eq]; group

      have ha_in_prod : a ∈ setMul (bp.bruhatCell w')
          (bp.bruhatCell (cs.simple s)) := by
        rw [ha_eq]; exact mem_setMul_of_mem_cells bp hw' hb_inv

      have hlen_ws_le : cs.length (w * cs.simple s) ≤ n := by omega
      rcases cs.length_mul_simple w' s with hlen_w's | hlen_w's
      ·
        have hlen_inc : cs.length (w' * cs.simple s) > cs.length w' := by omega
        have ha_w's : a ∈ bp.bruhatCell (w' * cs.simple s) :=
          ax.cell_mul_length_increasing w' s hlen_inc ha_in_prod

        have heq := ih (w * cs.simple s) (w' * cs.simple s) a hlen_ws_le ha_ws ha_w's

        exact mul_right_cancel heq
      ·
        have hlen_dec : cs.length (w' * cs.simple s) < cs.length w' := by omega
        have ha_union : a ∈ bp.bruhatCell (w' * cs.simple s) ∪ bp.bruhatCell w' :=
          ax.cell_mul_length_decreasing w' s hlen_dec ha_in_prod
        rcases ha_union with ha_w's | ha_w'
        ·
          exact mul_right_cancel (ih _ _ a hlen_ws_le ha_ws ha_w's)
        ·
          have heq := ih _ _ a hlen_ws_le ha_ws ha_w'


          exfalso
          have : cs.length w' < cs.length w := heq ▸ hlen_ws

          have hw's_eq_w : w' * cs.simple s = w := by
            rw [← heq]; exact mul_simple_simple_self cs w s

          have : cs.length w < cs.length w' := hw's_eq_w ▸ hlen_dec
          omega

end CellDisjoint
