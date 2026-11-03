/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Subgroup.Pointwise

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

namespace CellCover

open BNPair

/-- Any $b \in B$ lies in the identity Bruhat cell $C(1) = B \cdot T \cdot B$. -/
lemma B_mem_bruhatCell_one (bp : BNPair G M) {b : G} (hb : b ∈ bp.B) :
    b ∈ bp.bruhatCell 1 := by
  obtain ⟨n₀, hn₀⟩ := bp.π_surj (1 : M.Group)
  have n₀_in_T : (n₀ : G) ∈ bp.T := (bp.π_ker n₀).mp hn₀
  have n₀_in_B : (n₀ : G) ∈ bp.B := by
    rw [bp.T_eq] at n₀_in_T; exact (Subgroup.mem_inf.mp n₀_in_T).1
  exact ⟨⟨b * (↑n₀)⁻¹, bp.B.mul_mem hb (bp.B.inv_mem n₀_in_B)⟩, n₀,
    ⟨1, bp.B.one_mem⟩, hn₀, by simp⟩

/-- Right $B$-absorption: $C(w) \cdot B \subseteq C(w)$. -/
lemma bruhatCell_mul_B_right (bp : BNPair G M) {w : M.Group} {g b : G}
    (hg : g ∈ bp.bruhatCell w) (hb : b ∈ bp.B) :
    g * b ∈ bp.bruhatCell w := by
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  exact ⟨⟨b₁, hb₁⟩, n, ⟨b₂ * b, bp.B.mul_mem hb₂ hb⟩, hπ, by rw [hg_eq]; group⟩

/-- Multiplying $g \in C(w)$ by a lift $n \in N$ of a simple reflection $s$ lands in some Bruhat cell. -/
lemma bruhatCell_mul_N_simple (bp : BNPair G M) (ax : BNPairAxioms bp)
    {w : M.Group} {g : G} (hg : g ∈ bp.bruhatCell w)
    {n : bp.N} {s : B_idx} (hn : bp.π n = M.toCoxeterSystem.simple s) :
    ∃ u : M.Group, g * (n : G) ∈ bp.bruhatCell u := by

  have n_in_cell : (n : G) ∈ bp.bruhatCell (M.toCoxeterSystem.simple s) :=
    ⟨⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, hn, by simp⟩

  have gn_in_setMul : g * (n : G) ∈ setMul (bp.bruhatCell w)
      (bp.bruhatCell (M.toCoxeterSystem.simple s)) :=
    ⟨g, hg, (n : G), n_in_cell, rfl⟩

  let cs := M.toCoxeterSystem
  rcases cs.length_mul_simple w s with hlen | hlen
  ·
    have hgt : cs.length (w * cs.simple s) > cs.length w := by omega
    exact ⟨w * cs.simple s, ax.cell_mul_length_increasing w s hgt gn_in_setMul⟩
  ·
    have hlt : cs.length (w * cs.simple s) < cs.length w := by omega
    have h := ax.cell_mul_length_decreasing w s hlt gn_in_setMul
    rcases h with h | h
    · exact ⟨w * cs.simple s, h⟩
    · exact ⟨w, h⟩

/-- Generalization to arbitrary $n \in N$: multiplying $g \in C(w)$ by any element of $N$
lands in some Bruhat cell, by induction on a simple-reflection word for $\pi(n)$. -/
lemma bruhatCell_mul_N (bp : BNPair G M) (ax : BNPairAxioms bp)
    {w : M.Group} {g : G} (hg : g ∈ bp.bruhatCell w)
    (n : bp.N) : ∃ u : M.Group, g * (n : G) ∈ bp.bruhatCell u := by

  let cs := M.toCoxeterSystem
  have hgen : Subgroup.closure (Set.range cs.simple) = ⊤ :=
    cs.subgroup_closure_range_simple

  have hπn_mem : bp.π n ∈ Subgroup.closure (Set.range cs.simple) :=
    hgen ▸ Subgroup.mem_top _


  suffices ∀ (w' : M.Group), w' ∈ Subgroup.closure (Set.range cs.simple) →
      ∀ (w₀ : M.Group) (g₀ : G), g₀ ∈ bp.bruhatCell w₀ →
      ∀ (m : bp.N), bp.π m = w' → ∃ u, g₀ * (m : G) ∈ bp.bruhatCell u by
    exact this (bp.π n) hπn_mem w g hg n rfl
  intro w' hw'

  refine Subgroup.closure_induction_right
    (p := fun (w' : M.Group) _ => ∀ (w₀ : M.Group) (g₀ : G), g₀ ∈ bp.bruhatCell w₀ →
      ∀ (m : bp.N), bp.π m = w' → ∃ u, g₀ * (m : G) ∈ bp.bruhatCell u)
    ?one ?mul_right ?mul_inv hw'
  ·
    intro w₀ g₀ hg₀ m hm
    have m_in_T : (m : G) ∈ bp.T := (bp.π_ker m).mp hm
    have m_in_B : (m : G) ∈ bp.B := by
      rw [bp.T_eq] at m_in_T; exact (Subgroup.mem_inf.mp m_in_T).1
    exact ⟨w₀, bruhatCell_mul_B_right bp hg₀ m_in_B⟩
  ·
    intro w' hw' si hsi IH w₀ g₀ hg₀ m hm

    obtain ⟨i, rfl⟩ := hsi

    obtain ⟨n_s, hn_s⟩ := bp.π_surj (cs.simple i)

    have hπ_mn : bp.π (m * n_s⁻¹) = w' := by
      rw [map_mul, map_inv, hm, hn_s]
      group

    obtain ⟨u, hu⟩ := IH w₀ g₀ hg₀ (m * n_s⁻¹) hπ_mn

    have key : g₀ * (m : G) = g₀ * ((m * n_s⁻¹ : bp.N) : G) * (n_s : G) := by
      simp [Subgroup.coe_mul]; group
    rw [key]

    exact bruhatCell_mul_N_simple bp ax hu hn_s
  ·

    intro w' hw' si hsi IH w₀ g₀ hg₀ m hm
    obtain ⟨i, rfl⟩ := hsi

    have simple_inv : (cs.simple i)⁻¹ = cs.simple i := by
      have h := cs.simple_mul_simple_cancel_left (w := 1) i
      rw [mul_one] at h
      exact inv_eq_of_mul_eq_one_right h

    obtain ⟨n_s, hn_s⟩ := bp.π_surj (cs.simple i)

    have hπ_mn : bp.π (m * n_s) = w' := by
      rw [map_mul, hm, hn_s, simple_inv, cs.simple_mul_simple_cancel_right]

    obtain ⟨u, hu⟩ := IH w₀ g₀ hg₀ (m * n_s) hπ_mn

    have key : g₀ * (m : G) = g₀ * ((m * n_s : bp.N) : G) * (n_s : G)⁻¹ := by
      simp [Subgroup.coe_mul]; group
    rw [key]

    have hn_s_inv : bp.π (n_s⁻¹) = cs.simple i := by
      rw [map_inv, hn_s, simple_inv]
    exact bruhatCell_mul_N_simple bp ax hu hn_s_inv

/-- *Bruhat cell cover*: $G = \bigcup_{w \in W} BwB$. Every element of $G$ lies in some
Bruhat cell, proven by induction on a generating word in $B \cup N$. -/
theorem cell_cover_from_bnpair {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (ax : BNPairAxioms bp) :
    ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w := by
  intro g

  have hg_mem : g ∈ Subgroup.closure ((bp.B : Set G) ∪ (bp.N : Set G)) :=
    bp.generates ▸ Subgroup.mem_top g

  refine Subgroup.closure_induction_right
    (s := (bp.B : Set G) ∪ (bp.N : Set G))
    (p := fun g _ => ∃ w : M.Group, g ∈ bp.bruhatCell w)
    ?one ?mul_right ?mul_inv hg_mem
  ·
    exact ⟨1, B_mem_bruhatCell_one bp bp.B.one_mem⟩
  ·
    intro x hx y hy ⟨w, hw⟩
    rcases hy with hy_B | hy_N
    ·
      exact ⟨w, bruhatCell_mul_B_right bp hw hy_B⟩
    ·
      exact bruhatCell_mul_N bp ax hw ⟨y, hy_N⟩
  ·
    intro x hx y hy ⟨w, hw⟩
    rcases hy with hy_B | hy_N
    ·
      exact ⟨w, bruhatCell_mul_B_right bp hw (bp.B.inv_mem hy_B)⟩
    ·
      exact bruhatCell_mul_N bp ax hw ⟨y⁻¹, bp.N.inv_mem hy_N⟩

end CellCover
