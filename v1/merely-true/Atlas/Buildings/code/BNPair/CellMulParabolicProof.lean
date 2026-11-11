/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Atlas.Buildings.code.BNPair.ParabolicDefs
import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

namespace CellMulParabolic

open BNPair

/-- Right $B$-absorption: $C(w) \cdot B \subseteq C(w)$. -/
lemma bruhatCell_mul_B_right (bp : BNPair G M) {w : M.Group} {g b : G}
    (hg : g ∈ bp.bruhatCell w) (hb : b ∈ bp.B) :
    g * b ∈ bp.bruhatCell w := by
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  exact ⟨⟨b₁, hb₁⟩, n, ⟨b₂ * b, bp.B.mul_mem hb₂ hb⟩, hπ, by rw [hg_eq]; group⟩

/-- Left $B$-absorption: $B \cdot C(w) \subseteq C(w)$. -/
lemma bruhatCell_mul_B_left (bp : BNPair G M) {w : M.Group} {g b : G}
    (hb : b ∈ bp.B) (hg : g ∈ bp.bruhatCell w) :
    b * g ∈ bp.bruhatCell w := by
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  exact ⟨⟨b * b₁, bp.B.mul_mem hb hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, by rw [hg_eq]; group⟩

/-- Single-simple step: if $w \in W_{S'}$ and $s \in S'$, then for $g_1 \in C(w)$ and $g_2 \in C(s)$
the product $g_1 g_2$ lies in some $C(u)$ with $u \in W_{S'}$. -/
lemma cell_mul_simple_in_parabolic (bp : BNPair G M) (ax : BNPairAxioms bp)
    (S' : Set B_idx) (w : M.Group) (s : B_idx) (hs : s ∈ S')
    (hw : w ∈ bp.parabolicSubgroupW S')
    (g₁ g₂ : G) (hg₁ : g₁ ∈ bp.bruhatCell w)
    (hg₂ : g₂ ∈ bp.bruhatCell (M.toCoxeterSystem.simple s)) :
    ∃ u ∈ (bp.parabolicSubgroupW S' : Set M.Group),
      g₁ * g₂ ∈ bp.bruhatCell u := by
  let cs := M.toCoxeterSystem

  have prod_in_setMul : g₁ * g₂ ∈ setMul (bp.bruhatCell w)
      (bp.bruhatCell (cs.simple s)) :=
    ⟨g₁, hg₁, g₂, hg₂, rfl⟩

  have hs_mem : cs.simple s ∈ bp.parabolicSubgroupW S' :=
    Subgroup.subset_closure ⟨s, hs, rfl⟩
  rcases cs.length_mul_simple w s with hlen | hlen
  ·
    have hgt : cs.length (w * cs.simple s) > cs.length w := by omega
    exact ⟨w * cs.simple s,
      (bp.parabolicSubgroupW S').mul_mem hw hs_mem,
      ax.cell_mul_length_increasing w s hgt prod_in_setMul⟩
  ·
    have hlt : cs.length (w * cs.simple s) < cs.length w := by omega
    have h := ax.cell_mul_length_decreasing w s hlt prod_in_setMul
    rcases h with h | h
    · exact ⟨w * cs.simple s,
        (bp.parabolicSubgroupW S').mul_mem hw hs_mem, h⟩
    · exact ⟨w, hw, h⟩

/-- *Closure of Bruhat cells under multiplication within a parabolic*: if $w, w' \in W_{S'}$
and $g_i \in C(w_i)$, then $g_1 g_2 \in C(u)$ for some $u \in W_{S'}$.
This shows $\bigcup_{w \in W_{S'}} C(w) = P_{S'}$ is a subgroup. -/
theorem cell_mul_in_parabolic_from_bnpair {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (S' : Set B_idx) (w w' : M.Group)
    (hw : w ∈ bp.parabolicSubgroupW S') (hw' : w' ∈ bp.parabolicSubgroupW S')
    (g₁ g₂ : G) (hg₁ : g₁ ∈ bp.bruhatCell w) (hg₂ : g₂ ∈ bp.bruhatCell w') :
    ∃ u ∈ (bp.parabolicSubgroupW S' : Set M.Group), g₁ * g₂ ∈ bp.bruhatCell u := by
  let cs := M.toCoxeterSystem


  suffices ∀ (w' : M.Group), w' ∈ Subgroup.closure (cs.simple '' S') →
      ∀ (w₀ : M.Group), w₀ ∈ bp.parabolicSubgroupW S' →
      ∀ (g₁ g₂ : G), g₁ ∈ bp.bruhatCell w₀ → g₂ ∈ bp.bruhatCell w' →
      ∃ u ∈ (bp.parabolicSubgroupW S' : Set M.Group), g₁ * g₂ ∈ bp.bruhatCell u by
    exact this w' hw' w hw g₁ g₂ hg₁ hg₂
  intro w'₀ hw'₀

  refine Subgroup.closure_induction_right
    (p := fun (w'₀ : M.Group) _ =>
      ∀ (w₀ : M.Group), w₀ ∈ bp.parabolicSubgroupW S' →
      ∀ (g₁ g₂ : G), g₁ ∈ bp.bruhatCell w₀ → g₂ ∈ bp.bruhatCell w'₀ →
      ∃ u ∈ (bp.parabolicSubgroupW S' : Set M.Group), g₁ * g₂ ∈ bp.bruhatCell u)
    ?one ?mul_right ?mul_inv hw'₀
  ·


    intro w₀ hw₀ g₁' g₂' hg₁' hg₂'

    obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπn, hg₂'_eq⟩ := hg₂'

    have n_in_T : (n : G) ∈ bp.T := (bp.π_ker n).mp hπn
    have n_in_B : (n : G) ∈ bp.B := by
      rw [bp.T_eq] at n_in_T; exact (Subgroup.mem_inf.mp n_in_T).1

    have g₂'_in_B : g₂' ∈ bp.B := by
      rw [hg₂'_eq]; exact bp.B.mul_mem (bp.B.mul_mem hb₁ n_in_B) hb₂

    exact ⟨w₀, hw₀, bruhatCell_mul_B_right bp hg₁' g₂'_in_B⟩
  ·
    intro w'₁ hw'₁ si hsi IH

    obtain ⟨s, hs, rfl⟩ := hsi

    intro w₀ hw₀ g₁' g₂' hg₁' hg₂'


    obtain ⟨⟨b₁_g₂, hb₁_g₂⟩, n_g₂, ⟨b₂_g₂, hb₂_g₂⟩, hπ_g₂, hg₂'_eq⟩ := hg₂'

    obtain ⟨n_s, hn_s⟩ := bp.π_surj (cs.simple s)


    have simple_inv : (cs.simple s)⁻¹ = cs.simple s := by
      have h := cs.simple_mul_simple_cancel_left (w := 1) s
      rw [mul_one] at h
      exact inv_eq_of_mul_eq_one_right h
    have hπ_n' : bp.π (n_g₂ * n_s⁻¹) = w'₁ := by
      rw [map_mul, map_inv, hπ_g₂, hn_s]
      group


    set g₂_first : G := b₁_g₂ * (↑(n_g₂ * n_s⁻¹) : G) * 1
    have hg₂_first : g₂_first ∈ bp.bruhatCell w'₁ :=
      ⟨⟨b₁_g₂, hb₁_g₂⟩, n_g₂ * n_s⁻¹, ⟨1, bp.B.one_mem⟩, hπ_n', by simp [g₂_first]⟩


    set g_s : G := 1 * (↑n_s : G) * b₂_g₂
    have hg_s : g_s ∈ bp.bruhatCell (cs.simple s) :=
      ⟨⟨1, bp.B.one_mem⟩, n_s, ⟨b₂_g₂, hb₂_g₂⟩, hn_s, by simp [g_s]⟩


    have hg₂'_factor : g₂' = g₂_first * g_s := by
      simp only [g₂_first, g_s, mul_one, one_mul]
      rw [hg₂'_eq]
      simp [Subgroup.coe_mul]

      group


    obtain ⟨u, hu, h_prod⟩ := IH w₀ hw₀ g₁' g₂_first hg₁' hg₂_first


    rw [hg₂'_factor, ← mul_assoc]
    exact cell_mul_simple_in_parabolic bp ax S' u s hs hu
      (g₁' * g₂_first) g_s h_prod hg_s

  ·

    intro w'₁ hw'₁ si hsi IH
    obtain ⟨s, hs, rfl⟩ := hsi
    intro w₀ hw₀ g₁' g₂' hg₁' hg₂'

    have simple_inv : (cs.simple s)⁻¹ = cs.simple s := by
      have h := cs.simple_mul_simple_cancel_left (w := 1) s
      rw [mul_one] at h
      exact inv_eq_of_mul_eq_one_right h


    obtain ⟨⟨b₁_g₂, hb₁_g₂⟩, n_g₂, ⟨b₂_g₂, hb₂_g₂⟩, hπ_g₂, hg₂'_eq⟩ := hg₂'

    have hπ_g₂' : bp.π n_g₂ = w'₁ * cs.simple s := by
      rw [hπ_g₂, simple_inv]


    obtain ⟨n_s, hn_s⟩ := bp.π_surj (cs.simple s)


    have hπ_n' : bp.π (n_g₂ * n_s⁻¹) = w'₁ := by
      rw [map_mul, map_inv, hπ_g₂', hn_s]
      group


    set g₂_first : G := b₁_g₂ * (↑(n_g₂ * n_s⁻¹) : G) * 1
    have hg₂_first : g₂_first ∈ bp.bruhatCell w'₁ :=
      ⟨⟨b₁_g₂, hb₁_g₂⟩, n_g₂ * n_s⁻¹, ⟨1, bp.B.one_mem⟩, hπ_n', by simp [g₂_first]⟩

    set g_s : G := 1 * (↑n_s : G) * b₂_g₂
    have hg_s : g_s ∈ bp.bruhatCell (cs.simple s) :=
      ⟨⟨1, bp.B.one_mem⟩, n_s, ⟨b₂_g₂, hb₂_g₂⟩, hn_s, by simp [g_s]⟩

    have hg₂'_factor : g₂' = g₂_first * g_s := by
      simp only [g₂_first, g_s, mul_one, one_mul]
      rw [hg₂'_eq]
      simp [Subgroup.coe_mul]

      group

    obtain ⟨u, hu, h_prod⟩ := IH w₀ hw₀ g₁' g₂_first hg₁' hg₂_first

    rw [hg₂'_factor, ← mul_assoc]
    exact cell_mul_simple_in_parabolic bp ax S' u s hs hu
      (g₁' * g₂_first) g_s h_prod hg_s

end CellMulParabolic
