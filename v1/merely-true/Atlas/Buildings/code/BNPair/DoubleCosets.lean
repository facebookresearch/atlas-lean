/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.FurtherBruhatTits
import Atlas.Buildings.code.BNPair.BruhatPropertiesInstance
import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

namespace BNPair

open CellMulParabolic in

/-- The Borel $B$ is contained in every standard parabolic $P_{S'} = BW_{S'}B$, via the
trivial cell $B \cdot 1 \cdot B = B$. -/
lemma B_subset_standardParabolic (bp : BNPair G M) (S' : Set B_idx) :
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

/-- Any $N$-lift $n$ of $w = \pi(n)$ lies in its own Bruhat cell:
$n \in BnB \subseteq B \cdot n \cdot B$. -/
lemma lift_mem_bruhatCell (bp : BNPair G M) (n : bp.N) :
    (n : G) ∈ bp.bruhatCell (bp.π n) :=
  ⟨⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, rfl, by simp⟩

/-- If $w \in W_{S'}$ then the Bruhat cell $BwB$ is contained in the standard parabolic
$P_{S'} = \bigcup_{u \in W_{S'}} BuB$. -/
lemma bruhatCell_subset_standardParabolic (bp : BNPair G M) (S' : Set B_idx)
    (w : M.Group) (hw : w ∈ bp.parabolicSubgroupW S') :
    bp.bruhatCell w ⊆ bp.standardParabolic S' := fun _g hg =>
  Set.mem_iUnion₂.mpr ⟨w, hw, hg⟩

/-- Bruhat cells absorb right multiplication by $B$: if $g \in BwB$ and $b \in B$ then
$gb \in BwB$. -/
lemma bruhatCell_mul_B_right' (bp : BNPair G M) {w : M.Group} {g b : G}
    (hg : g ∈ bp.bruhatCell w) (hb : b ∈ bp.B) :
    g * b ∈ bp.bruhatCell w := by
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  exact ⟨⟨b₁, hb₁⟩, n, ⟨b₂ * b, bp.B.mul_mem hb₂ hb⟩, hπ, by rw [hg_eq]; group⟩

/-- Bruhat cells absorb left multiplication by $B$: if $b \in B$ and $g \in BwB$ then
$bg \in BwB$. -/
lemma bruhatCell_mul_B_left' (bp : BNPair G M) {w : M.Group} {g b : G}
    (hb : b ∈ bp.B) (hg : g ∈ bp.bruhatCell w) :
    b * g ∈ bp.bruhatCell w := by
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  exact ⟨⟨b * b₁, bp.B.mul_mem hb hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, by rw [hg_eq]; group⟩

/-- Simple reflections are involutions in $W$: $s^{-1} = s$ for every $s \in S$. -/
lemma simple_inv_eq (s : B_idx) :
    (M.toCoxeterSystem.simple s)⁻¹ = M.toCoxeterSystem.simple s := by
  have h := M.toCoxeterSystem.simple_mul_simple_cancel_left (w := 1) s
  rw [mul_one] at h
  exact inv_eq_of_mul_eq_one_right h

/-- Right multiplication by a single simple-reflection cell: $BvB \cdot BsB$ lands in
$Bv'B$ for some $v' = vu_2$ with $u_2 \in W_{S_2}$. The exchange condition picks either
$v' = vs$ or $v' = v$. -/
lemma cell_mul_simple_right_coset (bp : BNPair G M) (ax : BNPairAxioms bp)
    (S₂ : Set B_idx) (v : M.Group) (s : B_idx) (hs : s ∈ S₂)
    (g₁ g₂ : G) (hg₁ : g₁ ∈ bp.bruhatCell v)
    (hg₂ : g₂ ∈ bp.bruhatCell (M.toCoxeterSystem.simple s)) :
    ∃ v' : M.Group, (∃ u₂ ∈ (bp.parabolicSubgroupW S₂ : Set M.Group),
      v' = v * u₂) ∧ g₁ * g₂ ∈ bp.bruhatCell v' := by
  let cs := M.toCoxeterSystem
  have prod_in : g₁ * g₂ ∈ setMul (bp.bruhatCell v) (bp.bruhatCell (cs.simple s)) :=
    ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  have hs_mem : cs.simple s ∈ bp.parabolicSubgroupW S₂ :=
    Subgroup.subset_closure ⟨s, hs, rfl⟩
  rcases cs.length_mul_simple v s with hlen | hlen
  ·
    have hgt : cs.length (v * cs.simple s) > cs.length v := by omega
    exact ⟨v * cs.simple s,
      ⟨cs.simple s, hs_mem, rfl⟩,
      ax.cell_mul_length_increasing v s hgt prod_in⟩
  ·
    have hlt : cs.length (v * cs.simple s) < cs.length v := by omega
    rcases ax.cell_mul_length_decreasing v s hlt prod_in with h | h
    · exact ⟨v * cs.simple s,
        ⟨cs.simple s, hs_mem, rfl⟩, h⟩
    · exact ⟨v,
        ⟨1, (bp.parabolicSubgroupW S₂).one_mem, by simp⟩, h⟩

/-- **Right cell-by-coset multiplication.** For $u_2 \in W_{S_2}$, the product
$BvB \cdot Bu_2B$ is contained in $\bigcup_{u_2' \in W_{S_2}} B(vu_2')B$. Proved by
induction on a word for $u_2$ in the simple reflections of $S_2$, using
`cell_mul_simple_right_coset` at each step. -/
theorem cell_mul_right_coset (bp : BNPair G M) (ax : BNPairAxioms bp)
    (S₂ : Set B_idx) (v u₂ : M.Group)
    (hu₂ : u₂ ∈ bp.parabolicSubgroupW S₂)
    (g₁ g₂ : G) (hg₁ : g₁ ∈ bp.bruhatCell v) (hg₂ : g₂ ∈ bp.bruhatCell u₂) :
    ∃ v' : M.Group, (∃ u₂' ∈ (bp.parabolicSubgroupW S₂ : Set M.Group),
      v' = v * u₂') ∧ g₁ * g₂ ∈ bp.bruhatCell v' := by
  let cs := M.toCoxeterSystem

  suffices ∀ (u₂ : M.Group), u₂ ∈ Subgroup.closure (cs.simple '' S₂) →
      ∀ (v₀ : M.Group) (g₁ g₂ : G), g₁ ∈ bp.bruhatCell v₀ → g₂ ∈ bp.bruhatCell u₂ →
      ∃ v' : M.Group, (∃ u₂' ∈ (bp.parabolicSubgroupW S₂ : Set M.Group),
        v' = v₀ * u₂') ∧ g₁ * g₂ ∈ bp.bruhatCell v' by
    exact this u₂ hu₂ v g₁ g₂ hg₁ hg₂
  intro u₂₀ hu₂₀
  refine Subgroup.closure_induction_right
    (p := fun (u₂₀ : M.Group) _ =>
      ∀ (v₀ : M.Group) (g₁ g₂ : G), g₁ ∈ bp.bruhatCell v₀ → g₂ ∈ bp.bruhatCell u₂₀ →
      ∃ v' : M.Group, (∃ u₂' ∈ (bp.parabolicSubgroupW S₂ : Set M.Group),
        v' = v₀ * u₂') ∧ g₁ * g₂ ∈ bp.bruhatCell v')
    ?one ?mul_right ?mul_inv hu₂₀
  ·
    intro v₀ g₁' g₂' hg₁' hg₂'
    obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπn, hg₂'_eq⟩ := hg₂'
    have n_in_B : (n : G) ∈ bp.B := by
      have : (n : G) ∈ bp.T := (bp.π_ker n).mp hπn
      rw [bp.T_eq] at this; exact (Subgroup.mem_inf.mp this).1
    have g₂'_in_B : g₂' ∈ bp.B := by
      rw [hg₂'_eq]; exact bp.B.mul_mem (bp.B.mul_mem hb₁ n_in_B) hb₂
    exact ⟨v₀, ⟨1, (bp.parabolicSubgroupW S₂).one_mem, by simp⟩,
      bruhatCell_mul_B_right' bp hg₁' g₂'_in_B⟩
  ·
    intro u₂₁ hu₂₁ si hsi IH
    obtain ⟨s, hs, rfl⟩ := hsi
    intro v₀ g₁' g₂' hg₁' hg₂'

    obtain ⟨⟨b₁_g₂, hb₁_g₂⟩, n_g₂, ⟨b₂_g₂, hb₂_g₂⟩, hπ_g₂, hg₂'_eq⟩ := hg₂'
    obtain ⟨n_s, hn_s⟩ := bp.π_surj (cs.simple s)
    have hπ_n' : bp.π (n_g₂ * n_s⁻¹) = u₂₁ := by
      rw [map_mul, map_inv, hπ_g₂, hn_s]; group
    set g₂_first : G := ↑b₁_g₂ * (↑(n_g₂ * n_s⁻¹) : G) * 1
    have hg₂_first : g₂_first ∈ bp.bruhatCell u₂₁ :=
      ⟨⟨b₁_g₂, hb₁_g₂⟩, n_g₂ * n_s⁻¹, ⟨1, bp.B.one_mem⟩, hπ_n', by simp [g₂_first]⟩
    set g_s : G := 1 * (↑n_s : G) * ↑b₂_g₂
    have hg_s : g_s ∈ bp.bruhatCell (cs.simple s) :=
      ⟨⟨1, bp.B.one_mem⟩, n_s, ⟨b₂_g₂, hb₂_g₂⟩, hn_s, by simp [g_s]⟩
    have hg₂'_factor : g₂' = g₂_first * g_s := by
      simp only [g₂_first, g_s, mul_one, one_mul]
      rw [hg₂'_eq]; simp [Subgroup.coe_mul]; group

    obtain ⟨v₁, ⟨u₂'₁, hu₂'₁, hv₁_eq⟩, h_prod₁⟩ := IH v₀ g₁' g₂_first hg₁' hg₂_first

    obtain ⟨v', hv'_coset, h_prod₂⟩ :=
      cell_mul_simple_right_coset bp ax S₂ v₁ s hs
        (g₁' * g₂_first) g_s h_prod₁ hg_s
    obtain ⟨u₂'₂, hu₂'₂, hv'_eq⟩ := hv'_coset
    refine ⟨v', ⟨u₂'₁ * u₂'₂, (bp.parabolicSubgroupW S₂).mul_mem hu₂'₁ hu₂'₂, ?_⟩, ?_⟩
    · rw [hv'_eq, hv₁_eq, mul_assoc]
    · rwa [hg₂'_factor, ← mul_assoc]
  ·
    intro u₂₁ hu₂₁ si hsi IH
    obtain ⟨s, hs, rfl⟩ := hsi
    intro v₀ g₁' g₂' hg₁' hg₂'

    obtain ⟨⟨b₁_g₂, hb₁_g₂⟩, n_g₂, ⟨b₂_g₂, hb₂_g₂⟩, hπ_g₂, hg₂'_eq⟩ := hg₂'
    obtain ⟨n_s, hn_s⟩ := bp.π_surj (cs.simple s)

    have hπ_g₂' : bp.π n_g₂ = u₂₁ * cs.simple s := by
      rw [hπ_g₂, simple_inv_eq]
    have hπ_n' : bp.π (n_g₂ * n_s⁻¹) = u₂₁ := by
      rw [map_mul, map_inv, hπ_g₂', hn_s]; group
    set g₂_first : G := ↑b₁_g₂ * (↑(n_g₂ * n_s⁻¹) : G) * 1
    have hg₂_first : g₂_first ∈ bp.bruhatCell u₂₁ :=
      ⟨⟨b₁_g₂, hb₁_g₂⟩, n_g₂ * n_s⁻¹, ⟨1, bp.B.one_mem⟩, hπ_n', by simp [g₂_first]⟩
    set g_s : G := 1 * (↑n_s : G) * ↑b₂_g₂
    have hg_s : g_s ∈ bp.bruhatCell (cs.simple s) :=
      ⟨⟨1, bp.B.one_mem⟩, n_s, ⟨b₂_g₂, hb₂_g₂⟩, hn_s, by simp [g_s]⟩
    have hg₂'_factor : g₂' = g₂_first * g_s := by
      simp only [g₂_first, g_s, mul_one, one_mul]
      rw [hg₂'_eq]; simp [Subgroup.coe_mul]; group
    obtain ⟨v₁, ⟨u₂'₁, hu₂'₁, hv₁_eq⟩, h_prod₁⟩ := IH v₀ g₁' g₂_first hg₁' hg₂_first
    obtain ⟨v', hv'_coset, h_prod₂⟩ :=
      cell_mul_simple_right_coset bp ax S₂ v₁ s hs
        (g₁' * g₂_first) g_s h_prod₁ hg_s
    obtain ⟨u₂'₂, hu₂'₂, hv'_eq⟩ := hv'_coset
    exact ⟨v', ⟨u₂'₁ * u₂'₂, (bp.parabolicSubgroupW S₂).mul_mem hu₂'₁ hu₂'₂,
      by rw [hv'_eq, hv₁_eq, mul_assoc]⟩, by rwa [hg₂'_factor, ← mul_assoc]⟩

/-- Left multiplication by a simple-reflection cell: $BsB \cdot BvB$ lies in either
$B(sv)B$ or $BvB$, depending on whether $\ell(sv) > \ell(v)$. Dual to
`cell_mul_simple_right_coset`, proved by inverting and applying that result. -/
lemma cell_mul_simple_left (bp : BNPair G M) (ax : BNPairAxioms bp)
    (bd : BruhatProperties bp) (v : M.Group) (s : B_idx)
    (g₁ g₂ : G) (hg₁ : g₁ ∈ bp.bruhatCell (M.toCoxeterSystem.simple s))
    (hg₂ : g₂ ∈ bp.bruhatCell v) :
    g₁ * g₂ ∈ bp.bruhatCell (M.toCoxeterSystem.simple s * v) ∨
    g₁ * g₂ ∈ bp.bruhatCell v := by
  let cs := M.toCoxeterSystem


  have hg₂_inv : g₂⁻¹ ∈ bp.bruhatCell v⁻¹ := bd.cell_inv v g₂ hg₂
  have hs_inv : (cs.simple s)⁻¹ = cs.simple s := simple_inv_eq s
  have hg₁_inv : g₁⁻¹ ∈ bp.bruhatCell (cs.simple s) := by
    have := bd.cell_inv (cs.simple s) g₁ hg₁
    rwa [hs_inv] at this

  have prod_in : g₂⁻¹ * g₁⁻¹ ∈ setMul (bp.bruhatCell v⁻¹) (bp.bruhatCell (cs.simple s)) :=
    ⟨g₂⁻¹, hg₂_inv, g₁⁻¹, hg₁_inv, rfl⟩

  rcases cs.length_mul_simple v⁻¹ s with hlen | hlen
  ·
    have hgt : cs.length (v⁻¹ * cs.simple s) > cs.length v⁻¹ := by omega
    have h := ax.cell_mul_length_increasing v⁻¹ s hgt prod_in


    left
    have : (g₁ * g₂)⁻¹ ∈ bp.bruhatCell (v⁻¹ * cs.simple s) := by rwa [mul_inv_rev]
    have := bd.cell_inv _ _ this
    simp only [inv_inv] at this
    rwa [show (v⁻¹ * cs.simple s)⁻¹ = cs.simple s * v by rw [mul_inv_rev, inv_inv, hs_inv]] at this
  ·
    have hlt : cs.length (v⁻¹ * cs.simple s) < cs.length v⁻¹ := by omega
    rcases ax.cell_mul_length_decreasing v⁻¹ s hlt prod_in with h | h
    ·
      left
      have : (g₁ * g₂)⁻¹ ∈ bp.bruhatCell (v⁻¹ * cs.simple s) := by rwa [mul_inv_rev]
      have := bd.cell_inv _ _ this
      simp only [inv_inv] at this
      rwa [show (v⁻¹ * cs.simple s)⁻¹ = cs.simple s * v by
        rw [mul_inv_rev, inv_inv, hs_inv]] at this
    ·
      right
      have : (g₁ * g₂)⁻¹ ∈ bp.bruhatCell v⁻¹ := by rwa [mul_inv_rev]
      have := bd.cell_inv _ _ this
      simp only [inv_inv] at this
      exact this

/-- **Left cell-by-coset multiplication.** For $u_1 \in W_{S_1}$, the product
$Bu_1B \cdot BvB$ lands in $\bigcup_{u_1' \in W_{S_1}} B(u_1'v)B$. Dual to
`cell_mul_right_coset`, proved by induction on a word for $u_1$ in simple reflections. -/
theorem cell_mul_left_coset (bp : BNPair G M) (ax : BNPairAxioms bp)
    (bd : BruhatProperties bp)
    (S₁ : Set B_idx) (u₁ v : M.Group)
    (hu₁ : u₁ ∈ bp.parabolicSubgroupW S₁)
    (g₁ g₂ : G) (hg₁ : g₁ ∈ bp.bruhatCell u₁) (hg₂ : g₂ ∈ bp.bruhatCell v) :
    ∃ v' : M.Group, (∃ u₁' ∈ (bp.parabolicSubgroupW S₁ : Set M.Group),
      v' = u₁' * v) ∧ g₁ * g₂ ∈ bp.bruhatCell v' := by
  let cs := M.toCoxeterSystem
  suffices ∀ (u₁ : M.Group), u₁ ∈ Subgroup.closure (cs.simple '' S₁) →
      ∀ (v₀ : M.Group) (g₁ g₂ : G), g₁ ∈ bp.bruhatCell u₁ → g₂ ∈ bp.bruhatCell v₀ →
      ∃ v' : M.Group, (∃ u₁' ∈ (bp.parabolicSubgroupW S₁ : Set M.Group),
        v' = u₁' * v₀) ∧ g₁ * g₂ ∈ bp.bruhatCell v' by
    exact this u₁ hu₁ v g₁ g₂ hg₁ hg₂
  intro u₁₀ hu₁₀
  refine Subgroup.closure_induction_left
    (p := fun (u₁₀ : M.Group) _ =>
      ∀ (v₀ : M.Group) (g₁ g₂ : G), g₁ ∈ bp.bruhatCell u₁₀ → g₂ ∈ bp.bruhatCell v₀ →
      ∃ v' : M.Group, (∃ u₁' ∈ (bp.parabolicSubgroupW S₁ : Set M.Group),
        v' = u₁' * v₀) ∧ g₁ * g₂ ∈ bp.bruhatCell v')
    ?one ?mul_left ?inv_mul hu₁₀
  ·
    intro v₀ g₁' g₂' hg₁' hg₂'
    obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπn, hg₁'_eq⟩ := hg₁'
    have n_in_B : (n : G) ∈ bp.B := by
      have : (n : G) ∈ bp.T := (bp.π_ker n).mp hπn
      rw [bp.T_eq] at this; exact (Subgroup.mem_inf.mp this).1
    have g₁'_in_B : g₁' ∈ bp.B := by
      rw [hg₁'_eq]; exact bp.B.mul_mem (bp.B.mul_mem hb₁ n_in_B) hb₂
    exact ⟨v₀, ⟨1, (bp.parabolicSubgroupW S₁).one_mem, by simp⟩,
      bruhatCell_mul_B_left' bp g₁'_in_B hg₂'⟩
  ·

    intro si hsi u₁₁ hu₁₁ IH
    obtain ⟨s, hs, rfl⟩ := hsi
    intro v₀ g₁' g₂' hg₁' hg₂'

    obtain ⟨⟨b₁_g₁, hb₁_g₁⟩, n_g₁, ⟨b₂_g₁, hb₂_g₁⟩, hπ_g₁, hg₁'_eq⟩ := hg₁'
    obtain ⟨n_s, hn_s⟩ := bp.π_surj (cs.simple s)

    have hπ_n' : bp.π (n_s⁻¹ * n_g₁) = u₁₁ := by
      rw [map_mul, map_inv, hn_s, hπ_g₁]; group

    set g_s : G := ↑b₁_g₁ * (↑n_s : G) * 1
    have hg_s : g_s ∈ bp.bruhatCell (cs.simple s) :=
      ⟨⟨b₁_g₁, hb₁_g₁⟩, n_s, ⟨1, bp.B.one_mem⟩, hn_s, by simp [g_s]⟩
    set g₁_rest : G := 1 * (↑(n_s⁻¹ * n_g₁) : G) * ↑b₂_g₁
    have hg₁_rest : g₁_rest ∈ bp.bruhatCell u₁₁ :=
      ⟨⟨1, bp.B.one_mem⟩, n_s⁻¹ * n_g₁, ⟨b₂_g₁, hb₂_g₁⟩, hπ_n', by simp [g₁_rest]⟩
    have hg₁'_factor : g₁' = g_s * g₁_rest := by
      simp only [g_s, g₁_rest, mul_one, one_mul]
      rw [hg₁'_eq]; simp [Subgroup.coe_mul]; group

    obtain ⟨v₁, ⟨u₁'₁, hu₁'₁, hv₁_eq⟩, h_prod₁⟩ := IH v₀ g₁_rest g₂' hg₁_rest hg₂'

    rcases cell_mul_simple_left bp ax bd v₁ s g_s (g₁_rest * g₂') hg_s h_prod₁ with h | h
    ·
      refine ⟨cs.simple s * v₁,
        ⟨cs.simple s * u₁'₁,
          (bp.parabolicSubgroupW S₁).mul_mem (Subgroup.subset_closure ⟨s, hs, rfl⟩) hu₁'₁,
          by rw [hv₁_eq, mul_assoc]⟩, ?_⟩
      rwa [hg₁'_factor, mul_assoc]
    ·
      exact ⟨v₁, ⟨u₁'₁, hu₁'₁, hv₁_eq⟩, by rwa [hg₁'_factor, mul_assoc]⟩
  ·
    intro si hsi u₁₁ hu₁₁ IH
    obtain ⟨s, hs, rfl⟩ := hsi
    intro v₀ g₁' g₂' hg₁' hg₂'

    have hs_inv : (cs.simple s)⁻¹ = cs.simple s := simple_inv_eq s
    have hg₁'_cell : g₁' ∈ bp.bruhatCell (cs.simple s * u₁₁) := by
      rwa [hs_inv] at hg₁'

    obtain ⟨⟨b₁_g₁, hb₁_g₁⟩, n_g₁, ⟨b₂_g₁, hb₂_g₁⟩, hπ_g₁, hg₁'_eq⟩ := hg₁'_cell
    obtain ⟨n_s, hn_s⟩ := bp.π_surj (cs.simple s)
    have hπ_n' : bp.π (n_s⁻¹ * n_g₁) = u₁₁ := by
      rw [map_mul, map_inv, hn_s, hπ_g₁]; group
    set g_s : G := ↑b₁_g₁ * (↑n_s : G) * 1
    have hg_s : g_s ∈ bp.bruhatCell (cs.simple s) :=
      ⟨⟨b₁_g₁, hb₁_g₁⟩, n_s, ⟨1, bp.B.one_mem⟩, hn_s, by simp [g_s]⟩
    set g₁_rest : G := 1 * (↑(n_s⁻¹ * n_g₁) : G) * ↑b₂_g₁
    have hg₁_rest : g₁_rest ∈ bp.bruhatCell u₁₁ :=
      ⟨⟨1, bp.B.one_mem⟩, n_s⁻¹ * n_g₁, ⟨b₂_g₁, hb₂_g₁⟩, hπ_n', by simp [g₁_rest]⟩
    have hg₁'_factor : g₁' = g_s * g₁_rest := by
      simp only [g_s, g₁_rest, mul_one, one_mul]
      rw [hg₁'_eq]; simp [Subgroup.coe_mul]; group
    obtain ⟨v₁, ⟨u₁'₁, hu₁'₁, hv₁_eq⟩, h_prod₁⟩ := IH v₀ g₁_rest g₂' hg₁_rest hg₂'
    rcases cell_mul_simple_left bp ax bd v₁ s g_s (g₁_rest * g₂') hg_s h_prod₁ with h | h
    · exact ⟨cs.simple s * v₁,
        ⟨cs.simple s * u₁'₁,
          (bp.parabolicSubgroupW S₁).mul_mem (Subgroup.subset_closure ⟨s, hs, rfl⟩) hu₁'₁,
          by rw [hv₁_eq, mul_assoc]⟩,
        by rwa [hg₁'_factor, mul_assoc]⟩
    · exact ⟨v₁, ⟨u₁'₁, hu₁'₁, hv₁_eq⟩, by rwa [hg₁'_factor, mul_assoc]⟩

/-- **Injectivity of the double-coset map $W_{S_1} \backslash W / W_{S_2} \to
P_{S_1} \backslash G / P_{S_2}$.** If $g \in Bw'B$ also admits a factorization
$g = p_1 \cdot n \cdot p_2$ with $p_i \in P_{S_i}$ and $\pi(n) = w$, then $w'$ and $w$
represent the same $W_{S_1}\text{-}W_{S_2}$ double coset in $W$. Proved by combining
`cell_mul_right_coset` and `cell_mul_left_coset` to bring the right-hand expression into
$Bv'B$ with $v' \in W_{S_1} w W_{S_2}$, then using cell-disjointness. -/
theorem doubleCoset_injectivity (bp : BNPair G M) (ax : BNPairAxioms bp)
    (bd : BruhatProperties bp)
    (S₁ S₂ : Set B_idx) (w w' : M.Group) (g : G)
    (hg_cell : g ∈ bp.bruhatCell w')
    (hg_coset : ∃ p₁ ∈ bp.standardParabolic S₁,
      ∃ p₂ ∈ bp.standardParabolic S₂,
      ∃ n : bp.N, bp.π n = w ∧ g = p₁ * n * p₂) :
    w' ∈ bp.weylDoubleCoset S₁ S₂ w := by
  obtain ⟨p₁, hp₁, p₂, hp₂, n, hn, hg_eq⟩ := hg_coset

  rw [standardParabolic, Set.mem_iUnion₂] at hp₁
  obtain ⟨u₁, hu₁, hp₁_cell⟩ := hp₁

  rw [standardParabolic, Set.mem_iUnion₂] at hp₂
  obtain ⟨u₂, hu₂, hp₂_cell⟩ := hp₂

  have hn_cell : (n : G) ∈ bp.bruhatCell w := by
    rw [← hn]; exact lift_mem_bruhatCell bp n

  obtain ⟨v₁, ⟨u₂', hu₂', hv₁_eq⟩, h_np₂⟩ :=
    cell_mul_right_coset bp ax S₂ w u₂ hu₂ n p₂ hn_cell hp₂_cell

  obtain ⟨v', ⟨u₁', hu₁', hv'_eq⟩, h_prod⟩ :=
    cell_mul_left_coset bp ax bd S₁ u₁ v₁ hu₁ p₁ (↑n * p₂) hp₁_cell h_np₂

  have hg_in_v' : g ∈ bp.bruhatCell v' := by
    rw [hg_eq, mul_assoc]; exact h_prod

  have hw'_eq : w' = v' := bd.cell_disjoint w' v' ⟨g, hg_cell, hg_in_v'⟩

  rw [weylDoubleCoset]
  exact ⟨u₁', hu₁', u₂', hu₂', by rw [hw'_eq, hv'_eq, hv₁_eq, mul_assoc]⟩

/-- **Main theorem of §5.4 (Bourbaki):** the bijection
$W_{S_1} \backslash W / W_{S_2} \;\longleftrightarrow\; P_{S_1} \backslash G / P_{S_2}$,
sending $W_{S_1} w W_{S_2}$ to $P_{S_1} \cdot n \cdot P_{S_2}$ for any $N$-lift $n$ of $w$.
Concretely: $w' \in W_{S_1} w W_{S_2}$ iff for *every* pair of $N$-lifts $n \in \pi^{-1}(w)$,
$n' \in \pi^{-1}(w')$ we have $n' \in P_{S_1} n P_{S_2}$. The forward direction is a direct
computation using the parabolic subgroup structure; the reverse direction is
`doubleCoset_injectivity`. -/
theorem doubleCoset_bijection (bp : BNPair G M) (ax : BNPairAxioms bp)
    (bd : BruhatProperties bp)
    (S₁ S₂ : Set B_idx) (w w' : M.Group) :
    w' ∈ bp.weylDoubleCoset S₁ S₂ w ↔
    (∀ (n : bp.N), bp.π n = w →
      ∀ (n' : bp.N), bp.π n' = w' →
      (n' : G) ∈ doubleCoset (bp.standardParabolic S₁) (bp.standardParabolic S₂) n) := by
  constructor
  ·
    intro hw' n hn n' hn'
    obtain ⟨w₁, hw₁, w₂, hw₂, hw'_eq⟩ := hw'

    obtain ⟨m₁, hm₁⟩ := bp.π_surj w₁
    obtain ⟨m₂, hm₂⟩ := bp.π_surj w₂

    have hm₁_P : (m₁ : G) ∈ bp.standardParabolic S₁ :=
      bruhatCell_subset_standardParabolic bp S₁ w₁ hw₁ (hm₁ ▸ lift_mem_bruhatCell bp m₁)

    have hm₂_P : (m₂ : G) ∈ bp.standardParabolic S₂ :=
      bruhatCell_subset_standardParabolic bp S₂ w₂ hw₂ (hm₂ ▸ lift_mem_bruhatCell bp m₂)


    have hπ_prod : bp.π m₁ * bp.π n * bp.π m₂ = bp.π n' := by
      rw [hm₁, hn, hm₂, hn']; exact hw'_eq.symm

    have hπ_t : bp.π (n'⁻¹ * (m₁ * n * m₂)) = 1 := by
      simp [map_mul, map_inv]; rw [← hπ_prod]; group
    have ht_in_T : ((n'⁻¹ * (m₁ * n * m₂) : bp.N) : G) ∈ bp.T :=
      (bp.π_ker _).mp hπ_t
    have ht_in_B : ((n'⁻¹ * (m₁ * n * m₂) : bp.N) : G) ∈ bp.B := by
      rw [bp.T_eq] at ht_in_T; exact (Subgroup.mem_inf.mp ht_in_T).1


    rw [doubleCoset]


    have t_val : (n' : G)⁻¹ * ((m₁ : G) * (n : G) * (m₂ : G)) ∈ bp.B := by
      have : ((n'⁻¹ * (m₁ * n * m₂) : bp.N) : G) = (n' : G)⁻¹ * ((m₁ : G) * (n : G) * (m₂ : G)) := by
        simp [Subgroup.coe_mul]
      rwa [← this]

    have n'_eq : (n' : G) = (m₁ : G) * (n : G) * ((m₂ : G) * ((n' : G)⁻¹ * ((m₁ : G) * (n : G) * (m₂ : G)))⁻¹) := by
      group

    have hm₂t_P₂ : (m₂ : G) * ((n' : G)⁻¹ * ((m₁ : G) * (n : G) * (m₂ : G)))⁻¹ ∈
        bp.standardParabolic S₂ := by
      apply (parabolicsAreSubgroups bp bd S₂).2.1
      · exact hm₂_P
      · exact (parabolicsAreSubgroups bp bd S₂).2.2 _
          (B_subset_standardParabolic bp S₂ t_val)
    exact ⟨(m₁ : G), hm₁_P,
      (m₂ : G) * ((n' : G)⁻¹ * ((m₁ : G) * (n : G) * (m₂ : G)))⁻¹, hm₂t_P₂,
      n'_eq⟩
  ·
    intro h
    obtain ⟨n, hn⟩ := bp.π_surj w
    obtain ⟨n', hn'⟩ := bp.π_surj w'
    have h_dc := h n hn n' hn'

    obtain ⟨p₁, hp₁, p₂, hp₂, hn'_eq⟩ := h_dc

    have hn'_cell : (n' : G) ∈ bp.bruhatCell w' := by
      rw [← hn']; exact lift_mem_bruhatCell bp n'

    exact doubleCoset_injectivity bp ax bd S₁ S₂ w w' (n' : G)
      hn'_cell ⟨p₁, hp₁, p₂, hp₂, n, hn, hn'_eq⟩

end BNPair
