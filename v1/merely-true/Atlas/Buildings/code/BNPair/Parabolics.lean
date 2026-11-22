/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.BruhatPropertiesInstance

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} [DecidableEq B_idx] [Fintype B_idx]
  {M : CoxeterMatrix B_idx}

namespace BNPair

/-- Axiomless form of `standardParabolicInjective`: distinct subsets $S_1, S_2 \subseteq S$
yield distinct standard parabolics $P_{S_1} \ne P_{S_2}$, derived directly from the
BN-pair axioms (via `BruhatProperties.fromAxioms`). -/
noncomputable def standardParabolicInjective'
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (S₁ S₂ : Set B_idx)
    (h : bp.standardParabolic S₁ = bp.standardParabolic S₂) : S₁ = S₂ :=
  standardParabolicInjective bp (BruhatProperties.fromAxioms bp ax) S₁ S₂ h

/-- Axiomless form of `parabolicsAreSubgroups`: each $P_{S'}$ contains $1$ and is closed
under multiplication and inverses, derived from the BN-pair axioms alone. -/
noncomputable def parabolicsAreSubgroups'
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (S' : Set B_idx) :
    (1 : G) ∈ bp.standardParabolic S' ∧
    (∀ x y, x ∈ bp.standardParabolic S' → y ∈ bp.standardParabolic S' →
      x * y ∈ bp.standardParabolic S') ∧
    (∀ x, x ∈ bp.standardParabolic S' → x⁻¹ ∈ bp.standardParabolic S') :=
  parabolicsAreSubgroups bp (BruhatProperties.fromAxioms bp ax) S'

/-- Every Borel subgroup $B$ is contained in any standard parabolic $P_{S'}$:
since $1 \in W_{S'}$, the cell $B \cdot 1 \cdot B = B$ sits inside $P_{S'} = BW_{S'}B$. -/
theorem parabolicsContainB'
    (bp : BNPair G M) (S' : Set B_idx) :
    (bp.B : Set G) ⊆ bp.standardParabolic S' := by
  intro b hb
  rw [standardParabolic, Set.mem_iUnion₂]

  refine ⟨1, (bp.parabolicSubgroupW S').one_mem, ?_⟩


  obtain ⟨n₀, hn₀⟩ := bp.π_surj (1 : M.Group)
  have n₀_in_T : (n₀ : G) ∈ bp.T := (bp.π_ker n₀).mp hn₀
  have n₀_in_B : (n₀ : G) ∈ bp.B := by
    rw [bp.T_eq] at n₀_in_T; exact (Subgroup.mem_inf.mp n₀_in_T).1
  exact ⟨⟨b * (↑n₀)⁻¹, bp.B.mul_mem hb (bp.B.inv_mem n₀_in_B)⟩,
         n₀,
         ⟨1, bp.B.one_mem⟩,
         hn₀,
         by simp⟩

/-- **Classification of subgroups containing $B$.** Every subgroup $P \leq G$ with
$B \leq P$ equals some standard parabolic $P_{S'}$, where
$S' = \{s \in S : BsB \subseteq P\}$. Derived directly from the BN-pair axioms. -/
noncomputable def subgroupsOverB_eq_parabolic'
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (P : Subgroup G) (hBP : bp.B ≤ P) :
    ∃ S' : Set B_idx, (P : Set G) = bp.standardParabolic S' :=
  SubgroupOverB.subgroup_over_B_eq_parabolic_from_bnpair bp ax P hBP

/-- **Standard parabolics are self-normalizing** (axiomless form). If $g \in G$ normalizes
$P_{S'}$ in the sense $gP_{S'}g^{-1} = P_{S'}$, then $g \in P_{S'}$.
That is, $N_G(P_{S'}) = P_{S'}$. -/
noncomputable def parabolicSelfNormalizing'
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (S' : Set B_idx) (g : G)
    (hnorm : ∀ x, x ∈ bp.standardParabolic S' ↔
      g * x * g⁻¹ ∈ bp.standardParabolic S') :
    g ∈ bp.standardParabolic S' :=
  (BruhatProperties.fromAxioms bp ax).normalizer_in_parabolic S' g hnorm

/-- **No two distinct standard parabolics are conjugate** (axiomless form).
If $gP_{S_1}g^{-1} = P_{S_2}$ for some $g \in G$, then $S_1 = S_2$.
Equivalently, distinct subsets $S_1 \ne S_2$ of the simple roots give parabolics that
are not even conjugate in $G$. -/
noncomputable def parabolicsNotConjugate'
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (S₁ S₂ : Set B_idx) (g : G)
    (hconj : (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ =
      bp.standardParabolic S₂) :
    S₁ = S₂ := by
  let bd := BruhatProperties.fromAxioms bp ax

  have hg_S2 : g ∈ bp.standardParabolic S₂ :=
    bd.conjugator_in_target S₁ S₂ g hconj

  have PS1_subgp := parabolicsAreSubgroups bp bd S₁
  have PS1_eq_PS2 : bp.standardParabolic S₁ = bp.standardParabolic S₂ :=
    conj_image_eq (bp.standardParabolic S₁) (bp.standardParabolic S₂) g
      hg_S2 PS1_subgp.2.1 PS1_subgp.2.2 hconj

  exact standardParabolicInjective bp bd S₁ S₂ PS1_eq_PS2

/-- Convenience alias: $B \subseteq P_{S'}$ for every $S' \subseteq S$. -/
theorem parabolicsContainB (bp : BNPair G M) (S' : Set B_idx) :
    (bp.B : Set G) ⊆ bp.standardParabolic S' :=
  parabolicsContainB' bp S'

/-- Convenience alias for `subgroupsOverB_eq_parabolic'`: every subgroup containing $B$
is a standard parabolic. -/
noncomputable def subgroupsOverB_eq_parabolic
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (P : Subgroup G) (hBP : bp.B ≤ P) :
    ∃ S' : Set B_idx, (P : Set G) = bp.standardParabolic S' :=
  subgroupsOverB_eq_parabolic' bp ax P hBP

/-- Convenience alias: standard parabolics are self-normalizing, $N_G(P_{S'}) = P_{S'}$. -/
noncomputable def parabolicSelfNormalizing
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (S' : Set B_idx) (g : G)
    (hnorm : ∀ x, x ∈ bp.standardParabolic S' ↔
      g * x * g⁻¹ ∈ bp.standardParabolic S') :
    g ∈ bp.standardParabolic S' :=
  parabolicSelfNormalizing' bp ax S' g hnorm

/-- Convenience alias: distinct standard parabolics are not $G$-conjugate. -/
noncomputable def parabolicsNotConjugate
    (bp : BNPair G M) (ax : BNPairAxioms bp)
    (S₁ S₂ : Set B_idx) (g : G)
    (hconj : (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ =
      bp.standardParabolic S₂) :
    S₁ = S₂ :=
  parabolicsNotConjugate' bp ax S₁ S₂ g hconj

end BNPair
