/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.BruhatTitsFixedPoint
import Atlas.Buildings.code.Building.CompactSubgroups
import Atlas.Buildings.code.BNPair.Generalized.Defs

set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

open Set

/-- Restrict an isometric action of $G$ on $X$ to an action of a subgroup
$K \leq G$. -/
def restrictIsometricAction {G : Type*} [Group G] {X : Type*} [MetricSpace X]
    (act : IsometricAction G X) (K : Subgroup G) : IsometricAction K X where
  smul := fun ⟨g, _⟩ x => act.smul g x
  smul_one := by
    intro x; show act.smul (1 : G) x = x; exact act.smul_one x
  smul_mul := by
    intro ⟨g, _⟩ ⟨h, _⟩ x
    show act.smul (g * h) x = act.smul g (act.smul h x)
    exact act.smul_mul g h x
  isometry_smul := by
    intro ⟨g, _⟩; exact act.isometry_smul g

namespace FixedPointSubgroups

variable {Gt : Type*} [Group Gt] {X : Type*} [MetricSpace X]

/-- The orbit $E \cdot x = \{g \cdot x \mid g \in E\}$ of a point $x$ under
a subset $E$ of the group. -/
def orbitSet (act : IsometricAction Gt X)
    (E : Set Gt) (x : X) : Set X :=
  { y : X | ∃ g ∈ E, act.smul g x = y }

/-- The image $E \cdot Y = \{g \cdot y \mid g \in E,\, y \in Y\}$ of a
subset $Y \subseteq X$ under a subset $E$ of the group. -/
def actionOnSet (act : IsometricAction Gt X)
    (E : Set Gt) (Y : Set X) : Set X :=
  { z : X | ∃ g ∈ E, ∃ y ∈ Y, act.smul g y = z }

/-- The stabilizer subgroup $\mathrm{Stab}(x) = \{g \in G \mid g \cdot x = x\}$
of a point $x \in X$. -/
def pointStabilizer (act : IsometricAction Gt X)
    (x : X) : Subgroup Gt where
  carrier := { g : Gt | act.smul g x = x }
  mul_mem' := by
    intro a b ha hb
    show act.smul (a * b) x = x
    rw [act.smul_mul, hb, ha]
  one_mem' := act.smul_one x
  inv_mem' := by
    intro a ha
    show act.smul a⁻¹ x = x
    have h1 : act.smul a⁻¹ (act.smul a x) = act.smul (a⁻¹ * a) x :=
      (act.smul_mul a⁻¹ a x).symm
    rw [inv_mul_cancel] at h1
    rw [act.smul_one] at h1
    rw [ha] at h1
    exact h1

/-- A package of data and axioms needed to relate bounded subgroups of a
group $G^t$ acting on a $\mathrm{CAT}(0)$ space $X$ to point stabilizers:
an isometric action satisfying the negative-curvature inequality, a
generalised BN-pair, a group bornology, a base chamber point, and
compatibility axioms ensuring boundedness is equivalent to having a bounded
orbit. -/
structure BuildingGroupContext (Gt : Type*) [Group Gt] (B_idx : Type*)
    (M : CoxeterMatrix B_idx) where
  X : Type*
  [metricSpace : MetricSpace X]
  [completeSpace : CompleteSpace X]
  [nonempty : Nonempty X]
  nci : NegativeCurvatureInequality X
  action : IsometricAction Gt X
  gbnpair : GeneralizedBNPair Gt M
  bruhatProps : BNPair.BruhatProperties gbnpair.strictBNPair
  born : CompactSubgroups.GroupBornology Gt
  chamber_point : X
  borel_fixes_chamber_point :
    ∀ (b : Gt), b ∈ gbnpair.strictBNPair.B.map gbnpair.G.subtype →
      action.smul b chamber_point = chamber_point
  Tt_fixes_chamber_point :
    ∀ (t : Gt), t ∈ gbnpair.Tt → action.smul t chamber_point = chamber_point
  born_bounded_orbit_at_chamber_point :
    ∀ (E : Set Gt), born.isBounded E →
      Bornology.IsBounded (orbitSet action E chamber_point)
  orbit_bounded_at_chamber_point_born_bounded :
    ∀ (E : Set Gt), Bornology.IsBounded (orbitSet action E chamber_point) →
      born.isBounded E
  Tt_in_every_maximal_bounded :
    ∀ (K : Subgroup Gt), CompactSubgroups.IsMaximalBounded born K →
      ∀ (t : Gt), t ∈ gbnpair.Tt → t ∈ K
  stabilizer_of_bounded_orbit :
    ∀ (x : X) (H : Subgroup Gt),
      pointStabilizer action x ≤ H →
      Bornology.IsBounded (orbitSet action (H : Set Gt) x) →
      H ≤ pointStabilizer action x

attribute [instance] BuildingGroupContext.metricSpace BuildingGroupContext.completeSpace
  BuildingGroupContext.nonempty

/-- The orbit of $x$ under a subgroup $K$ is non-empty (it contains $x$ itself). -/
theorem orbit_nonempty (act : IsometricAction Gt X)
    (K : Subgroup Gt) (x : X) :
    (orbitSet act (K : Set Gt) x).Nonempty :=
  ⟨x, 1, K.one_mem, act.smul_one x⟩

/-- The orbit $K \cdot x$ is stable under the restricted action of $K$ on $X$. -/
theorem orbit_stable_restricted (act : IsometricAction Gt X)
    (K : Subgroup Gt) (x : X) :
    (restrictIsometricAction act K).IsStable (orbitSet act (K : Set Gt) x) := by
  intro ⟨g, hg⟩ y hy
  obtain ⟨k, hk, rfl⟩ := hy
  exact ⟨g * k, K.mul_mem hg hk, act.smul_mul g k x⟩

/-- If $x_0$ is a fixed point of the restricted action of $K$, then $K$ is
contained in the stabilizer of $x_0$. -/
theorem subgroup_le_stabilizer_of_restricted_fixed (act : IsometricAction Gt X)
    (K : Subgroup Gt) (x₀ : X)
    (hfix : (restrictIsometricAction act K).IsFixedPoint x₀) :
    K ≤ pointStabilizer act x₀ := by
  intro g hg
  exact hfix ⟨g, hg⟩

/-- The orbit of $x$ under its stabilizer is exactly $\{x\}$. -/
theorem stabilizer_orbit_eq_singleton (act : IsometricAction Gt X)
    (x : X) :
    orbitSet act (pointStabilizer act x : Set Gt) x = {x} := by
  ext y
  constructor
  ·
    rintro ⟨g, hg, rfl⟩
    simp only [mem_singleton_iff]
    exact hg
  ·
    intro hy
    rw [mem_singleton_iff] at hy
    subst hy
    exact ⟨1, (pointStabilizer act y).one_mem, act.smul_one y⟩

/-- If a subset $E \subseteq G^t$ is bounded with respect to the group
bornology, then its orbit $E \cdot x$ is bounded in $X$ for every point $x$. -/
theorem born_bounded_orbit_bounded
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (E : Set Gt) (hE : ctx.born.isBounded E) (x : ctx.X) :
    Bornology.IsBounded (orbitSet ctx.action E x) := by

  have h_cp := ctx.born_bounded_orbit_at_chamber_point E hE

  obtain ⟨R, hR⟩ := h_cp.subset_closedBall ctx.chamber_point
  rw [Metric.isBounded_iff_subset_closedBall x]
  refine ⟨R + dist ctx.chamber_point x + dist ctx.chamber_point x, ?_⟩
  intro z hz
  obtain ⟨g, hg, rfl⟩ := hz
  simp only [Metric.mem_closedBall]
  have h1 : dist (ctx.action.smul g ctx.chamber_point) ctx.chamber_point ≤ R :=
    hR ⟨g, hg, rfl⟩

  have h_tri : dist (ctx.action.smul g ctx.chamber_point) x ≤
      dist (ctx.action.smul g ctx.chamber_point) ctx.chamber_point +
        dist ctx.chamber_point x := dist_triangle _ _ _
  calc dist (ctx.action.smul g x) x
      ≤ dist (ctx.action.smul g x) (ctx.action.smul g ctx.chamber_point) +
        dist (ctx.action.smul g ctx.chamber_point) x := dist_triangle _ _ _
    _ = dist x ctx.chamber_point +
        dist (ctx.action.smul g ctx.chamber_point) x :=
        by rw [(ctx.action.isometry_smul g).dist_eq]
    _ ≤ dist x ctx.chamber_point +
        (dist (ctx.action.smul g ctx.chamber_point) ctx.chamber_point +
         dist ctx.chamber_point x) := by linarith
    _ ≤ dist ctx.chamber_point x + (R + dist ctx.chamber_point x) := by
        rw [dist_comm x ctx.chamber_point]; linarith
    _ = R + dist ctx.chamber_point x + dist ctx.chamber_point x := by ring

/-- Converse: if some orbit $E \cdot x$ is bounded in $X$, then $E$ itself
is bounded in the group bornology. -/
theorem orbit_bounded_born_bounded
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (E : Set Gt) (h : ∃ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x)) :
    ctx.born.isBounded E := by
  obtain ⟨x, hx⟩ := h

  apply ctx.orbit_bounded_at_chamber_point_born_bounded
  obtain ⟨R, hR⟩ := hx.subset_closedBall x
  rw [Metric.isBounded_iff_subset_closedBall ctx.chamber_point]
  refine ⟨R + dist x ctx.chamber_point + dist x ctx.chamber_point, ?_⟩
  intro z hz
  obtain ⟨g, hg, rfl⟩ := hz
  simp only [Metric.mem_closedBall]
  have h1 : dist (ctx.action.smul g x) x ≤ R := by
    have := hR ⟨g, hg, rfl⟩
    simp only [Metric.mem_closedBall] at this
    exact this
  calc dist (ctx.action.smul g ctx.chamber_point) ctx.chamber_point
      ≤ dist (ctx.action.smul g ctx.chamber_point) (ctx.action.smul g x) +
        dist (ctx.action.smul g x) ctx.chamber_point := dist_triangle _ _ _
    _ = dist ctx.chamber_point x +
        dist (ctx.action.smul g x) ctx.chamber_point :=
        by rw [(ctx.action.isometry_smul g).dist_eq]
    _ ≤ dist ctx.chamber_point x +
        (dist (ctx.action.smul g x) x + dist x ctx.chamber_point) := by
        linarith [dist_triangle (ctx.action.smul g x) x ctx.chamber_point]
    _ ≤ dist x ctx.chamber_point + (R + dist x ctx.chamber_point) := by
        rw [dist_comm ctx.chamber_point x]; linarith
    _ = R + dist x ctx.chamber_point + dist x ctx.chamber_point := by ring

/-- Maximality of stabilizers: any strictly larger subgroup $H$ than
$\mathrm{Stab}(x)$ fails to be bounded. -/
theorem stabilizer_maximal_born_ax
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (x : ctx.X) (H : Subgroup Gt) :
    pointStabilizer ctx.action x < H → ¬ctx.born.isBounded (H : Set Gt) := by
  intro hlt hbdd

  have h_orbit_bdd : Bornology.IsBounded (orbitSet ctx.action (H : Set Gt) x) :=
    born_bounded_orbit_bounded ctx (H : Set Gt) hbdd x


  have h_le : H ≤ pointStabilizer ctx.action x :=
    ctx.stabilizer_of_bounded_orbit x H hlt.le h_orbit_bdd


  exact absurd (le_antisymm hlt.le h_le) (ne_of_lt hlt)

/-- If $K$ is a maximal bounded subgroup and $k = \sigma g$ with $\sigma$
in the small torus $T^t$, then $g \in K$ — left factors from $T^t$ can be
absorbed into $K$. -/
theorem decomp_stable_in_stabilizer
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (K : Subgroup Gt) (hK : CompactSubgroups.IsMaximalBounded ctx.born K)
    (σ : Gt) (hσ : σ ∈ ctx.gbnpair.Tt) (g : Gt) (_hg : g ∈ ctx.gbnpair.G)
    (k : Gt) (hk : k ∈ K) (hk_eq : k = σ * g) : g ∈ K := by

  have hσ_K : σ ∈ K := ctx.Tt_in_every_maximal_bounded K hK σ hσ

  have hg_eq : g = σ⁻¹ * k := by
    rw [hk_eq]; group
  rw [hg_eq]
  exact K.mul_mem (K.inv_mem hσ_K) hk

/-- Every point stabilizer is bounded in the group bornology. -/
theorem stabilizer_born_bounded_thm
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (x : ctx.X) :
    ctx.born.isBounded (pointStabilizer ctx.action x : Set Gt) := by
  apply orbit_bounded_born_bounded ctx
  refine ⟨x, ?_⟩
  rw [stabilizer_orbit_eq_singleton]
  exact Bornology.isBounded_singleton

/-- If both $E \cdot x_0$ and a set $Y$ are bounded, then the action set
$E \cdot Y$ is bounded as well. -/
theorem orbit_bounded_implies_action_bounded
    {Gt : Type*} [Group Gt] {X : Type*} [MetricSpace X]
    (act : IsometricAction Gt X)
    (E : Set Gt) (x₀ : X)
    (h_orbit_bdd : Bornology.IsBounded (orbitSet act E x₀))
    (Y : Set X) (hY : Bornology.IsBounded Y) :
    Bornology.IsBounded (actionOnSet act E Y) := by
  obtain ⟨δ, hδ⟩ := h_orbit_bdd.subset_closedBall x₀
  obtain ⟨D, hD⟩ := hY.subset_closedBall x₀
  rw [Metric.isBounded_iff_subset_closedBall x₀]
  refine ⟨δ + D, ?_⟩
  intro z hz
  obtain ⟨g, hg, y, hy, rfl⟩ := hz
  simp only [Metric.mem_closedBall] at *
  have h1 : dist (act.smul g x₀) x₀ ≤ δ := hδ ⟨g, hg, rfl⟩
  have h2 : dist y x₀ ≤ D := hD hy
  calc dist (act.smul g y) x₀
      ≤ dist (act.smul g y) (act.smul g x₀) + dist (act.smul g x₀) x₀ := dist_triangle _ _ _
    _ = dist y x₀ + dist (act.smul g x₀) x₀ := by rw [(act.isometry_smul g).dist_eq]
    _ ≤ D + δ := by linarith
    _ = δ + D := by ring

/-- Acting on the singleton $\{x\}$ recovers the orbit $E \cdot x$. -/
theorem actionOnSet_singleton (act : IsometricAction Gt X)
    (E : Set Gt) (x : X) :
    actionOnSet act E {x} = orbitSet act E x := by
  ext z
  simp only [actionOnSet, orbitSet, mem_setOf_eq, mem_singleton_iff]
  constructor
  · rintro ⟨g, hg, y, rfl, heq⟩; exact ⟨g, hg, heq⟩
  · rintro ⟨g, hg, heq⟩; exact ⟨g, hg, x, rfl, heq⟩

/-- A cyclic equivalence of three notions of boundedness for a subset
$E \subseteq G^t$: boundedness in the group bornology, having a bounded
orbit, and producing only bounded images of bounded subsets of $X$. -/
theorem BoundedSubsetsEquivalence
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (E : Set Gt) :
    (ctx.born.isBounded E →
      ∀ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x)) ∧
    ((∃ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x)) →
      ∀ Y : Set ctx.X, Bornology.IsBounded Y →
        Bornology.IsBounded (actionOnSet ctx.action E Y)) ∧
    ((∀ Y : Set ctx.X, Bornology.IsBounded Y →
        Bornology.IsBounded (actionOnSet ctx.action E Y)) →
      ctx.born.isBounded E) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    exact born_bounded_orbit_bounded ctx E
  ·

    intro ⟨x₀, hx₀⟩ Y hY
    exact orbit_bounded_implies_action_bounded ctx.action E x₀ hx₀ Y hY
  ·

    intro h_all_bounded
    apply orbit_bounded_born_bounded ctx

    obtain ⟨x₀⟩ := ctx.nonempty
    refine ⟨x₀, ?_⟩
    rw [← actionOnSet_singleton]
    exact h_all_bounded {x₀} Bornology.isBounded_singleton

/-- Every point stabilizer $\mathrm{Stab}(x_0)$ is a maximal bounded subgroup
in the group bornology. -/
theorem stabilizer_is_maximal_bounded
    {Gt : Type*} [Group Gt] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (x₀ : ctx.X) :
    CompactSubgroups.IsMaximalBounded ctx.born (pointStabilizer ctx.action x₀) := by
  constructor
  ·
    exact stabilizer_born_bounded_thm ctx x₀
  ·
    exact stabilizer_maximal_born_ax ctx x₀

/-- Restatement of `decomp_stable_in_stabilizer` in the finite-type
$B_{\mathrm{idx}}$ setting: $T^t$-factors can be absorbed into a maximal
bounded subgroup. -/
theorem stabilizer_Gt_decomp_mem_right
    {Gt : Type*} [Group Gt] {B_idx : Type*} [Fintype B_idx] [DecidableEq B_idx]
    {M : CoxeterMatrix B_idx}
    (ctx : BuildingGroupContext Gt B_idx M)
    (K : Subgroup Gt) (hK : CompactSubgroups.IsMaximalBounded ctx.born K)
    (σ : Gt) (hσ : σ ∈ ctx.gbnpair.Tt) (g : Gt) (hg : g ∈ ctx.gbnpair.G)
    (k : Gt) (hk : k ∈ K) (hk_eq : k = σ * g) : g ∈ K :=
  decomp_stable_in_stabilizer ctx K hK σ hσ g hg k hk hk_eq

end FixedPointSubgroups
