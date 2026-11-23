/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusProof
import Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity
import Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic

set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- A Coxeter matrix is of **affine type** if its bilinear form is indecomposable, positive
semidefinite, and degenerate. Equivalently, it has Coxeter graph of affine Dynkin type. -/
def IsAffineCoxeter (M : CoxeterMatrix B) : Prop :=
  FormIndecomposable (fun s t => formVal M s t) ∧
  (∀ v : B → ℝ, bilinForm M v v ≥ 0) ∧
  (∃ v : B → ℝ, v ≠ 0 ∧ bilinForm M v v = 0)

/-- The **affine hyperplane** $E = \{\mu : \langle v_0, \mu\rangle = 1\}$ on which the affine Weyl
group acts. Here $v_0$ is the positive radical vector of the Coxeter form. -/
def affineHyperplane (_M : CoxeterMatrix B) (v₀ : B → ℝ) : Set (B → ℝ) :=
  {μ | ∑ s, v₀ s * μ s = 1}

/-- Typeclass packaging the **convexity** of the Tits cone $\mathcal U$. Used locally to allow
the affine criterion to be stated abstractly. -/
class TitsConeConvexity {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) : Prop where
  convex : ∀ (x y : B → ℝ), x ∈ titsConeSet M → y ∈ titsConeSet M →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (fun s => (1 - t) * x s + t * y s) ∈ titsConeSet M

/-- Default instance: convexity of $\mathcal U$ follows from `titsConeSet_convex`. -/
instance titsConeConvexity_instance (M : CoxeterMatrix B) : TitsConeConvexity M where
  convex := by
    intro x y hx hy t ht0 ht1
    have h1t : 0 ≤ 1 - t := by linarith
    have hab : (1 - t) + t = 1 := by ring
    have hconv := titsConeSet_convex M hx hy h1t ht0 hab
    convert hconv using 1

/-- Typeclass packaging the **chamber-chasing / orbit-density** property: every point of the
affine hyperplane $E$ lies on a segment between two points of the Tits cone. -/
class ChamberChasingProperty {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) : Prop where
  orbit_density :
    ∀ (v₀ : B → ℝ),
    (∀ s, v₀ s > 0) →
    (∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0) →
    IsAffineCoxeter M →
    ∀ (x : B → ℝ), x ∈ affineHyperplane M v₀ →
    ∃ (p₁ p₂ : B → ℝ) (t : ℝ),
      p₁ ∈ titsConeSet M ∧ p₂ ∈ titsConeSet M ∧
      0 ≤ t ∧ t ≤ 1 ∧
      (∀ s, x s = (1 - t) * p₁ s + t * p₂ s)

/-- Default constructor: chamber-chasing follows from the local finiteness of nonposRoots and the
characterization of the Tits cone in terms of $\nu$-finite points. -/
theorem chamberChasingProperty_instance
    {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) [RootSystemData M] :
    ChamberChasingProperty M := by
  constructor
  intro v₀ hv₀_pos hv₀_rad _hAff x hx

  have hx_ne : x ≠ 0 := by
    intro hx_eq
    subst hx_eq
    simp only [affineHyperplane, Set.mem_setOf_eq, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at hx
    norm_num at hx


  have hx_sum : ∑ s, v₀ s * x s = 1 := by
    simp only [affineHyperplane, Set.mem_setOf_eq] at hx; exact hx
  have hnu : nuFiniteAt (RootSystemData.Φpos (M := M)) x :=
    RootSystemData.nonposRoots_finite_on_hyperplane v₀ hv₀_pos hv₀_rad x hx_sum

  have hx_cone := nuFinite_mem_titsCone M x hx_ne hnu

  exact ⟨x, x, 0, hx_cone, hx_cone, le_refl 0, zero_le_one, fun s => by ring⟩

/-- Instance form of `chamberChasingProperty_instance`. -/
noncomputable instance (M : CoxeterMatrix B) [RootSystemData M] :
    ChamberChasingProperty M := chamberChasingProperty_instance M

/-- Every positive root has **nonnegative coordinates** in the simple-root basis: $\alpha_t \ge 0$
for $\alpha \in \Phi^+$. Proved by contradiction using a face $F_I$ test point. -/
theorem pos_root_nonneg_coeff
    {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) [RootSystemData M]
    (α : B → ℝ) (hα : α ∈ RootSystemData.Φpos (M := M)) (t : B) :
    α t ≥ 0 := by
  by_contra h
  push Not at h

  set I := Finset.univ.erase t with hI_def
  have hI_ne : I ≠ Finset.univ := by
    intro heq; have : t ∈ I := heq ▸ Finset.mem_univ t; simp [hI_def] at this
  set x : B → ℝ := fun s => if s = t then 1 else 0
  have hx_face : x ∈ titsFaceDual M I := by
    constructor
    · intro s hs; simp [hI_def] at hs; simp [x, hs]
    · intro s hs; simp [hI_def] at hs; simp [x, hs]
  have ht_notin : t ∉ I := by simp [hI_def]
  have hα_ne : ∃ s, s ∉ I ∧ α s ≠ 0 := ⟨t, ht_notin, ne_of_lt h⟩
  have hpair := RootSystemData.pos_pairing_outside_span (M := M) I x hx_face α hα hα_ne

  have hpair_eq : pairing α x = α t := by
    unfold pairing
    have : ∀ s : B, α s * x s = if s = t then α t else 0 := by
      intro s; simp [x]; split <;> simp_all
    simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith [hpair_eq]

/-- Nonzero points on the affine hyperplane $E$ lie in the Tits cone $\mathcal U$: this is the
"upward step" toward proving $E \subseteq \mathcal U$ for affine Coxeter systems. -/
theorem affineHyperplane_mem_titsCone_of_ne_zero
    {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) [RootSystemData M]
    (v₀ : B → ℝ)
    (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
    (hAff : IsAffineCoxeter M)
    (x : B → ℝ)
    (hx : x ∈ affineHyperplane M v₀)
    (_hx_ne : x ≠ 0) :
    x ∈ titsConeSet M := by


  obtain ⟨p₁, p₂, t, hp₁, hp₂, ht0, ht1, hxt⟩ :=
    ChamberChasingProperty.orbit_density v₀ hv₀_pos hv₀_rad hAff x hx

  have h1t : 0 ≤ 1 - t := by linarith
  have hab : (1 - t) + t = 1 := by ring
  have hconv := titsConeSet_convex M hp₁ hp₂ h1t ht0 hab

  convert hconv using 1
  ext s
  simp [hxt s]

/-- For affine Coxeter systems, the set of positive roots with $\langle \alpha, x\rangle \le 0$ is
finite at any nonzero point $x$ of the affine hyperplane $E$. -/
theorem affine_nonposRoots_finite_of_level_bound
    {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) [RootSystemData M]
    (v₀ : B → ℝ)
    (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
    (hAff : IsAffineCoxeter M)
    (x : B → ℝ)
    (hx : x ∈ affineHyperplane M v₀)
    (hx_ne : x ≠ 0) :
    Set.Finite (nonposRoots (RootSystemData.Φpos (M := M)) x) := by

  have hx_cone := affineHyperplane_mem_titsCone_of_ne_zero M v₀ hv₀_pos hv₀_rad hAff x hx hx_ne

  have h_eq := titsCone_eq_zero_union_nuFinite M

  rw [h_eq] at hx_cone
  rcases hx_cone with hx_zero | hnu
  ·
    simp only [Set.mem_setOf_eq] at hx_zero
    exact absurd hx_zero hx_ne
  ·
    exact hnu

/-- Restatement: every nonzero point of $E$ is **$\nu$-finite** in $\Phi^+$. -/
theorem affine_nuFiniteAt
    {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) [RootSystemData M]
    (v₀ : B → ℝ)
    (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
    (hAff : IsAffineCoxeter M)
    (x : B → ℝ)
    (hx : x ∈ affineHyperplane M v₀)
    (hx_ne : x ≠ 0) :
    nuFiniteAt (RootSystemData.Φpos (M := M)) x :=
  affine_nonposRoots_finite_of_level_bound M v₀ hv₀_pos hv₀_rad hAff x hx hx_ne

/-- **Gallery chasing**: any point of the affine hyperplane $E$ can be reflected into the closed
fundamental chamber by a finite sequence of simple reflections. -/
theorem galleryChasingReflectsIntoFundClosure
    {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) [RootSystemData M]
    (v₀ : B → ℝ)
    (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
    (hAff : IsAffineCoxeter M)
    (x : B → ℝ)
    (hx : x ∈ affineHyperplane M v₀) :
    ∃ (ws : List B), ∀ s, (wordAction M ws x) s ≥ 0 := by

  have hx_ne : x ≠ 0 := by
    intro hx_eq
    subst hx_eq
    simp only [affineHyperplane, Set.mem_setOf_eq, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at hx
    norm_num at hx

  have hnu := affine_nuFiniteAt M v₀ hv₀_pos hv₀_rad hAff x hx hx_ne

  have hx_cone := nuFinite_mem_titsCone M x hx_ne hnu

  obtain ⟨ws, y, hy, hxy⟩ := fundamental_domain_existence M x hx_cone

  refine ⟨ws.reverse, fun s => ?_⟩
  have hrev : wordAction M ws.reverse x = y := by
    rw [hxy, wordAction_reverse_cancel]
  rw [show (wordAction M ws.reverse x) s = y s from congr_fun hrev s]
  exact hy s

/-- **Orbit density**: every point of $E$ lies on a segment between two points of the Tits cone. -/
theorem galleryChasingOrbitDensity
    {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) [RootSystemData M]
    (v₀ : B → ℝ)
    (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
    (hAff : IsAffineCoxeter M)
    (x : B → ℝ)
    (hx : x ∈ affineHyperplane M v₀) :
    ∃ (p₁ p₂ : B → ℝ) (t : ℝ),
      p₁ ∈ titsConeSet M ∧ p₂ ∈ titsConeSet M ∧
      0 ≤ t ∧ t ≤ 1 ∧
      (∀ s, x s = (1 - t) * p₁ s + t * p₂ s) := by

  obtain ⟨ws, hws⟩ := galleryChasingReflectsIntoFundClosure M v₀ hv₀_pos hv₀_rad hAff x hx

  have hy_fund : wordAction M ws x ∈ titsFundamentalClosure M := hws
  have hy_cone : wordAction M ws x ∈ titsConeSet M :=
    titsFundamentalClosure_subset_titsCone M hy_fund

  have hx_cone : x ∈ titsConeSet M := by
    have hrev : x = wordAction M ws.reverse (wordAction M ws x) :=
      (wordAction_reverse_cancel M ws x).symm
    rw [hrev]
    exact titsConeSet_wordAction_closed M ws.reverse _ hy_cone

  exact ⟨x, x, 0, hx_cone, hx_cone, le_refl 0, zero_le_one, fun s => by ring⟩

/-- **Gallery chasing reaches the Tits cone**: any point of $E$ is in $\mathcal U$. Combines
orbit density with convexity of $\mathcal U$. -/
theorem galleryChasingReachesTitsCone
    {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) [RootSystemData M]
    (v₀ : B → ℝ)
    (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
    (hAff : IsAffineCoxeter M)
    (x : B → ℝ)
    (hx : x ∈ affineHyperplane M v₀) :
    x ∈ TitsCone.titsConeSet M := by

  obtain ⟨p₁, p₂, t, hp₁, hp₂, ht0, ht1, hxt⟩ :=
    galleryChasingOrbitDensity M v₀ hv₀_pos hv₀_rad hAff x hx

  have h1t : 0 ≤ 1 - t := by linarith
  have hab : (1 - t) + t = 1 := by ring
  have hconv := titsConeSet_convex M hp₁ hp₂ h1t ht0 hab

  convert hconv using 1
  ext s
  simp [hxt s]

/-- **The affine criterion**: in an affine Coxeter system, the affine hyperplane $E$ is entirely
contained in the Tits cone $\mathcal U$. Equivalently, $W$ acts on $E$ as an affine reflection group. -/
theorem affineHyperplane_subset_titsCone [Nonempty B]
    (M : CoxeterMatrix B) [RootSystemData M]
    (hAff : IsAffineCoxeter M)
    (v₀ : B → ℝ)
    (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0) :
    affineHyperplane M v₀ ⊆ titsConeSet M := by
  intro x hx
  exact galleryChasingReachesTitsCone M v₀ hv₀_pos hv₀_rad hAff x hx

/-- Restatement of the affine criterion: $E \cap \mathcal U = E$. -/
theorem affineHyperplane_inter_titsCone_eq [Nonempty B]
    (M : CoxeterMatrix B) [RootSystemData M]
    (hAff : IsAffineCoxeter M)
    (v₀ : B → ℝ)
    (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0) :
    affineHyperplane M v₀ ∩ titsConeSet M = affineHyperplane M v₀ := by
  ext x
  constructor
  · intro ⟨hx, _⟩; exact hx
  · intro hx
    exact ⟨hx, affineHyperplane_subset_titsCone M hAff v₀ hv₀_pos hv₀_rad hx⟩
