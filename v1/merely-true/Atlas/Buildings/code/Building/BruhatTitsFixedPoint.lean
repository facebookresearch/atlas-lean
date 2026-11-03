/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt

set_option maxHeartbeats 400000

open Set Filter Topology

noncomputable section

variable {M : Type*} [MetricSpace M]

/-- CAT(0)/negative curvature inequality on a metric space $M$: for every pair $x, y \in M$ there
exists a midpoint $m$ such that for all $z$,
$d(z, m)^2 \leq \tfrac{1}{2} d(z, x)^2 + \tfrac{1}{2} d(z, y)^2 - \tfrac{1}{4} d(x, y)^2$. -/
def NegativeCurvatureInequality (M : Type*) [MetricSpace M] : Prop :=
  ∀ x y : M, ∃ m : M, ∀ z : M,
    dist z m ^ 2 ≤ (1 / 2) * dist z x ^ 2 + (1 / 2) * dist z y ^ 2 - (1 / 4) * dist x y ^ 2

/-- Radius of the set $Y$ as seen from the point $x$: $\sup_{y \in Y} d(x, y)$. -/
def radiusFrom (x : M) (Y : Set M) : ℝ :=
  ⨆ y : Y, dist x (y : M)

/-- Circumradius of $Y$: $\inf_{x \in M} \sup_{y \in Y} d(x, y)$. -/
def circumradius (Y : Set M) : ℝ :=
  ⨅ x : M, radiusFrom x Y

/-- $x$ is a circumcenter of $Y$ iff its enclosing radius equals the circumradius of $Y$. -/
def IsCircumcenter (x : M) (Y : Set M) : Prop :=
  radiusFrom x Y = circumradius Y

/-- An isometric action of a group $G$ on a metric space $M$: a scalar multiplication
respecting the group identity, composition, and acting by isometries on $M$. -/
structure IsometricAction (G : Type*) [Group G] (M : Type*) [MetricSpace M] where
  smul : G → M → M
  smul_one : ∀ x : M, smul 1 x = x
  smul_mul : ∀ (g h : G) (x : M), smul (g * h) x = smul g (smul h x)
  isometry_smul : ∀ g : G, Isometry (smul g)

/-- A subset $Y \subseteq M$ is stable under the isometric action iff $g \cdot Y \subseteq Y$ for
every $g \in G$. -/
def IsometricAction.IsStable {G : Type*} [Group G] (act : IsometricAction G M)
    (Y : Set M) : Prop :=
  ∀ g : G, ∀ y ∈ Y, act.smul g y ∈ Y

/-- $x$ is a fixed point of the isometric action iff $g \cdot x = x$ for all $g \in G$. -/
def IsometricAction.IsFixedPoint {G : Type*} [Group G] (act : IsometricAction G M)
    (x : M) : Prop :=
  ∀ g : G, act.smul g x = x

/-- The radius from a point is nonnegative. -/
lemma radiusFrom_nonneg (x : M) (Y : Set M) : 0 ≤ radiusFrom x Y := by
  unfold radiusFrom
  exact Real.sSup_nonneg (by rintro _ ⟨⟨_, _⟩, rfl⟩; exact dist_nonneg)

/-- For bounded $Y$, the set of distances from $x$ to elements of $Y$ is bounded above. -/
lemma bddAbove_dist_range (x : M) (Y : Set M) (hbd : Bornology.IsBounded Y) :
    BddAbove (range (fun (y : Y) => dist x (y : M))) := by
  obtain ⟨r, hr⟩ := hbd.subset_ball x
  refine ⟨r, ?_⟩
  rintro _ ⟨⟨y, hy⟩, rfl⟩
  simp only
  have := Metric.mem_ball.mp (hr hy)
  linarith [dist_comm x y]

/-- Any point of a bounded set $Y$ lies within `radiusFrom x Y` from $x$. -/
lemma dist_le_radiusFrom (x : M) {Y : Set M} (hbd : Bornology.IsBounded Y)
    {y : M} (hy : y ∈ Y) : dist x y ≤ radiusFrom x Y :=
  le_ciSup (bddAbove_dist_range x Y hbd) ⟨y, hy⟩

/-- The circumradius is nonnegative. -/
lemma circumradius_nonneg (Y : Set M) : 0 ≤ circumradius Y := by
  unfold circumradius
  show 0 ≤ sInf (range (fun x => radiusFrom x Y))
  exact Real.sInf_nonneg (by rintro _ ⟨x, rfl⟩; exact radiusFrom_nonneg x Y)

/-- The circumradius is a lower bound for `radiusFrom x Y` at every $x$. -/
lemma circumradius_le_radiusFrom (x : M) (Y : Set M) :
    circumradius Y ≤ radiusFrom x Y :=
  ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact radiusFrom_nonneg z Y⟩ x

/-- Isometries preserve `radiusFrom`: if $\varphi$ is an isometry then
`radiusFrom (φ x) (φ '' Y) = radiusFrom x Y`. -/
theorem isometry_radiusFrom_eq
    (φ : M → M) (hφ : Isometry φ) (x : M) (Y : Set M) :
    radiusFrom (φ x) (φ '' Y) = radiusFrom x Y := by
  unfold radiusFrom
  show sSup (range (fun (z : ↥(φ '' Y)) => dist (φ x) (z : M))) =
    sSup (range (fun (y : ↥Y) => dist x (y : M)))
  congr 1
  ext d; simp only [mem_range, Subtype.exists]
  constructor
  · rintro ⟨z, hz, rfl⟩; obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, hy, (hφ.dist_eq x y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨φ y, mem_image_of_mem φ hy, hφ.dist_eq x y⟩

/-- **Existence of circumcenters in CAT(0) spaces**: in a complete metric space satisfying the
negative curvature inequality, every nonempty bounded subset $Y$ has a circumcenter $c \in M$. -/
theorem circumcenter_exists (M : Type*) [MetricSpace M] [CompleteSpace M]
    (hNCI : NegativeCurvatureInequality M) (Y : Set M)
    (hne : Y.Nonempty) (hbd : Bornology.IsBounded Y) :
    ∃ c : M, IsCircumcenter c Y := by
  obtain ⟨y₀, hy₀⟩ := hne
  haveI : Nonempty M := ⟨y₀⟩
  haveI : Nonempty ↥Y := ⟨⟨y₀, hy₀⟩⟩
  set r := circumradius Y with hr_def
  have hr_nn : 0 ≤ r := circumradius_nonneg Y

  have hmini : ∀ n : ℕ, ∃ x : M, radiusFrom x Y < r + 1 / ((n : ℝ) + 1) := by
    intro n; apply exists_lt_of_ciInf_lt
    show (⨅ x : M, radiusFrom x Y) < r + 1 / ((n : ℝ) + 1)
    simp only [hr_def, circumradius]
    linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
  choose xseq hxseq using hmini

  have hdist_bound : ∀ i j : ℕ, dist (xseq i) (xseq j) ^ 2 ≤
      2 * (r + 1 / ((i : ℝ) + 1)) ^ 2 + 2 * (r + 1 / ((j : ℝ) + 1)) ^ 2 - 4 * r ^ 2 := by
    intro i j
    obtain ⟨mid, hmid⟩ := hNCI (xseq i) (xseq j)
    have bound : ∀ y ∈ Y, dist y mid ^ 2 ≤
        (1/2) * (r + 1/((i : ℝ)+1))^2 + (1/2) * (r + 1/((j : ℝ)+1))^2 -
        (1/4) * dist (xseq i) (xseq j) ^ 2 := by
      intro y hy
      have h1 : dist y (xseq i) ≤ r + 1/((i : ℝ)+1) := by
        calc dist y (xseq i) = dist (xseq i) y := dist_comm _ _
          _ ≤ radiusFrom (xseq i) Y := dist_le_radiusFrom _ hbd hy
          _ ≤ r + 1/((i : ℝ)+1) := le_of_lt (hxseq i)
      have h2 : dist y (xseq j) ≤ r + 1/((j : ℝ)+1) := by
        calc dist y (xseq j) = dist (xseq j) y := dist_comm _ _
          _ ≤ radiusFrom (xseq j) Y := dist_le_radiusFrom _ hbd hy
          _ ≤ r + 1/((j : ℝ)+1) := le_of_lt (hxseq j)
      nlinarith [hmid y, sq_nonneg (r + 1/((i:ℝ)+1) - dist y (xseq i)),
        sq_nonneg (r + 1/((j:ℝ)+1) - dist y (xseq j)),
        @dist_nonneg M _ y (xseq i), @dist_nonneg M _ y (xseq j)]
    have hnn : 0 ≤ (1/2) * (r + 1/((i : ℝ)+1))^2 + (1/2) * (r + 1/((j : ℝ)+1))^2 -
        (1/4) * dist (xseq i) (xseq j) ^ 2 := by
      nlinarith [bound y₀ hy₀, sq_nonneg (dist y₀ mid)]
    have hrad_mid : radiusFrom mid Y ≤ Real.sqrt ((1/2) * (r + 1/((i : ℝ)+1))^2 +
        (1/2) * (r + 1/((j : ℝ)+1))^2 - (1/4) * dist (xseq i) (xseq j) ^ 2) := by
      unfold radiusFrom; apply ciSup_le; intro ⟨y, hy⟩
      rw [Real.le_sqrt dist_nonneg hnn, dist_comm]; exact bound y hy
    have hcr_mid : r ≤ radiusFrom mid Y := circumradius_le_radiusFrom mid Y
    have h_comb := le_trans hcr_mid hrad_mid
    rw [Real.le_sqrt hr_nn hnn] at h_comb
    nlinarith

  have hcauchy : CauchySeq xseq := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
    obtain ⟨N, hN⟩ := exists_nat_gt ((8 * r + 4) / ε ^ 2)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [show ε = Real.sqrt (ε ^ 2) by rw [Real.sqrt_sq (le_of_lt hε)]]
    rw [← Real.sqrt_sq dist_nonneg]
    apply Real.sqrt_lt_sqrt (sq_nonneg _)
    have hm_le : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity)
      exact_mod_cast Nat.succ_le_succ hm
    have hn_le : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity)
      exact_mod_cast Nat.succ_le_succ hn
    have diff_m : (1/((N:ℝ)+1) - 1/((m:ℝ)+1)) * (2*r + 1/((N:ℝ)+1) + 1/((m:ℝ)+1)) ≥ 0 := by
      apply mul_nonneg <;> [linarith; positivity]
    have diff_n : (1/((N:ℝ)+1) - 1/((n:ℝ)+1)) * (2*r + 1/((N:ℝ)+1) + 1/((n:ℝ)+1)) ≥ 0 := by
      apply mul_nonneg <;> [linarith; positivity]
    calc dist (xseq m) (xseq n) ^ 2
        ≤ 2 * (r + 1/((m : ℝ)+1))^2 + 2 * (r + 1/((n : ℝ)+1))^2 - 4 * r^2 := hdist_bound m n
      _ ≤ 2 * (r + 1/((N : ℝ)+1))^2 + 2 * (r + 1/((N : ℝ)+1))^2 - 4 * r^2 := by nlinarith
      _ = 4 * (r + 1/((N : ℝ)+1))^2 - 4 * r^2 := by ring
      _ < ε ^ 2 := by
          have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
          have key : 8 * r + 4 < (N : ℝ) * ε ^ 2 := by rwa [div_lt_iff₀ hε2] at hN
          have expand : 4 * (r + 1 / ((N : ℝ) + 1)) ^ 2 - 4 * r ^ 2 =
              (8 * r * ((N : ℝ) + 1) + 4) / ((N : ℝ) + 1) ^ 2 := by field_simp; ring
          rw [expand, div_lt_iff₀ (by positivity : (0:ℝ) < ((N : ℝ) + 1) ^ 2)]
          nlinarith [sq_nonneg ((N : ℝ) + 1), sq_nonneg (N : ℝ)]

  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy

  refine ⟨c, ?_⟩
  unfold IsCircumcenter
  apply le_antisymm
  ·
    unfold radiusFrom; apply ciSup_le; intro ⟨y, hy⟩

    exact le_of_tendsto_of_tendsto
      (hc.dist tendsto_const_nhds)
      (by have h := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
          have := Filter.Tendsto.add (show Tendsto (fun _ : ℕ => r) atTop (nhds r) from
            tendsto_const_nhds) h
          rwa [add_zero] at this)
      (Filter.Eventually.of_forall fun n => le_of_lt (calc
        dist (xseq n) y ≤ radiusFrom (xseq n) Y := dist_le_radiusFrom _ hbd hy
        _ < r + 1 / ((n : ℝ) + 1) := hxseq n))
  ·
    exact circumradius_le_radiusFrom c Y

/-- **Uniqueness of circumcenters in CAT(0) spaces**: any two circumcenters $c_1, c_2$ of a
nonempty bounded set $Y$ in a CAT(0) metric space coincide. -/
theorem circumcenter_unique (M : Type*) [MetricSpace M]
    (hNCI : NegativeCurvatureInequality M) (Y : Set M)
    (hne : Y.Nonempty) (hbd : Bornology.IsBounded Y)
    (c₁ c₂ : M) (h₁ : IsCircumcenter c₁ Y) (h₂ : IsCircumcenter c₂ Y) :
    c₁ = c₂ := by
  by_contra hne_pts
  obtain ⟨y₀, hy₀⟩ := hne
  haveI : Nonempty ↥Y := ⟨⟨y₀, hy₀⟩⟩
  set r := circumradius Y
  have hr_nn : 0 ≤ r := circumradius_nonneg Y
  have hd : 0 < dist c₁ c₂ := dist_pos.mpr hne_pts
  obtain ⟨mid, hmid⟩ := hNCI c₁ c₂
  have hc1 : ∀ y ∈ Y, dist y c₁ ≤ r := fun y hy => by
    rw [dist_comm]; exact le_trans (dist_le_radiusFrom c₁ hbd hy) (le_of_eq h₁)
  have hc2 : ∀ y ∈ Y, dist y c₂ ≤ r := fun y hy => by
    rw [dist_comm]; exact le_trans (dist_le_radiusFrom c₂ hbd hy) (le_of_eq h₂)
  have hbd_mid : ∀ y ∈ Y, dist y mid ^ 2 ≤ r ^ 2 - (1/4) * dist c₁ c₂ ^ 2 := by
    intro y hy
    have sq1 : dist y c₁ ^ 2 ≤ r ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (hc1 y hy) (@dist_nonneg M _ y c₁)]
    have sq2 : dist y c₂ ^ 2 ≤ r ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (hc2 y hy) (@dist_nonneg M _ y c₂)]
    nlinarith [hmid y]
  have hnn : 0 ≤ r ^ 2 - (1/4) * dist c₁ c₂ ^ 2 := by
    nlinarith [hbd_mid y₀ hy₀, sq_nonneg (dist y₀ mid)]
  have hrf_mid : radiusFrom mid Y ≤ Real.sqrt (r ^ 2 - (1/4) * dist c₁ c₂ ^ 2) := by
    unfold radiusFrom; apply ciSup_le; intro ⟨y, hy⟩
    rw [Real.le_sqrt dist_nonneg hnn, dist_comm]; exact hbd_mid y hy
  have hr_le : r ≤ radiusFrom mid Y := circumradius_le_radiusFrom mid Y
  have : r ≤ Real.sqrt (r ^ 2 - (1/4) * dist c₁ c₂ ^ 2) := le_trans hr_le hrf_mid
  rw [Real.le_sqrt hr_nn hnn] at this
  nlinarith [sq_nonneg (dist c₁ c₂)]

/-- If $Y$ is stable under the action then $g \cdot Y = Y$ as a set. -/
lemma stable_image_eq {G : Type*} [Group G] (act : IsometricAction G M)
    (Y : Set M) (hstab : act.IsStable Y) (g : G) : act.smul g '' Y = Y := by
  ext z; constructor
  · rintro ⟨y, hy, rfl⟩; exact hstab g y hy
  · intro hz
    refine ⟨act.smul g⁻¹ z, hstab g⁻¹ z hz, ?_⟩
    rw [← act.smul_mul, mul_inv_cancel, act.smul_one]

/-- **Bruhat–Tits fixed point theorem**: a group $G$ acting isometrically on a complete CAT(0)
metric space $M$ and stabilizing some nonempty bounded subset $Y$ admits a global fixed point
$x \in M$. The fixed point is the (unique) circumcenter of $Y$. -/
theorem BruhatTitsFixedPoint (M : Type*) [MetricSpace M] [CompleteSpace M]
    (hNCI : NegativeCurvatureInequality M)
    (G : Type*) [Group G] (act : IsometricAction G M)
    (Y : Set M) (hne : Y.Nonempty) (hbd : Bornology.IsBounded Y)
    (hstab : act.IsStable Y) :
    ∃ x : M, act.IsFixedPoint x := by
  obtain ⟨c, hc⟩ := circumcenter_exists M hNCI Y hne hbd
  refine ⟨c, fun g => ?_⟩

  have hgc : IsCircumcenter (act.smul g c) Y := by
    unfold IsCircumcenter
    calc radiusFrom (act.smul g c) Y
        = radiusFrom (act.smul g c) (act.smul g '' Y) := by
          rw [stable_image_eq act Y hstab g]
      _ = radiusFrom c Y := isometry_radiusFrom_eq (act.smul g) (act.isometry_smul g) c Y
      _ = circumradius Y := hc
  exact (circumcenter_unique M hNCI Y hne hbd c (act.smul g c) hc hgc).symm

end
