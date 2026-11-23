/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AffineMetric
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.InnerProductSpace.Basic

open ChamberComplex

variable {V : Type*} [DecidableEq V]

namespace AffineBuilding

/-- A geodesic segment in a building from $x$ to $y$: a set of points
characterised by satisfying the parametrised distance equations
$d(p, x) = (1-t) d(x, y)$ and $d(p, y) = t d(x, y)$ for some $t \in [0, 1]$,
together with completeness (every such point is included). -/
structure GeodesicSegment (b : Building V) (md : ApartmentMetricData b)
    (x y : V) where
  points : Set V
  endpoints : x ∈ points ∧ y ∈ points
  dist_characterization : ∀ p ∈ points, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    buildingDist b md p x = (1 - t) * buildingDist b md x y ∧
    buildingDist b md p y = t * buildingDist b md x y
  complete : ∀ p : V, (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    buildingDist b md p x = (1 - t) * buildingDist b md x y ∧
    buildingDist b md p y = t * buildingDist b md x y) → p ∈ points

/-- The building distance is non-negative. -/
lemma buildingDist_nonneg (b : Building V) (md : ApartmentMetricData b)
    (x y : V) : 0 ≤ buildingDist b md x y := by
  unfold buildingDist
  split
  · exact md.dist_nonneg _ x y
  · exact le_refl 0

/-- The building distance between two vertices that lie in a common apartment
$A$ equals the apartment distance computed in $A$. -/
lemma buildingDist_eq_dist_fn (b : Building V) (md : ApartmentMetricData b)
    (A : { A // A ∈ b.apartmentSystem.apartments }) (u v : V)
    (huA : ∃ s ∈ A.val.faces, u ∈ s) (hvA : ∃ s ∈ A.val.faces, v ∈ s) :
    buildingDist b md u v = md.dist_fn A u v := by
  unfold buildingDist
  split
  · next h =>

    exact buildingDist_well_defined_general b md h.choose A u v
      h.choose_spec.1 h.choose_spec.2 huA hvA
  · next h =>

    exact absurd ⟨A, huA, hvA⟩ h

/-- The CAT(0) negative-curvature inequality: for any point $z$ and any geodesic
parametrisation $z_t = (1-t) x + t y$ (in terms of the building distance),
$d(z, z_t)^2 \le t\, d(z, x)^2 + (1-t)\, d(z, y)^2 - t(1-t)\, d(x, y)^2$. -/
def NegCurvatureIneq (b : Building V) (md : ApartmentMetricData b) : Prop :=
  ∀ (x y z z_t : V) (t : ℝ),
    0 ≤ t → t ≤ 1 →
    buildingDist b md z_t x = (1 - t) * buildingDist b md x y →
    buildingDist b md z_t y = t * buildingDist b md x y →
    (buildingDist b md z z_t) ^ 2 ≤
      t * (buildingDist b md z x) ^ 2 +
      (1 - t) * (buildingDist b md z y) ^ 2 -
      t * (1 - t) * (buildingDist b md x y) ^ 2

/-- Parallelogram-style identity in a real inner product space: for $x, y \in E$
and $t \in \mathbb{R}$,
$\|t x + (1-t) y\|^2 = t \|x\|^2 + (1-t) \|y\|^2 - t(1-t) \|x-y\|^2$. -/
theorem euclidean_identity_ips {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (t : ℝ) :
    ‖t • x + (1 - t) • y‖ ^ 2 =
      t * ‖x‖ ^ 2 + (1 - t) * ‖y‖ ^ 2 - t * (1 - t) * ‖x - y‖ ^ 2 := by

  have hx : ‖x‖ ^ 2 = @inner ℝ E _ x x := by rw [real_inner_self_eq_norm_sq]
  have hy : ‖y‖ ^ 2 = @inner ℝ E _ y y := by rw [real_inner_self_eq_norm_sq]

  have hsymm : @inner ℝ E _ y x = @inner ℝ E _ x y := by rw [real_inner_comm]

  have hxy : ‖x - y‖ ^ 2 = @inner ℝ E _ x x - 2 * @inner ℝ E _ x y +
      @inner ℝ E _ y y := by
    rw [norm_sub_sq_real x y, hx, hy]

  have hlhs : ‖t • x + (1 - t) • y‖ ^ 2 =
      @inner ℝ E _ (t • x + (1 - t) • y) (t • x + (1 - t) • y) := by
    rw [real_inner_self_eq_norm_sq]

  rw [hlhs]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
             RCLike.conj_to_real]
  rw [hx, hy, hxy, hsymm]
  ring

/-- Origin-shifted Euclidean identity: for $z_t = t x + (1-t) y$ and any base
point $q$, $\|q - z_t\|^2 = t \|q - x\|^2 + (1-t) \|q - y\|^2 - t(1-t)\|x-y\|^2$. -/
theorem euclidean_identity_origin_shifted {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q x y z_t : E) (t : ℝ)
    (h_zt : z_t = t • x + (1 - t) • y) :
    ‖q - z_t‖ ^ 2 = t * ‖q - x‖ ^ 2 + (1 - t) * ‖q - y‖ ^ 2 -
      t * (1 - t) * ‖x - y‖ ^ 2 := by

  have key : q - z_t = -(t • (x - q) + (1 - t) • (y - q)) := by
    rw [h_zt]; simp only [smul_sub, neg_add_rev]; module
  rw [key, norm_neg]

  rw [norm_sub_rev q x, norm_sub_rev q y]

  have hsub : (x - q) - (y - q) = x - y := by abel
  rw [← hsub]
  exact euclidean_identity_ips (x - q) (y - q) t

/-- Within a single apartment $A$ realised as Euclidean space $E$, the CAT(0)
identity becomes an equality (not just inequality): the geodesic point
$z_t = t x + (1-t) y$ satisfies the parallelogram identity with the
building distance. -/
theorem euclidean_identity_in_apartment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (b : Building V) (md : ApartmentMetricData b)
    (coord : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → V → E)
    (dist_eq_norm : ∀ (A : { A // A ∈ b.apartmentSystem.apartments }) (u v : V),
      md.dist_fn A u v = ‖coord A u - coord A v‖)
    (coord_geodesic : ∀ (A : { A // A ∈ b.apartmentSystem.apartments })
      (x y z_t : V) (t : ℝ),
      (∃ s ∈ A.val.faces, x ∈ s) → (∃ s ∈ A.val.faces, y ∈ s) →
      (∃ s ∈ A.val.faces, z_t ∈ s) →
      md.dist_fn A z_t x = (1 - t) * md.dist_fn A x y →
      md.dist_fn A z_t y = t * md.dist_fn A x y →
      coord A z_t = t • coord A x + (1 - t) • coord A y)
    (x y q z_t : V) (t : ℝ)
    (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1)
    (hzt_x : buildingDist b md z_t x = (1 - t) * buildingDist b md x y)
    (hzt_y : buildingDist b md z_t y = t * buildingDist b md x y)
    (A : { A // A ∈ b.apartmentSystem.apartments })
    (hqA : ∃ s ∈ A.val.faces, q ∈ s)
    (hxA : ∃ s ∈ A.val.faces, x ∈ s)
    (hyA : ∃ s ∈ A.val.faces, y ∈ s)
    (hztA : ∃ s ∈ A.val.faces, z_t ∈ s) :
    (buildingDist b md q z_t) ^ 2 =
      t * (buildingDist b md q x) ^ 2 +
      (1 - t) * (buildingDist b md q y) ^ 2 -
      t * (1 - t) * (buildingDist b md x y) ^ 2 := by

  rw [buildingDist_eq_dist_fn b md A q z_t hqA hztA,
      buildingDist_eq_dist_fn b md A q x hqA hxA,
      buildingDist_eq_dist_fn b md A q y hqA hyA,
      buildingDist_eq_dist_fn b md A x y hxA hyA]

  rw [dist_eq_norm A q z_t, dist_eq_norm A q x,
      dist_eq_norm A q y, dist_eq_norm A x y]

  have hzt_x_A : md.dist_fn A z_t x = (1 - t) * md.dist_fn A x y := by
    rw [← buildingDist_eq_dist_fn b md A z_t x hztA hxA,
        ← buildingDist_eq_dist_fn b md A x y hxA hyA]; exact hzt_x
  have hzt_y_A : md.dist_fn A z_t y = t * md.dist_fn A x y := by
    rw [← buildingDist_eq_dist_fn b md A z_t y hztA hyA,
        ← buildingDist_eq_dist_fn b md A x y hxA hyA]; exact hzt_y

  have hcoord := coord_geodesic A x y z_t t hxA hyA hztA hzt_x_A hzt_y_A

  exact euclidean_identity_origin_shifted (coord A q) (coord A x) (coord A y)
    (coord A z_t) t hcoord

/-- An affine building with a distance-non-increasing retraction onto each
apartment and a Euclidean realisation of every apartment satisfies the
CAT(0) negative-curvature inequality. This reduces the inequality to the
Euclidean parallelogram identity inside one apartment after retracting. -/
theorem negCurvatureIneq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Building V) (md : ApartmentMetricData b)
    (coord : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → V → E)
    (dist_eq_norm : ∀ (A : { A // A ∈ b.apartmentSystem.apartments }) (u v : V),
      md.dist_fn A u v = ‖coord A u - coord A v‖)
    (coord_geodesic : ∀ (A : { A // A ∈ b.apartmentSystem.apartments })
      (x y z_t : V) (t : ℝ),
      (∃ s ∈ A.val.faces, x ∈ s) → (∃ s ∈ A.val.faces, y ∈ s) →
      (∃ s ∈ A.val.faces, z_t ∈ s) →
      md.dist_fn A z_t x = (1 - t) * md.dist_fn A x y →
      md.dist_fn A z_t y = t * md.dist_fn A x y →
      coord A z_t = t • coord A x + (1 - t) • coord A y)
    (retract_exists : ∀ (x y z z_t : V),
      ∃ (ρ : V → V) (A : { A // A ∈ b.apartmentSystem.apartments }),
        (∃ s ∈ A.val.faces, x ∈ s) ∧ (∃ s ∈ A.val.faces, y ∈ s) ∧
        (∃ s ∈ A.val.faces, ρ z ∈ s) ∧
        ρ x = x ∧ ρ y = y ∧
        (∀ u v, buildingDist b md (ρ u) (ρ v) ≤ buildingDist b md u v) ∧
        buildingDist b md z z_t = buildingDist b md (ρ z) z_t)
    (zt_in_apt : ∀ (x y z_t : V) (t : ℝ),
      0 ≤ t → t ≤ 1 →
      buildingDist b md z_t x = (1 - t) * buildingDist b md x y →
      buildingDist b md z_t y = t * buildingDist b md x y →
      ∀ (A : { A // A ∈ b.apartmentSystem.apartments }),
        (∃ s ∈ A.val.faces, x ∈ s) → (∃ s ∈ A.val.faces, y ∈ s) →
        (∃ s ∈ A.val.faces, z_t ∈ s)) :
    NegCurvatureIneq b md := by
  intro x y z z_t t ht0 ht1 hzt_x hzt_y

  obtain ⟨ρ, A, hxA, hyA, hρzA, hρ_fix_x, hρ_fix_y, hρ_nonincr, hρ_isom⟩ :=
    retract_exists x y z z_t

  have hztA := zt_in_apt x y z_t t ht0 ht1 hzt_x hzt_y A hxA hyA


  have h_euclid : (buildingDist b md (ρ z) z_t) ^ 2 =
      t * (buildingDist b md (ρ z) x) ^ 2 +
      (1 - t) * (buildingDist b md (ρ z) y) ^ 2 -
      t * (1 - t) * (buildingDist b md x y) ^ 2 :=
    euclidean_identity_in_apartment b md coord dist_eq_norm coord_geodesic
      x y (ρ z) z_t t ht0 ht1 hzt_x hzt_y A hρzA hxA hyA hztA


  rw [hρ_isom, h_euclid]


  have h_dim_x : buildingDist b md (ρ z) x ≤ buildingDist b md z x := by
    have h := hρ_nonincr z x; rw [hρ_fix_x] at h; exact h
  have h_dim_y : buildingDist b md (ρ z) y ≤ buildingDist b md z y := by
    have h := hρ_nonincr z y; rw [hρ_fix_y] at h; exact h

  have hρx_sq : (buildingDist b md (ρ z) x) ^ 2 ≤
      (buildingDist b md z x) ^ 2 :=
    pow_le_pow_left₀ (buildingDist_nonneg b md (ρ z) x) h_dim_x 2
  have hρy_sq : (buildingDist b md (ρ z) y) ^ 2 ≤
      (buildingDist b md z y) ^ 2 :=
    pow_le_pow_left₀ (buildingDist_nonneg b md (ρ z) y) h_dim_y 2

  have h1 : t * (buildingDist b md (ρ z) x) ^ 2 ≤
      t * (buildingDist b md z x) ^ 2 :=
    mul_le_mul_of_nonneg_left hρx_sq ht0
  have h2 : (1 - t) * (buildingDist b md (ρ z) y) ^ 2 ≤
      (1 - t) * (buildingDist b md z y) ^ 2 :=
    mul_le_mul_of_nonneg_left hρy_sq (sub_nonneg.mpr ht1)
  linarith

/-- A building $(\mathcal{B}, d)$ is CAT(0) if it is a complete geodesic metric
space satisfying the negative-curvature (CAT(0)) inequality on every geodesic
triangle. This is the geometric form of "non-positive curvature". -/
structure IsCAT0 (b : Building V) (md : ApartmentMetricData b) : Prop where
  metric : IsMetricSpace b md
  geodesic : IsGeodesic b md
  neg_curvature : NegCurvatureIneq b md

/-- Data realising each apartment of a building as an isometric copy of a
Euclidean (inner product) space $E$: coordinates, the distance-as-norm
identity, and the fact that the geodesic point in the apartment maps to the
Euclidean barycentric combination. -/
structure EuclideanRealizationData {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : Building V) (md : ApartmentMetricData b) where
  coord : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → V → E
  dist_eq_norm : ∀ (A : { A // A ∈ b.apartmentSystem.apartments }) (u v : V),
    md.dist_fn A u v = ‖coord A u - coord A v‖
  coord_geodesic : ∀ (A : { A // A ∈ b.apartmentSystem.apartments })
    (x y z_t : V) (t : ℝ),
    (∃ s ∈ A.val.faces, x ∈ s) → (∃ s ∈ A.val.faces, y ∈ s) →
    (∃ s ∈ A.val.faces, z_t ∈ s) →
    md.dist_fn A z_t x = (1 - t) * md.dist_fn A x y →
    md.dist_fn A z_t y = t * md.dist_fn A x y →
    coord A z_t = t • coord A x + (1 - t) • coord A y

/-- Data witnessing that a building admits suitable retractions: for any four
vertices $x, y, z, z_t$ there is a distance-non-increasing retraction $\rho$
to an apartment $A$ containing $x$, $y$, $\rho z$ and fixing $x$ and $y$,
together with the assertion that a geodesic point $z_t$ remains in any
apartment containing both endpoints. -/
structure BuildingRetractionData (b : Building V) (md : ApartmentMetricData b) where
  retract_exists : ∀ (x y z z_t : V),
    ∃ (ρ : V → V) (A : { A // A ∈ b.apartmentSystem.apartments }),
      (∃ s ∈ A.val.faces, x ∈ s) ∧ (∃ s ∈ A.val.faces, y ∈ s) ∧
      (∃ s ∈ A.val.faces, ρ z ∈ s) ∧
      ρ x = x ∧ ρ y = y ∧
      (∀ u v, buildingDist b md (ρ u) (ρ v) ≤ buildingDist b md u v) ∧
      buildingDist b md z z_t = buildingDist b md (ρ z) z_t
  zt_in_apt : ∀ (x y z_t : V) (t : ℝ),
    0 ≤ t → t ≤ 1 →
    buildingDist b md z_t x = (1 - t) * buildingDist b md x y →
    buildingDist b md z_t y = t * buildingDist b md x y →
    ∀ (A : { A // A ∈ b.apartmentSystem.apartments }),
      (∃ s ∈ A.val.faces, x ∈ s) → (∃ s ∈ A.val.faces, y ∈ s) →
      (∃ s ∈ A.val.faces, z_t ∈ s)

/-- The building is contractible: there is a base point $y_0$ and a homotopy
$f : [0,1] \times \mathcal{B} \to \mathcal{B}$ with $f(1, \cdot) = \mathrm{id}$,
$f(0, \cdot) = y_0$, geodesic-distance constraints, and joint continuity
in $(t, x)$. -/
def IsContractible (b : Building V) (md : ApartmentMetricData b) : Prop :=
  ∃ (y₀ : V) (f : ℝ → V → V),

    (∀ x, f 1 x = x) ∧

    (∀ x, f 0 x = y₀) ∧

    (∀ (t : ℝ) (x : V), 0 ≤ t → t ≤ 1 →
      buildingDist b md (f t x) x = (1 - t) * buildingDist b md x y₀ ∧
      buildingDist b md (f t x) y₀ = t * buildingDist b md x y₀) ∧

    (∀ (t : ℝ) (x : V) (ε : ℝ), 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (t' : ℝ) (x' : V),
          |t' - t| < δ → buildingDist b md x' x < δ →
          buildingDist b md (f t' x') (f t x) < ε)

/-- The building is complete: every Cauchy sequence of vertices converges to a
limit in $V$. -/
def IsComplete (b : Building V) (md : ApartmentMetricData b) : Prop :=
  ∀ (seq : ℕ → V),

    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      buildingDist b md (seq m) (seq n) < ε) →

    ∃ lim : V, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      buildingDist b md (seq n) lim < ε

end AffineBuilding
