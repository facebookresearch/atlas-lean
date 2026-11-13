/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Affine
import Atlas.Buildings.code.AffineCoxeter.CanonicalMetric
import Mathlib.Topology.MetricSpace.Basic

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex
open AffineCoxeter

/-- A map $f : X \to Y$ between pseudo-metric spaces is a similitude of
ratio $c > 0$ if $d(f(x), f(y)) = c \cdot d(x, y)$ for all $x, y \in X$. -/
def IsSimilitude {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (c : ℝ) : Prop :=
  0 < c ∧ ∀ x y : X, dist (f x) (f y) = c * dist x y

/-- A similitude sends bounded sets to bounded sets. -/
lemma IsSimilitude.image_bounded {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {c : ℝ} (hf : IsSimilitude f c) (S : Set X) (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (f '' S) := by
  rw [Metric.isBounded_iff]
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hS
  exact ⟨c * D, fun x ⟨a, ha, hfa⟩ y ⟨b, hb, hfb⟩ => by
    rw [← hfa, ← hfb, hf.2 a b]; exact mul_le_mul_of_nonneg_left (hD ha hb) (le_of_lt hf.1)⟩

/-- A similitude of ratio $c$ scales diameters by $c$:
$\mathrm{diam}(f(S)) = c \cdot \mathrm{diam}(S)$. -/
lemma IsSimilitude.diam_image {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {c : ℝ} (hf : IsSimilitude f c) (S : Set X) (hS : Bornology.IsBounded S) :
    Metric.diam (f '' S) = c * Metric.diam S := by
  apply le_antisymm
  ·
    apply Metric.diam_le_of_forall_dist_le (mul_nonneg (le_of_lt hf.1) Metric.diam_nonneg)
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [hf.2 a b]
    exact mul_le_mul_of_nonneg_left (Metric.dist_le_diam_of_mem hS ha hb) (le_of_lt hf.1)
  ·


    have hfS_bdd := hf.image_bounded S hS
    rw [mul_comm, ← le_div_iff₀ hf.1]
    apply Metric.diam_le_of_forall_dist_le (div_nonneg Metric.diam_nonneg (le_of_lt hf.1))
    intro a ha b hb
    rw [le_div_iff₀ hf.1, mul_comm, ← hf.2 a b]
    exact Metric.dist_le_diam_of_mem hfS_bdd (Set.mem_image_of_mem f ha) (Set.mem_image_of_mem f hb)

/-- If a similitude $f$ of ratio $c$ sends a set $S$ of diameter $1$ to a
set of diameter $1$, then $c = 1$ (so $f$ is an isometry on the diameter). -/
lemma IsSimilitude.const_eq_one_of_diam_preserved
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {c : ℝ} (hf : IsSimilitude f c)
    {S : Set X} (hS_bdd : Bornology.IsBounded S)
    (hS_diam : Metric.diam S = 1) (hfS_diam : Metric.diam (f '' S) = 1) :
    c = 1 := by
  have h := hf.diam_image S hS_bdd
  rw [hfS_diam, hS_diam] at h
  linarith

namespace AffineCoxeterComplex

variable {B : Type*} [DecidableEq B]

/-- A canonical metric on the realization of an affine Coxeter complex of
matrix $M$: a designated family of "chambers" $\{C\} \subseteq X$, each
bounded with diameter exactly $1$. -/
structure CanonicalMetric (M : CoxeterMatrix B) (X : Type*)
    [PseudoMetricSpace X] where
  chambers : Set (Set X)
  chamber_bounded : ∀ C ∈ chambers, Bornology.IsBounded C
  chamber_diam_one : ∀ C ∈ chambers, Metric.diam C = 1
  is_affine : M.IsAffine

/-- A canonical metric on $X$ is $W$-invariant under an action $W \times X
\to X$ if every $w \in W$ acts as an isometry on $X$. -/
def CanonicalMetric.IsWInvariant {M : CoxeterMatrix B} {X : Type*}
    [PseudoMetricSpace X]
    (_cm : CanonicalMetric M X)
    (action : M.Group → X → X) : Prop :=
  ∀ w : M.Group, ∀ x y : X, dist (action w x) (action w y) = dist x y

/-- The canonical distance on the Euclidean realization $E$ of an affine
Coxeter complex: $d(x, y) = \|x - y\| / \mathrm{diam}(C)$, where $C$ is
any chamber. This normalizes chambers to have diameter $1$. -/
noncomputable def CoxeterComplexCanonicalDist
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : AffineCoxeterComplex E) (x y : E) : ℝ :=
  ‖x - y‖ / A.chamberDiameter



/-- Abstract canonical-metric version: a similitude $\varphi : X \to X'$
sending chambers to chambers between two canonical metrics with
nonempty chamber families must be an isometry, because chamber diameter
$1$ forces the similitude constant to be $1$. -/
theorem sc_iso_canonical_isometry'
    {B B' : Type*} [DecidableEq B] [DecidableEq B']
    {M : CoxeterMatrix B} {M' : CoxeterMatrix B'}
    {X X' : Type*} [PseudoMetricSpace X] [PseudoMetricSpace X']
    (cm : CanonicalMetric M X) (cm' : CanonicalMetric M' X')
    (φ : X → X')
    {c : ℝ} (hφ : IsSimilitude φ c)
    (hφ_chambers : ∀ C ∈ cm.chambers, (φ '' C) ∈ cm'.chambers)
    (h_cover : ∀ x : X, ∃ C ∈ cm.chambers, x ∈ C)
    (hC_nonempty : cm.chambers.Nonempty) :
    ∀ x y : X, dist (φ x) (φ y) = dist x y := by


  obtain ⟨C, hC_mem⟩ := hC_nonempty

  have hC_diam : Metric.diam C = 1 := cm.chamber_diam_one C hC_mem

  have hφC_diam : Metric.diam (φ '' C) = 1 := cm'.chamber_diam_one (φ '' C) (hφ_chambers C hC_mem)

  have hC_bdd : Bornology.IsBounded C := cm.chamber_bounded C hC_mem


  have hc_one : c = 1 := hφ.const_eq_one_of_diam_preserved hC_bdd hC_diam hφC_diam

  intro x y
  rw [hφ.2 x y, hc_one, one_mul]

/-- Uniqueness of canonical (chamber-diameter-one) metrics: a similitude
between two pseudo-metric spaces sending chambers of diameter $1$ to
chambers of diameter $1$ is automatically an isometry. -/
theorem canonical_metric_unique
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (chambersX : Set (Set X)) (chambersY : Set (Set Y))
    (hX_bdd : ∀ C ∈ chambersX, Bornology.IsBounded C)
    (hX_diam : ∀ C ∈ chambersX, Metric.diam C = 1)
    (hY_diam : ∀ C ∈ chambersY, Metric.diam C = 1)
    (φ : X → Y)
    {c : ℝ} (hφ : IsSimilitude φ c)
    (hφ_chambers : ∀ C ∈ chambersX, (φ '' C) ∈ chambersY)
    (hne : chambersX.Nonempty) :
    ∀ x y : X, dist (φ x) (φ y) = dist x y := by

  obtain ⟨C, hC⟩ := hne

  have hc_one : c = 1 :=
    hφ.const_eq_one_of_diam_preserved (hX_bdd C hC) (hX_diam C hC) (hY_diam _ (hφ_chambers C hC))

  intro x y
  rw [hφ.2 x y, hc_one, one_mul]

/-- Canonical-metric formulation of `canonical_metric_unique`: a
similitude between two `CanonicalMetric` structures sending chambers to
chambers is an isometry. -/
theorem canonical_metric_unique'
    {B B' : Type*} [DecidableEq B] [DecidableEq B']
    {M : CoxeterMatrix B} {M' : CoxeterMatrix B'}
    {X X' : Type*} [PseudoMetricSpace X] [PseudoMetricSpace X']
    (cm : CanonicalMetric M X) (cm' : CanonicalMetric M' X')
    (φ : X → X')
    {c : ℝ} (hφ : IsSimilitude φ c)
    (hφ_chambers : ∀ C ∈ cm.chambers, (φ '' C) ∈ cm'.chambers)
    (hne : cm.chambers.Nonempty) :
    ∀ x y : X, dist (φ x) (φ y) = dist x y :=
  canonical_metric_unique cm.chambers cm'.chambers
    cm.chamber_bounded cm.chamber_diam_one cm'.chamber_diam_one
    φ hφ hφ_chambers hne

end AffineCoxeterComplex

variable {V : Type*} [DecidableEq V]

namespace AffineBuilding

/-- The type of a per-apartment metric: a function assigning to each
apartment $A$ a (pseudo-)distance $V \times V \to \mathbb{R}$. -/
def apartmentMetric (b : Building V) :=
  { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → (V → V → ℝ)

/-- Per-apartment metric data for a building: an ambient space $X$ with
embedding $\iota : V \to X$ and a per-apartment pseudo-distance
$\mathrm{dist}_{\mathrm{fn}}$ that is symmetric, satisfies the triangle
inequality, vanishes on the diagonal, is preserved by every simplicial
isomorphism between apartments, and normalizes each chamber to have
diameter $1$. -/
structure ApartmentMetricData (b : Building V) where
  X : Type*
  ι : V → X
  dist_X : X → X → ℝ
  dist_fn : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → (V → V → ℝ)
  dist_nonneg : ∀ A x y, 0 ≤ dist_fn A x y
  dist_symm : ∀ A x y, dist_fn A x y = dist_fn A y x
  dist_eq_zero : ∀ A (x : V), dist_fn A x x = 0
  dist_triangle : ∀ A x y z, dist_fn A x z ≤ dist_fn A x y + dist_fn A y z
  iso_isometry : ∀ (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments }),
    ∀ (φ : SimplicialMap A₁.val A₂.val),
      (∀ s ∈ A₁.val.faces, s.image φ.toFun ∈ A₂.val.faces) →
      ∀ x y, dist_fn A₁ x y = dist_fn A₂ (φ.toFun x) (φ.toFun y)
  chamber_diam_one : ∀ (A : { A // A ∈ b.apartmentSystem.apartments }),
    ∀ C, A.val.IsMaximal C →
      (∀ x ∈ C, ∀ y ∈ C, dist_fn A x y ≤ 1) ∧
      (∃ x ∈ C, ∃ y ∈ C, dist_fn A x y = 1)

/-- The ambient-space distance between two vertices: $d_X(\iota v, \iota w)$. -/
def ApartmentMetricData.buildingDistVert {b : Building V}
    (md : ApartmentMetricData b) (v w : V) : ℝ :=
  md.dist_X (md.ι v) (md.ι w)

/-- The building distance between two vertices $x, y$: if there is some
apartment containing faces through both $x$ and $y$, return the
apartment-distance in any such apartment; otherwise return $0$.
Well-definedness is proved below by `buildingDist_well_defined_general`. -/
noncomputable def buildingDist (b : Building V) (md : ApartmentMetricData b)
    (x y : V) : ℝ :=
  if h : ∃ (A : { A // A ∈ b.apartmentSystem.apartments }),
      (∃ s ∈ A.val.faces, x ∈ s) ∧ (∃ s ∈ A.val.faces, y ∈ s)
  then md.dist_fn h.choose x y
  else 0

/-- If two apartments share a face $\sigma$ and a chamber $C$ containing
$\sigma$, then there is a simplicial isomorphism $A_1 \to A_2$ fixing
both vertices $x$ and $y$ of $\sigma$. -/
lemma iso_fix_from_shared_face_and_chamber
    (b : Building V)
    (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
    (σ : Finset V) (C : Finset V)
    (x y : V)
    (hσ_A₁ : σ ∈ A₁.val.faces) (hσ_A₂ : σ ∈ A₂.val.faces)
    (hx_σ : x ∈ σ) (hy_σ : y ∈ σ)
    (hC_max : A₁.val.IsMaximal C) (hC_A₂ : C ∈ A₂.val.faces) :
    ∃ φ : SimplicialMap A₁.val A₂.val, φ.toFun x = x ∧ φ.toFun y = y := by

  obtain ⟨φ, hφ_σ, _hφ_C⟩ :=
    b.apartmentSystem.iso_exists A₁.val A₁.property A₂.val A₂.property
      σ hσ_A₁ hσ_A₂ C hC_max hC_A₂
  exact ⟨φ, hφ_σ x hx_σ, hφ_σ y hy_σ⟩

/-- When $x, y$ both lie in a face $\sigma$ shared by two apartments that
also share a chamber containing $\sigma$, the apartment distances agree:
$\mathrm{dist}_{A_1}(x, y) = \mathrm{dist}_{A_2}(x, y)$. -/
lemma buildingDist_wellDefined_from_face_and_chamber
    (b : Building V) (md : ApartmentMetricData b)
    (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
    (σ : Finset V) (C : Finset V)
    (hσ_A₁ : σ ∈ A₁.val.faces) (hσ_A₂ : σ ∈ A₂.val.faces)
    (hC_max : A₁.val.IsMaximal C) (hC_A₂ : C ∈ A₂.val.faces)
    (x y : V) (hx_σ : x ∈ σ) (hy_σ : y ∈ σ) :
    md.dist_fn A₁ x y = md.dist_fn A₂ x y := by

  obtain ⟨φ, hφx, hφy⟩ := iso_fix_from_shared_face_and_chamber b A₁ A₂
    σ C x y hσ_A₁ hσ_A₂ hx_σ hy_σ hC_max hC_A₂

  have h_iso := md.iso_isometry A₁ A₂ φ φ.map_face x y

  rw [h_iso, hφx, hφy]

/-- A "cross" version of well-definedness: $x$ lies in a shared face
$\sigma$ and $y$ lies in a shared chamber $C$; the two apartments share
both $\sigma$ and $C$, so an isomorphism fixes both $x$ and $y$ and the
apartment distances agree. -/
lemma buildingDist_wellDefined_from_face_and_chamber_cross
    (b : Building V) (md : ApartmentMetricData b)
    (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
    (σ : Finset V) (C : Finset V)
    (hσ_A₁ : σ ∈ A₁.val.faces) (hσ_A₂ : σ ∈ A₂.val.faces)
    (hC_max : A₁.val.IsMaximal C) (hC_A₂ : C ∈ A₂.val.faces)
    (x y : V) (hx_σ : x ∈ σ) (hy_C : y ∈ C) :
    md.dist_fn A₁ x y = md.dist_fn A₂ x y := by

  obtain ⟨φ, hφ_σ, hφ_C⟩ :=
    b.apartmentSystem.iso_exists A₁.val A₁.property A₂.val A₂.property
      σ hσ_A₁ hσ_A₂ C hC_max hC_A₂

  have hφx : φ.toFun x = x := hφ_σ x hx_σ
  have hφy : φ.toFun y = y := hφ_C y hy_C

  have h_iso := md.iso_isometry A₁ A₂ φ φ.map_face x y
  rw [h_iso, hφx, hφy]

/-- Well-definedness of the building distance when there is a common face
through $v$ and $w$: any two apartments containing such a face assign the
same distance to $(v, w)$. The proof uses the standard chamber-system
argument: extend $\sigma$ to a chamber in each apartment and find a third
apartment containing both. -/
theorem buildingDist_wellDefined (b : Building V) (md : ApartmentMetricData b)
    (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
    (v w : V)

    (hcommon : ∃ σ ∈ A₁.val.faces, σ ∈ A₂.val.faces ∧ v ∈ σ ∧ w ∈ σ) :
    md.dist_fn A₁ v w = md.dist_fn A₂ v w := by

  obtain ⟨σ, hσ_A₁, hσ_A₂, hv_σ, hw_σ⟩ := hcommon


  obtain ⟨_, _, cc₁, hcc₁_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A₁.val A₁.property
  obtain ⟨_, _, cc₂, hcc₂_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A₂.val A₂.property

  have hσ_cc₁ : σ ∈ cc₁.toSimplicialComplex.faces := hcc₁_eq ▸ hσ_A₁
  obtain ⟨C₁, hC₁_max_cc, hσ_sub_C₁⟩ := cc₁.exists_maximal σ hσ_cc₁
  have hC₁_max : A₁.val.IsMaximal C₁ := hcc₁_eq ▸ hC₁_max_cc

  have hσ_cc₂ : σ ∈ cc₂.toSimplicialComplex.faces := hcc₂_eq ▸ hσ_A₂
  obtain ⟨D₂, hD₂_max_cc, hσ_sub_D₂⟩ := cc₂.exists_maximal σ hσ_cc₂
  have hD₂_max : A₂.val.IsMaximal D₂ := hcc₂_eq ▸ hD₂_max_cc

  have hC₁_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A₁.val A₁.property C₁ hC₁_max
  have hD₂_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A₂.val A₂.property D₂ hD₂_max

  obtain ⟨A₃_val, hA₃_mem, hC₁_A₃, hD₂_A₃⟩ :=
    b.apartmentSystem.contains_pair C₁ D₂ hC₁_bmax hD₂_bmax
  let A₃ : { A // A ∈ b.apartmentSystem.apartments } := ⟨A₃_val, hA₃_mem⟩

  have hσ_nonempty : σ.Nonempty := ⟨v, hv_σ⟩
  have hσ_A₃ : σ ∈ A₃.val.faces :=
    A₃_val.down_closed hC₁_A₃ hσ_sub_C₁ hσ_nonempty


  have h₁ := buildingDist_wellDefined_from_face_and_chamber b md A₁ A₃
    σ C₁ hσ_A₁ hσ_A₃ hC₁_max hC₁_A₃ v w hv_σ hw_σ


  have h₂ := buildingDist_wellDefined_from_face_and_chamber b md A₂ A₃
    σ D₂ hσ_A₂ hσ_A₃ hD₂_max hD₂_A₃ v w hv_σ hw_σ

  rw [h₁, ← h₂]

/-- Well-definedness without assuming a common face: if vertices
$\{v\}, \{w\}$ are both vertices of two apartments $A_1, A_2$ (no shared
edge required), then $\mathrm{dist}_{A_1}(v, w) = \mathrm{dist}_{A_2}(v, w)$.
The proof combines $v$ and $w$ across a third apartment via the
"cross" lemma in both directions. -/
theorem buildingDist_well_defined_clean (b : Building V) (md : ApartmentMetricData b)
    (v w : V)
    (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
    (hv₁ : {v} ∈ A₁.val.faces) (hw₁ : {w} ∈ A₁.val.faces)
    (hv₂ : {v} ∈ A₂.val.faces) (hw₂ : {w} ∈ A₂.val.faces) :
    md.dist_fn A₁ v w = md.dist_fn A₂ v w := by

  obtain ⟨_, _, cc₁, hcc₁_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A₁.val A₁.property
  have hw_cc₁ : {w} ∈ cc₁.toSimplicialComplex.faces := hcc₁_eq ▸ hw₁
  obtain ⟨C_w, hCw_max_cc, hw_sub_Cw⟩ := cc₁.exists_maximal {w} hw_cc₁
  have hCw_max : A₁.val.IsMaximal C_w := hcc₁_eq ▸ hCw_max_cc
  have hCw_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A₁.val A₁.property C_w hCw_max

  obtain ⟨_, _, cc₂, hcc₂_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A₂.val A₂.property
  have hv_cc₂ : {v} ∈ cc₂.toSimplicialComplex.faces := hcc₂_eq ▸ hv₂
  obtain ⟨D_v, hDv_max_cc, hv_sub_Dv⟩ := cc₂.exists_maximal {v} hv_cc₂
  have hDv_max : A₂.val.IsMaximal D_v := hcc₂_eq ▸ hDv_max_cc
  have hDv_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A₂.val A₂.property D_v hDv_max

  obtain ⟨A₃_val, hA₃_mem, hCw_A₃, hDv_A₃⟩ :=
    b.apartmentSystem.contains_pair C_w D_v hCw_bmax hDv_bmax
  let A₃ : { A // A ∈ b.apartmentSystem.apartments } := ⟨A₃_val, hA₃_mem⟩

  have hv_A₃ : {v} ∈ A₃.val.faces :=
    A₃_val.down_closed hDv_A₃ hv_sub_Dv (Finset.singleton_nonempty v)
  have hw_A₃ : {w} ∈ A₃.val.faces :=
    A₃_val.down_closed hCw_A₃ hw_sub_Cw (Finset.singleton_nonempty w)

  have hw_in_Cw : w ∈ C_w := Finset.singleton_subset_iff.mp hw_sub_Cw
  have h₁ := buildingDist_wellDefined_from_face_and_chamber_cross b md A₁ A₃
    {v} C_w hv₁ hv_A₃ hCw_max hCw_A₃ v w
    (Finset.mem_singleton.mpr rfl) hw_in_Cw

  have hv_in_Dv : v ∈ D_v := Finset.singleton_subset_iff.mp hv_sub_Dv
  have h₂_swap := buildingDist_wellDefined_from_face_and_chamber_cross b md A₂ A₃
    {w} D_v hw₂ hw_A₃ hDv_max hDv_A₃ w v
    (Finset.mem_singleton.mpr rfl) hv_in_Dv

  have h₂ : md.dist_fn A₂ v w = md.dist_fn A₃ v w := by
    rw [md.dist_symm A₂ v w, h₂_swap, md.dist_symm A₃ w v]

  rw [h₁, ← h₂]

/-- Most general well-definedness: assuming only that $x, y$ are each
contained in some face of $A_1$ and some face of $A_2$ (i.e., they are
vertices of both apartments), the apartment distances agree. -/
theorem buildingDist_well_defined_general (b : Building V) (md : ApartmentMetricData b)
    (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
    (x y : V)
    (hx₁ : ∃ s ∈ A₁.val.faces, x ∈ s) (hy₁ : ∃ s ∈ A₁.val.faces, y ∈ s)
    (hx₂ : ∃ s ∈ A₂.val.faces, x ∈ s) (hy₂ : ∃ s ∈ A₂.val.faces, y ∈ s) :
    md.dist_fn A₁ x y = md.dist_fn A₂ x y := by

  obtain ⟨sx, hsx, hx_sx⟩ := hx₁
  have hx₁' : {x} ∈ A₁.val.faces :=
    A₁.val.down_closed hsx (Finset.singleton_subset_iff.mpr hx_sx) (Finset.singleton_nonempty x)
  obtain ⟨sy, hsy, hy_sy⟩ := hy₁
  have hy₁' : {y} ∈ A₁.val.faces :=
    A₁.val.down_closed hsy (Finset.singleton_subset_iff.mpr hy_sy) (Finset.singleton_nonempty y)
  obtain ⟨sx₂, hsx₂, hx_sx₂⟩ := hx₂
  have hx₂' : {x} ∈ A₂.val.faces :=
    A₂.val.down_closed hsx₂ (Finset.singleton_subset_iff.mpr hx_sx₂) (Finset.singleton_nonempty x)
  obtain ⟨sy₂, hsy₂, hy_sy₂⟩ := hy₂
  have hy₂' : {y} ∈ A₂.val.faces :=
    A₂.val.down_closed hsy₂ (Finset.singleton_subset_iff.mpr hy_sy₂) (Finset.singleton_nonempty y)

  exact buildingDist_well_defined_clean b md x y A₁ A₂ hx₁' hy₁' hx₂' hy₂'

/-- The building distance defines a pseudo-metric: nonnegativity, symmetry,
$d(x, x) = 0$, and triangle inequality. -/
def IsMetricSpace (b : Building V) (md : ApartmentMetricData b) : Prop :=
  (∀ x y, 0 ≤ buildingDist b md x y) ∧
  (∀ x y, buildingDist b md x y = buildingDist b md y x) ∧
  (∀ x, buildingDist b md x x = 0) ∧
  (∀ x y z, buildingDist b md x z ≤ buildingDist b md x y + buildingDist b md y z)

/-- A geodesic path from $x$ to $y$ in the building: a finite vertex list
$v_0 = x, v_1, \ldots, v_n = y$ whose consecutive-distance sum equals
$\mathrm{dist}(x, y)$, certifying the path is length-minimizing. -/
structure GeodesicPath (b : Building V) (md : ApartmentMetricData b)
    (x y : V) where
  vertices : List V
  head_eq : vertices.head? = some x
  last_eq : vertices.getLast? = some y
  nonempty : vertices ≠ []
  length_eq : (List.zipWith (buildingDist b md) vertices vertices.tail).sum
    = buildingDist b md x y

/-- The building is a geodesic space: every pair of vertices is connected
by some geodesic path. -/
def IsGeodesic (b : Building V) (md : ApartmentMetricData b) : Prop :=
  ∀ x y, Nonempty (GeodesicPath b md x y)

/-- A retraction $\rho : V \to V$ is distance-non-increasing if
$d(\rho x, \rho y) \le d(x, y)$ for all vertices $x, y$. -/
def IsRetractDistNonIncreasing (b : Building V) (md : ApartmentMetricData b)
    (ρ : V → V) : Prop :=
  ∀ x y, buildingDist b md (ρ x) (ρ y) ≤ buildingDist b md x y

/-- A retraction $\rho : V \to V$ is an isometry on the base chamber if
$d(\rho x, \rho y) = d(x, y)$ whenever at least one of $x, y$ lies in the
base chamber. -/
def IsRetractIsometryOnBase (b : Building V) (md : ApartmentMetricData b)
    (ρ : V → V) (base : Finset V) : Prop :=
  ∀ x y, (x ∈ base ∨ y ∈ base) →
    buildingDist b md (ρ x) (ρ y) = buildingDist b md x y

/-- Telescoping triangle inequality: for any list $[v_0, \ldots, v_n]$,
$d(v_0, v_n) \le \sum_{i=0}^{n-1} d(v_i, v_{i+1})$, assuming $d$
satisfies the triangle inequality and $d(x, x) \le 0$. -/
lemma telescoping_triangle_ineq
    {α : Type*}
    (d : α → α → ℝ)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hzero : ∀ x, d x x ≤ 0) :
    ∀ (l : List α) (hne : l ≠ []),
    d (l.head hne) (l.getLast hne) ≤ (List.zipWith d l l.tail).sum := by
  intro l hne
  induction l with
  | nil => exact absurd rfl hne
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp [List.head, List.getLast, List.tail]
      exact hzero a
    | cons c rest' =>
      have htail_ne : (c :: rest') ≠ [] := List.cons_ne_nil _ _
      have ih_tail := ih htail_ne
      have htail_simp : (c :: rest').tail = rest' := by simp [List.tail]
      rw [htail_simp] at ih_tail
      simp only [List.head, List.tail_cons, List.zipWith_cons_cons, List.sum_cons]
      have hhead_eq : (c :: rest').head htail_ne = c := by simp [List.head]
      have hlast_eq : (a :: c :: rest').getLast (List.cons_ne_nil a (c :: rest'))
          = (c :: rest').getLast htail_ne := by
        simp [List.getLast_cons]
      rw [hlast_eq]
      rw [hhead_eq] at ih_tail
      calc d a ((c :: rest').getLast htail_ne)
          ≤ d a c + d c ((c :: rest').getLast htail_ne) := htri a c _
        _ ≤ d a c + (List.zipWith d (c :: rest') rest').sum := by linarith

/-- The (combinatorial) line segment from $x$ to $y$: the set of vertices
$z$ satisfying $d(x, y) = d(x, z) + d(z, y)$ (the additivity / "between"
relation). -/
def LineSegment (b : Building V) (md : ApartmentMetricData b) (x y : V) : Set V :=
  { z : V | buildingDist b md x y = buildingDist b md x z + buildingDist b md z y }

end AffineBuilding
