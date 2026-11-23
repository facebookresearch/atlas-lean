/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Reflection.WallSeparation
import Atlas.Buildings.code.Reflection.ReflectionGroupsCoxeter
import Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs
import Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Theorems
import Atlas.Buildings.code.Reflection.GenericFunctional

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

namespace HyperplaneArrangement

variable {arr : HyperplaneArrangement E}

def ChamberInPositiveHalfSpace (C : arr.Chamber) (η : AffineHyperplane E) : Prop :=
  C.set ⊆ η.positiveHalfSpace

def ChamberInNegativeHalfSpace (C : arr.Chamber) (η : AffineHyperplane E) : Prop :=
  C.set ⊆ η.negativeHalfSpace

def inwardUnitNormal (C : arr.Chamber) (η : AffineHyperplane E)
    [Decidable (ChamberInPositiveHalfSpace C η)] : E :=
  if ChamberInPositiveHalfSpace C η
  then (‖η.normal‖⁻¹) • η.normal
  else (‖η.normal‖⁻¹) • (-η.normal)

lemma norm_inwardUnitNormal {C : arr.Chamber} {η : AffineHyperplane E}
    [Decidable (ChamberInPositiveHalfSpace C η)] :
    ‖inwardUnitNormal C η‖ = 1 := by
  unfold inwardUnitNormal
  split
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr η.normal_ne_zero
  · rw [norm_smul, norm_inv, norm_norm, norm_neg, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr η.normal_ne_zero

theorem root_diff_mem_of_inner_pos
    (Φ : FiniteReflectionGroups.RootSystem E)
    (hcryst : Φ.IsCrystallographic)
    {α β : E}
    (hα : α ∈ Φ.roots) (hβ : β ∈ Φ.roots)
    (hne : α ≠ β) (hneg : α ≠ -β)
    (hpos : @inner ℝ _ _ α β > 0) :
    α - β ∈ Φ.roots := by
  open FiniteReflectionGroups in
  obtain ⟨n, hn⟩ := hcryst β hβ α hα
  obtain ⟨m, hm⟩ := hcryst α hα β hβ
  have hα_ne : α ≠ 0 := Φ.roots_ne_zero α hα
  have hβ_ne : β ≠ 0 := Φ.roots_ne_zero β hβ
  have hαα_pos : ⟪α, α⟫_ℝ > 0 := by rw [real_inner_self_eq_norm_sq]; positivity
  have hββ_pos : ⟪β, β⟫_ℝ > 0 := by rw [real_inner_self_eq_norm_sq]; positivity
  have hcoroot_α : ⟪β, coroot α⟫_ℝ = (2 / ⟪α, α⟫_ℝ) * ⟪β, α⟫_ℝ := by
    simp only [coroot, real_inner_smul_right]
  have hcoroot_β : ⟪α, coroot β⟫_ℝ = (2 / ⟪β, β⟫_ℝ) * ⟪α, β⟫_ℝ := by
    simp only [coroot, real_inner_smul_right]
  have hn_val : (n : ℝ) = 2 * ⟪α, β⟫_ℝ / ⟪α, α⟫_ℝ := by
    rw [← hn, hcoroot_α, real_inner_comm β α]; ring
  have hm_val : (m : ℝ) = 2 * ⟪α, β⟫_ℝ / ⟪β, β⟫_ℝ := by
    rw [← hm, hcoroot_β]; ring
  have hn_pos : (n : ℝ) > 0 := by rw [hn_val]; positivity
  have hn_ge_one : n ≥ 1 := Int.lt_iff_add_one_le.mp (by exact_mod_cast hn_pos)
  have hm_pos : (m : ℝ) > 0 := by rw [hm_val]; positivity
  have hm_ge_one : m ≥ 1 := Int.lt_iff_add_one_le.mp (by exact_mod_cast hm_pos)

  have cs : ⟪α, β⟫_ℝ * ⟪α, β⟫_ℝ ≤ ⟪α, α⟫_ℝ * ⟪β, β⟫_ℝ := by
    have h1 := real_inner_le_norm α β
    have h2 := real_inner_le_norm α (-β)
    simp only [inner_neg_right, norm_neg] at h2
    have : ⟪α, β⟫_ℝ ^ 2 ≤ (‖α‖ * ‖β‖) ^ 2 := sq_le_sq' (by linarith) h1
    rw [mul_pow, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at this
    nlinarith [sq_abs (⟪α, β⟫_ℝ)]

  have hnm_eq : (n : ℝ) * m = 4 * (⟪α, β⟫_ℝ * ⟪α, β⟫_ℝ) / (⟪α, α⟫_ℝ * ⟪β, β⟫_ℝ) := by
    rw [hn_val, hm_val]; field_simp; ring
  have hnm_le : (n : ℝ) * m ≤ 4 := by
    rw [hnm_eq]; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hnm_le_int : n * m ≤ 4 := by exact_mod_cast hnm_le

  have h_n1_or_m1 : n = 1 ∨ m = 1 := by
    by_contra h_neither
    push_neg at h_neither
    have hn2 : n ≥ 2 := by omega
    have hm2 : m ≥ 2 := by omega
    have h4 : n * m ≥ 4 := by nlinarith
    have hn_eq : n = 2 := by nlinarith
    have hm_eq : m = 2 := by nlinarith
    have h_inner_eq_αα : ⟪α, β⟫_ℝ = ⟪α, α⟫_ℝ := by
      have : (n : ℝ) = 2 := by exact_mod_cast hn_eq
      rw [hn_val] at this; field_simp at this; linarith
    have h_inner_eq_ββ : ⟪α, β⟫_ℝ = ⟪β, β⟫_ℝ := by
      have : (m : ℝ) = 2 := by exact_mod_cast hm_eq
      rw [hm_val] at this; field_simp at this; linarith
    have h_zero : ⟪α - β, α - β⟫_ℝ = 0 := by
      simp only [inner_sub_left, inner_sub_right]
      nlinarith [real_inner_comm β α]
    exact hne (sub_eq_zero.mp (inner_self_eq_zero.mp h_zero))

  rcases h_n1_or_m1 with hn1 | hm1
  ·
    have h_coeff : 2 * ⟪α, β⟫_ℝ / ⟪α, α⟫_ℝ = 1 := by
      linarith [show (n : ℝ) = 1 from by exact_mod_cast hn1, hn_val]
    have h_refl : linearReflection α β = β - α := by
      simp only [linearReflection, h_coeff, one_smul]
    have h_mem := Φ.reflection_closed α hα β hβ
    rw [show α - β = -(β - α) from by abel, ← h_refl]
    exact Φ.neg_mem_roots h_mem
  ·
    have h_coeff : 2 * ⟪β, α⟫_ℝ / ⟪β, β⟫_ℝ = 1 := by
      rw [real_inner_comm]
      linarith [show (m : ℝ) = 1 from by exact_mod_cast hm1, hm_val]
    have h_refl : linearReflection β α = α - β := by
      simp only [linearReflection, h_coeff, one_smul]
    rw [← h_refl]
    exact Φ.reflection_closed β hβ α hα

theorem simple_roots_inner_nonpos_axiom
    (Φ : FiniteReflectionGroups.RootSystem E)
    (hcryst : Φ.IsCrystallographic)
    (f : E → ℝ) (hf_linear : IsLinearMap ℝ f)
    (hf_nonzero : ∀ α ∈ Φ.roots, f α ≠ 0)
    {α β : E}
    (hα : Φ.IsSimpleRoot f α) (hβ : Φ.IsSimpleRoot f β)
    (hne : α ≠ β) :

    @inner ℝ _ _ α β ≤ 0 := by

  by_contra h_pos
  push_neg at h_pos

  have hα_pos : α ∈ Φ.positiveRootSet f := hα.1
  have hβ_pos : β ∈ Φ.positiveRootSet f := hβ.1
  have hα_root : α ∈ Φ.roots := hα_pos.1
  have hβ_root : β ∈ Φ.roots := hβ_pos.1
  have hfα : f α > 0 := hα_pos.2
  have hfβ : f β > 0 := hβ_pos.2
  have hα_simple := hα.2
  have hβ_simple := hβ.2

  have hα_ne_neg_β : α ≠ -β := by
    intro h
    have h1 : f α = f (-β) := by rw [h]
    have hf_map_smul' : ∀ (r : ℝ) (x : E), f (r • x) = r * f x := hf_linear.2
    have h2 : f (-β) = (-1 : ℝ) * f β := by rw [← hf_map_smul']; simp
    linarith

  have h_diff_root : α - β ∈ Φ.roots :=
    root_diff_mem_of_inner_pos Φ hcryst hα_root hβ_root hne hα_ne_neg_β h_pos

  have hf_diff_ne : f (α - β) ≠ 0 := hf_nonzero (α - β) h_diff_root

  have hf_map_add : ∀ (x y : E), f (x + y) = f x + f y := hf_linear.1
  have hf_map_smul : ∀ (r : ℝ) (x : E), f (r • x) = r * f x := hf_linear.2
  have hf_map_sub : ∀ (x y : E), f (x - y) = f x - f y := by
    intro x y; rw [sub_eq_add_neg, hf_map_add, show f (-y) = (-1) * f y from
      by rw [← hf_map_smul, neg_one_smul]]; ring
  have hf_diff_val : f (α - β) = f α - f β := hf_map_sub α β

  rcases lt_or_gt_of_ne hf_diff_ne with hf_neg | hf_pos_diff
  ·
    have h_neg_diff_root : β - α ∈ Φ.roots := by
      have : β - α = -(α - β) := by abel
      rw [this]; exact Φ.neg_mem_roots h_diff_root
    have hf_neg_diff : f (β - α) > 0 := by
      have : f (β - α) = f β - f α := hf_map_sub β α
      rw [this]; linarith [hf_diff_val]
    have h_neg_diff_pos : β - α ∈ Φ.positiveRootSet f := ⟨h_neg_diff_root, hf_neg_diff⟩

    apply hβ_simple
    exact ⟨β - α, α, h_neg_diff_pos, hα_pos, by abel⟩
  ·
    have h_diff_pos : α - β ∈ Φ.positiveRootSet f := ⟨h_diff_root, by linarith [hf_diff_val]⟩

    apply hα_simple
    exact ⟨α - β, β, h_diff_pos, hβ_pos, by abel⟩

/-- *Reflection through a unit vector*: when $\|e\| = 1$, the formula for the linear reflection
across the hyperplane $e^\perp$ simplifies to $v \mapsto v - 2\langle e, v\rangle\,e$, since the
denominator $\langle e, e\rangle = \|e\|^2 = 1$ disappears. -/
lemma linearReflection_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e v : E) (he : ‖e‖ = 1) :
    FiniteReflectionGroups.linearReflection e v = v - (2 * ⟪e, v⟫_ℝ) • e := by
  unfold FiniteReflectionGroups.linearReflection
  congr 1
  congr 1
  rw [real_inner_self_eq_norm_sq, he]
  norm_num

/-- *Coroot of a unit vector*: when $\|e\| = 1$, the coroot $e^\vee = 2e/\langle e, e\rangle$
simplifies to $2e$. -/
lemma coroot_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (he : ‖e‖ = 1) :
    FiniteReflectionGroups.coroot e = (2 : ℝ) • e := by
  unfold FiniteReflectionGroups.coroot
  congr 1
  rw [real_inner_self_eq_norm_sq, he]
  norm_num



/-- *Generic vector in the hyperplane $d^\perp$*: given a nonzero $d$ and a finite set $S$ of
nonzero vectors none of which is parallel to $d$, there exists $v \in d^\perp$ (i.e.
$\langle v, d\rangle = 0$) such that $\langle v, \gamma\rangle \ne 0$ for every $\gamma \in S$.
The proof projects $S$ onto $d^\perp$ along $d$ to obtain a nonzero set $S'$, then applies
`exists_inner_ne_zero_of_finite_nonzero` to find a vector $u$ avoiding all kernels in $S'$, and
finally $v = \pi_{d^\perp}(u)$ works by self-adjointness of the projection. -/
lemma exists_in_ker_inner_ne_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (d : E) (hd : d ≠ 0)
    (S : Finset E) (_hS : ∀ γ ∈ S, γ ≠ 0) (hS_ne : S.Nonempty)
    (h_not_prop : ∀ γ ∈ S, ∀ c : ℝ, γ ≠ c • d) :
    ∃ v : E, ⟪v, d⟫_ℝ = 0 ∧ ∀ γ ∈ S, ⟪v, γ⟫_ℝ ≠ 0 := by
  classical

  let πd : E → E := fun x => x - (⟪x, d⟫_ℝ / ⟪d, d⟫_ℝ) • d

  let S' : Finset E := S.image πd

  have hS'_nz : ∀ w ∈ S', w ≠ 0 := by
    intro w hw
    simp only [S', Finset.mem_image] at hw
    obtain ⟨γ, hγ_mem, hγ_eq⟩ := hw
    rw [← hγ_eq]
    intro hc
    exact h_not_prop γ hγ_mem _ (by rwa [sub_eq_zero] at hc)

  have hS'_ne : S'.Nonempty := Finset.Nonempty.image hS_ne πd

  obtain ⟨u, hu⟩ := exists_inner_ne_zero_of_finite_nonzero S' hS'_nz hS'_ne

  refine ⟨πd u, ?_, ?_⟩
  ·
    show ⟪u - (⟪u, d⟫_ℝ / ⟪d, d⟫_ℝ) • d, d⟫_ℝ = 0
    rw [inner_sub_left, real_inner_smul_left, div_mul_cancel₀]
    · ring
    · exact inner_self_ne_zero.mpr hd
  ·
    intro γ hγ_mem

    have self_adj : ⟪πd u, γ⟫_ℝ = ⟪u, πd γ⟫_ℝ := by
      show ⟪u - (⟪u, d⟫_ℝ / ⟪d, d⟫_ℝ) • d, γ⟫_ℝ =
           ⟪u, γ - (⟪γ, d⟫_ℝ / ⟪d, d⟫_ℝ) • d⟫_ℝ
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm d γ]
      ring
    rw [self_adj]
    exact hu (πd γ) (Finset.mem_image.mpr ⟨γ, hγ_mem, rfl⟩)



/-- *Cartan integrality of inward unit normals in a Coxeter arrangement*: for two walls $\eta,
\zeta$ of a chamber $C$ in a Coxeter arrangement, the inner product of their inward unit normals
satisfies $2\langle e_\eta, e_\zeta\rangle \in \mathbb{Z}$. This packages the finite-order
property of the rotation $s_\eta s_\zeta$ into a Cartan integer. The four sign cases (positive
vs negative half-space for each wall) are handled by tracking the appropriate sign in front of
the integer $n$ from the locally-finite assumption. -/
theorem coxeter_arrangement_dihedral_finite
    [CoxeterArrangement arr]
    {C : arr.Chamber} {η ζ : AffineHyperplane E}
    (hη : η ∈ arr.hyperplanes) (hζ : ζ ∈ arr.hyperplanes)
    (hη_wall : η.IsWall C.set) (hζ_wall : ζ.IsWall C.set)
    [inst_η : Decidable (ChamberInPositiveHalfSpace C η)]
    [inst_ζ : Decidable (ChamberInPositiveHalfSpace C ζ)] :
    ∃ n : ℤ, (2 : ℝ) * ⟪inwardUnitNormal C η, inwardUnitNormal C ζ⟫_ℝ = ↑n := by

  obtain ⟨n, hn⟩ := CoxeterArrangement.locally_finite C η ζ hη hζ hη_wall hζ_wall


  unfold inwardUnitNormal
  split_ifs with hη_pos hζ_pos hζ_pos

  · exact ⟨n, hn⟩

  · refine ⟨-n, ?_⟩
    have : ⟪(‖η.normal‖⁻¹) • η.normal, (‖ζ.normal‖⁻¹) • (-ζ.normal)⟫_ℝ =
        -⟪(‖η.normal‖⁻¹) • η.normal, (‖ζ.normal‖⁻¹) • ζ.normal⟫_ℝ := by
      simp [inner_smul_right, inner_neg_right]
    rw [this, mul_neg, hn]; push_cast; ring

  · refine ⟨-n, ?_⟩
    have : ⟪(‖η.normal‖⁻¹) • (-η.normal), (‖ζ.normal‖⁻¹) • ζ.normal⟫_ℝ =
        -⟪(‖η.normal‖⁻¹) • η.normal, (‖ζ.normal‖⁻¹) • ζ.normal⟫_ℝ := by
      simp [inner_smul_left, inner_neg_left]
    rw [this, mul_neg, hn]; push_cast; ring

  · refine ⟨n, ?_⟩
    have : ⟪(‖η.normal‖⁻¹) • (-η.normal), (‖ζ.normal‖⁻¹) • (-ζ.normal)⟫_ℝ =
        ⟪(‖η.normal‖⁻¹) • η.normal, (‖ζ.normal‖⁻¹) • ζ.normal⟫_ℝ := by
      simp [inner_smul_left, inner_smul_right, inner_neg_left, inner_neg_right]
    rw [this, hn]

/-- *Linear independence of two non-parallel unit vectors*: if $e, f$ are unit vectors with $f$
not a scalar multiple of $e$, then $\{e, f\}$ is linearly independent. Using `linearIndependent_fin2`
this reduces to showing $e \ne 0$ (immediate from $\|e\| = 1$) and that no $f = a \cdot e$
relation holds, which contradicts `h_not_parallel`. -/
lemma linearIndependent_of_unit_not_parallel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (h_not_parallel : ¬∃ c : ℝ, f = c • e) :
    LinearIndependent ℝ ![e, f] := by
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  exact ⟨by intro h; rw [h, norm_zero] at hf; linarith,
    fun a ha => h_not_parallel ⟨a⁻¹, by
      have he_ne : e ≠ 0 := by intro h; rw [h, norm_zero] at he; linarith
      have ha_ne : a ≠ 0 := by intro h; rw [h, zero_smul] at ha; exact he_ne ha.symm
      rw [← ha, smul_smul, inv_mul_cancel₀ ha_ne, one_smul]⟩⟩




/-- *Closure passes from a strict half-space to a closed half-space*: if $S$ is contained in the
open half-space $\{x : \langle n, x\rangle > a\}$, then its closure is contained in the closed
half-space $\{x : \langle n, x\rangle \ge a\}$. This is a routine application of
`closure_minimal` using continuity of the inner product. -/
lemma closure_subset_closedHalfSpace (n : E) (a : ℝ) (S : Set E)
    (hS : S ⊆ {x : E | @inner ℝ _ _ n x > a}) :
    closure S ⊆ {x : E | @inner ℝ _ _ n x ≥ a} := by
  apply closure_minimal
  · intro y hy
    have := hS hy
    simp only [mem_setOf_eq] at this ⊢
    linarith
  · exact isClosed_le continuous_const (continuous_const.inner continuous_id')

/-- *A wall meets the closure of its chamber*: if $\eta$ is a wall of $C$, then the hyperplane
carrier $\eta$ intersects the closure of $C$ non-trivially. Direct unpacking of the definition
`IsWall`. -/
lemma wall_carrier_meets_closure {η : AffineHyperplane E} {C : Set E}
    (hw : η.IsWall C) : (η.carrier ∩ closure C).Nonempty := by
  obtain ⟨U, _, hU_nonempty, hU_sub⟩ := hw
  obtain ⟨p, hp⟩ := hU_nonempty
  exact ⟨p, hp.2, hU_sub hp⟩

/-- *Hyperplane equation and chamber half-space in terms of the inward unit normal*: for a wall
$\eta$ of chamber $C$, there is a real number $a$ such that the carrier of $\eta$ equals
$\{y : \langle e_\eta, y\rangle = a\}$ and the chamber lies in the strict half-space
$\{y : \langle e_\eta, y\rangle > a\}$. The constant $a$ is obtained by rescaling $\eta$'s
offset by $\|η.normal\|^{-1}$ and adjusting sign according to which half-space $C$ lies in. -/
lemma inwardNormal_carrier_and_halfspace
    {C : arr.Chamber} {η : AffineHyperplane E}
    (hη : η ∈ arr.hyperplanes) (x : E) (hx : x ∈ C.set)
    [inst_η : Decidable (ChamberInPositiveHalfSpace C η)] :
    ∃ a : ℝ,
      (∀ y, y ∈ η.carrier ↔ @inner ℝ _ _ (inwardUnitNormal C η) y = a) ∧
      (∀ y, y ∈ C.set → @inner ℝ _ _ (inwardUnitNormal C η) y > a) := by
  set e := inwardUnitNormal C η
  rcases chamber_subset_halfSpace C hη with hpos | hneg
  ·
    have he_eq : e = ‖η.normal‖⁻¹ • η.normal := by
      show inwardUnitNormal C η = _
      unfold inwardUnitNormal
      simp [show ChamberInPositiveHalfSpace C η from hpos]
    have h_inv_pos : (0 : ℝ) < ‖η.normal‖⁻¹ :=
      inv_pos.mpr (norm_pos_iff.mpr η.normal_ne_zero)
    refine ⟨η.offset * ‖η.normal‖⁻¹, ?_, ?_⟩
    · intro y
      simp only [AffineHyperplane.carrier, mem_setOf_eq, he_eq, real_inner_smul_left]
      constructor <;> intro h <;> nlinarith
    · intro y hy
      have := hpos hy
      simp only [AffineHyperplane.positiveHalfSpace, mem_setOf_eq] at this
      simp only [he_eq, real_inner_smul_left]
      nlinarith
  ·
    have he_eq : e = ‖η.normal‖⁻¹ • (-η.normal) := by
      show inwardUnitNormal C η = _
      unfold inwardUnitNormal
      split_ifs with h
      · exfalso
        have h1 := h hx
        have h2 := hneg hx
        simp only [AffineHyperplane.positiveHalfSpace, mem_setOf_eq] at h1
        simp only [AffineHyperplane.negativeHalfSpace, mem_setOf_eq] at h2
        linarith
      · rfl
    have h_inv_pos : (0 : ℝ) < ‖η.normal‖⁻¹ :=
      inv_pos.mpr (norm_pos_iff.mpr η.normal_ne_zero)
    refine ⟨-(η.offset * ‖η.normal‖⁻¹), ?_, ?_⟩
    · intro y
      simp only [AffineHyperplane.carrier, mem_setOf_eq, he_eq,
        real_inner_smul_left, inner_neg_left]
      constructor <;> intro h <;> nlinarith
    · intro y hy
      have := hneg hy
      simp only [AffineHyperplane.negativeHalfSpace, mem_setOf_eq] at this
      simp only [he_eq, real_inner_smul_left, inner_neg_left]
      nlinarith


end HyperplaneArrangement
