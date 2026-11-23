/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Reflection.AffineWeylGroups

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Full data for the affine Weyl group $W_a = W ⋉ Λ(\check Φ)$ in an inner product
space $E$: a finite reduced root system, the coroot map $\check α = (2/⟨α,α⟩) α$, the
coroot lattice, crystallographic integrality, stability of roots under $W$, and
integrality of coroot-lattice pairings with roots. -/
structure AffineWeylGroupFullData (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] extends AffineWeylGroupData E where
  roots_finite : Set.Finite roots
  coroot : E → E
  coroot_def : ∀ α ∈ roots, coroot α = (2 / ⟪α, α⟫_ℝ) • α
  coroot_mem_lattice : ∀ α ∈ roots, coroot α ∈ corootLattice
  crystallographic : ∀ α ∈ roots, ∀ β ∈ roots,
    ∃ n : ℤ, ⟪coroot α, β⟫_ℝ = ↑n
  weylGroup_stable_roots : ∀ w ∈ weylGroup, ∀ α ∈ roots,
    (w : E ≃ₗᵢ[ℝ] E) α ∈ roots
  corootLattice_int : ∀ α ∈ roots, ∀ v ∈ corootLattice,
    ∃ m : ℤ, ⟪v, α⟫_ℝ = ↑m

namespace AffineWeylGroupFullData

variable (d : AffineWeylGroupFullData E)

/-- Shorthand for the underlying affine hyperplane arrangement of the affine Weyl data. -/
def affineArr : HyperplaneArrangement E :=
  d.toAffineWeylGroupData.affineArrangement

/-- Two affine hyperplanes are equal if their normals and offsets match. -/
theorem affineHyperplane_ext (h1 h2 : AffineHyperplane E)
    (hn : h1.normal = h2.normal) (ho : h1.offset = h2.offset) :
    h1 = h2 := by
  cases h1; cases h2; simp_all

/-- Section 12.5 of the textbook: the affine hyperplane arrangement
$\{H_{α,k} : α ∈ Φ, k ∈ ℤ\}$ is locally finite — around every point only finitely many
walls accumulate. -/
theorem locallyFinite :
    d.affineArr.IsLocallyFinite := by
  intro x
  refine ⟨1, one_pos, ?_⟩
  have hS_fin : Set.Finite (⋃ α ∈ d.roots,
    ⋃ k ∈ {k : ℤ | |↑k - ⟪α, x⟫_ℝ| < ‖α‖ + 1},
      ({⟨α, ↑k, d.roots_ne_zero α ‹_›⟩} : Set (AffineHyperplane E))) := by
    apply Set.Finite.biUnion' d.roots_finite
    intro α hα
    apply Set.Finite.biUnion
    · apply Set.Finite.subset (Set.finite_Icc
        (⌊⟪α, x⟫_ℝ - (‖α‖ + 1)⌋)
        (⌈⟪α, x⟫_ℝ + (‖α‖ + 1)⌉))
      intro k hk
      simp only [Set.mem_setOf_eq] at hk
      simp only [Set.mem_Icc]
      have hk_abs := abs_sub_lt_iff.mp hk
      exact ⟨Int.floor_le_iff.mpr (by push_cast; linarith [hk_abs.2]),
             Int.le_ceil_iff.mpr (by push_cast; linarith [hk_abs.1])⟩
    · intro _ _; exact Set.finite_singleton _
  apply hS_fin.subset
  intro η ⟨hη_arr, hη_meet⟩
  obtain ⟨y, hy_ball, hy_carrier⟩ := hη_meet
  obtain ⟨α, hα, k, hα_eq, hk_eq⟩ := hη_arr
  simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hy_carrier
  rw [Metric.mem_ball] at hy_ball
  have h_cs : |⟪α, y - x⟫_ℝ| ≤ ‖α‖ * ‖y - x‖ := abs_real_inner_le_norm α (y - x)
  have h_dist : ‖y - x‖ < 1 := by rwa [← dist_eq_norm]
  have h_bound : |↑k - ⟪α, x⟫_ℝ| < ‖α‖ + 1 := by
    have h1 : ⟪η.normal, y⟫_ℝ = η.offset := hy_carrier
    rw [hα_eq] at h1
    calc |↑k - ⟪α, x⟫_ℝ|
        = |⟪α, y⟫_ℝ - ⟪α, x⟫_ℝ| := by congr 1; linarith [h1, hk_eq]
      _ = |⟪α, y - x⟫_ℝ| := by rw [inner_sub_right]
      _ ≤ ‖α‖ * ‖y - x‖ := h_cs
      _ < ‖α‖ * 1 := by
          rcases eq_or_lt_of_le (norm_nonneg α) with h0 | h0
          · exact absurd (norm_eq_zero.mp h0.symm) (d.roots_ne_zero α hα)
          · exact mul_lt_mul_of_pos_left h_dist h0
      _ ≤ ‖α‖ + 1 := by linarith [norm_nonneg α]
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
  exact ⟨α, hα, k, h_bound, affineHyperplane_ext _ _ hα_eq (by linarith [hk_eq])⟩

/-- Translation by an element of the coroot lattice carries any affine wall to another
wall with the same normal direction. -/
theorem stable_corootLattice :
    ∀ v ∈ d.corootLattice, ∀ η ∈ d.affineArr.hyperplanes,
      ∃ η' ∈ d.affineArr.hyperplanes,
        η'.normal = η.normal ∧
        ∀ x : E, x ∈ η'.carrier ↔ (x - v) ∈ η.carrier := by
  intro v hv η hη
  obtain ⟨α, hα, k, hα_eq, hk_eq⟩ := hη
  obtain ⟨m, hm⟩ := d.corootLattice_int α hα v hv
  refine ⟨⟨α, ↑(k + m), d.roots_ne_zero α hα⟩, ⟨α, hα, k + m, rfl, rfl⟩, ?_, ?_⟩
  · exact hα_eq.symm
  · intro x
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq]
    rw [hα_eq, hk_eq, inner_sub_right, real_inner_comm v α]
    constructor
    · intro h; push_cast at h; linarith
    · intro h; push_cast; linarith

/-- The finite Weyl group $W$ permutes affine walls, sending $H_{α,k}$ to $H_{wα,k}$. -/
theorem stable_weylGroup :
    ∀ w ∈ d.weylGroup, ∀ η ∈ d.affineArr.hyperplanes,
      ∃ η' ∈ d.affineArr.hyperplanes,
        η'.normal = (w : E ≃ₗᵢ[ℝ] E) η.normal ∧
        η'.offset = η.offset := by
  intro w hw η hη
  obtain ⟨α, hα, k, hα_eq, hk_eq⟩ := hη
  refine ⟨⟨(w : E ≃ₗᵢ[ℝ] E) α, ↑k, ?_⟩, ?_, ?_, ?_⟩
  · intro h; exact d.roots_ne_zero α hα ((w : E ≃ₗᵢ[ℝ] E).injective (by simp [h]))
  · exact ⟨(w : E ≃ₗᵢ[ℝ] E) α, d.weylGroup_stable_roots w hw α hα, k, rfl, rfl⟩
  · rw [hα_eq]
  · rw [hk_eq]

/-- Formula for the affine reflection across $H_{α,k}$:
$s_{α,k}(v) = v - (⟨α,v⟩ - k) \check α$. -/
def affineReflFun (α : E) (k : ℤ) (v : E) : E :=
  v - (⟪α, v⟫_ℝ - ↑k) • d.coroot α

/-- Formula for the linear reflection through the hyperplane perpendicular to $α$:
$s_α(v) = v - ⟨α,v⟩ \check α$. -/
def linearReflFun (α : E) (v : E) : E :=
  v - ⟪α, v⟫_ℝ • d.coroot α

/-- $s_{α,k}(v) = s_α(v) + k · \check α$: the affine reflection factors as the linear
reflection followed by translation by $k \check α$. -/
theorem affineRefl_eq_translation_comp_linearRefl
    (α : E) (hα : α ∈ d.roots) (k : ℤ) (v : E) :
    d.affineReflFun α k v = d.linearReflFun α v + (k : ℝ) • d.coroot α := by
  simp only [affineReflFun, linearReflFun, sub_smul]
  abel

/-- Translation by $\check α$ realized as a composition of two affine reflections:
$v + \check α = s_{α,1}(s_α(v))$. -/
theorem translation_coroot_eq_comp
    (α : E) (hα : α ∈ d.roots) (v : E) :
    v + d.coroot α = d.affineReflFun α 1 (d.linearReflFun α v) := by
  simp only [affineReflFun, linearReflFun]
  have h_inner : ⟪α, d.coroot α⟫_ℝ = 2 := by
    rw [d.coroot_def α hα, inner_smul_right, div_mul_cancel₀]
    exact (inner_self_ne_zero.mpr (d.roots_ne_zero α hα))
  simp only [inner_sub_right, inner_smul_right, h_inner]
  push_cast
  module

/-- Semidirect-product structure: every affine reflection decomposes as a linear
reflection composed with translation by an element of $Λ(\check Φ)$. -/
theorem semidirect_product_affineWeylGroup :
    ∀ α ∈ d.roots, ∀ k : ℤ, ∀ v : E,
      ∃ (t : E),
        t ∈ d.corootLattice ∧
        d.affineReflFun α k v = d.linearReflFun α v + t := by
  intro α hα k v
  refine ⟨(k : ℝ) • d.coroot α, ?_, ?_⟩
  ·
    have hcr_mem := d.coroot_mem_lattice α hα
    have hzsmul : (k : ℤ) • d.coroot α ∈ d.corootLattice :=
      d.corootLattice.zsmul_mem hcr_mem k
    convert hzsmul using 1
    exact Int.cast_smul_eq_zsmul ℝ k (d.coroot α)
  · exact d.affineRefl_eq_translation_comp_linearRefl α hα k v

/-- The intersection of the linear part group with the translation subgroup is trivial:
if $w v = v + t$ for all $v$, then $t = 0$ and $w = 1$. -/
theorem linear_inter_translation_trivial
    (w : E ≃ₗᵢ[ℝ] E) (t : E)
    (h : ∀ v : E, w v = v + t) :
    t = 0 ∧ w = 1 := by
  have h0 : w 0 = 0 + t := h 0
  have hw0 : w 0 = 0 := map_zero w
  rw [hw0, zero_add] at h0
  constructor
  · exact h0.symm
  · ext v
    have hv := h v
    rw [← h0] at hv
    simp only [LinearIsometryEquiv.coe_one, id_eq]
    simp only [add_zero] at hv
    exact hv

/-- Restatement of the axiom that the Weyl group stabilizes the coroot lattice. -/
theorem weylGroup_normalizes_lattice :
    ∀ w ∈ d.weylGroup, ∀ v ∈ d.corootLattice,
      (w : E ≃ₗᵢ[ℝ] E) v ∈ d.corootLattice :=
  d.weylGroup_stable_corootLattice

/-- Reflection across any affine hyperplane is an involution. -/
theorem reflection_involutive
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (η : AffineHyperplane E) :
    η.reflectionMap * η.reflectionMap = 1 := by
  ext x
  simp only [AffineIsometryEquiv.coe_mul, Function.comp_apply, AffineIsometryEquiv.coe_one, id_eq]
  exact EuclideanGeometry.reflection_reflection η.toAffineSubspace x

/-- The linear reflection coincides with the affine reflection across $H_{α,0}$. -/
theorem linearRefl_eq_affineRefl_zero (α : E) (v : E) :
    d.linearReflFun α v = d.affineReflFun α 0 v := by
  simp only [linearReflFun, affineReflFun, Int.cast_zero, sub_zero]

/-- Affine reflection $s_{α,k}$ is involutive: $s_{α,k}^2 = \mathrm{id}$. -/
theorem affineReflFun_involutive (α : E) (hα : α ∈ d.roots) (k : ℤ) (v : E) :
    d.affineReflFun α k (d.affineReflFun α k v) = v := by
  simp only [affineReflFun]
  have h_inner : ⟪α, d.coroot α⟫_ℝ = 2 := by
    rw [d.coroot_def α hα, inner_smul_right, div_mul_cancel₀]
    exact (inner_self_ne_zero.mpr (d.roots_ne_zero α hα))
  simp only [inner_sub_right, inner_smul_right, h_inner]
  push_cast
  module

/-- The fixed-point set of $s_{α,k}$ is exactly the hyperplane $⟨α, v⟩ = k$. -/
theorem affineReflFun_fixed_iff (α : E) (hα : α ∈ d.roots) (k : ℤ) (v : E) :
    d.affineReflFun α k v = v ↔ ⟪α, v⟫_ℝ = ↑k := by
  simp only [affineReflFun]
  constructor
  · intro h
    have h1 : (⟪α, v⟫_ℝ - ↑k) • d.coroot α = 0 := by
      have h2 : v - (⟪α, v⟫_ℝ - ↑k) • d.coroot α - v = 0 := by rw [h, sub_self]
      rwa [sub_right_comm, sub_self, zero_sub, neg_eq_zero] at h2
    have hcr_ne : d.coroot α ≠ 0 := by
      rw [d.coroot_def α hα]
      intro hc
      rcases smul_eq_zero.mp hc with h1 | h1
      · exact div_ne_zero two_ne_zero (inner_self_ne_zero.mpr (d.roots_ne_zero α hα)) h1
      · exact d.roots_ne_zero α hα h1
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hcr_ne)
  · intro h
    simp [h, sub_self, zero_smul, sub_zero]

/-- Uniqueness of the semidirect decomposition: if $w_1 v + t_1 = w_2 v + t_2$ for all
$v ∈ E$, then $w_1 = w_2$ and $t_1 = t_2$. -/
theorem affineWeylGroup_uniqueDecomposition
    (w₁ w₂ : E ≃ₗᵢ[ℝ] E) (t₁ t₂ : E)
    (h : ∀ v : E, w₁ v + t₁ = w₂ v + t₂) :
    w₁ = w₂ ∧ t₁ = t₂ := by

  have h0 : ∀ v : E, (w₂.symm.trans w₁) v = v + (t₂ - t₁) := by
    intro v
    have hv := h (w₂.symm v)
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply] at hv ⊢

    have : w₁ (w₂.symm v) + t₁ + (-t₁) = v + t₂ + (-t₁) := congr_arg (· + (-t₁)) hv
    simp only [add_neg_cancel_right] at this
    rw [this]; abel


  have key := linear_inter_translation_trivial (w₂.symm.trans w₁) (t₂ - t₁) h0
  constructor
  ·
    have hw : w₂.symm.trans w₁ = 1 := key.2
    ext v
    have hv := LinearIsometryEquiv.ext_iff.mp hw (w₂ v)
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply,
               LinearIsometryEquiv.coe_one, id_eq] at hv
    exact hv
  ·
    have ht : t₂ - t₁ = 0 := key.1
    exact (sub_eq_zero.mp ht).symm

/-- Translation by $\check α$ is the composition of two affine reflections
$s_{α,1} \circ s_{α,0}$. -/
theorem corootTranslation_eq_comp_affineRefls (α : E) (hα : α ∈ d.roots) :
    ∀ v : E, v + d.coroot α =
      d.affineReflFun α 1 (d.affineReflFun α 0 v) := by
  intro v
  rw [← d.linearRefl_eq_affineRefl_zero α v]
  exact d.translation_coroot_eq_comp α hα v

/-- Translation by $-\check α$ is the composition $s_{α,-1} \circ s_{α,0}$. -/
theorem neg_corootTranslation_eq_comp_affineRefls (α : E) (hα : α ∈ d.roots) :
    ∀ v : E, v - d.coroot α =
      d.affineReflFun α (-1) (d.affineReflFun α 0 v) := by
  intro v
  rw [← d.linearRefl_eq_affineRefl_zero α v]
  simp only [affineReflFun, linearReflFun]
  have h_inner : ⟪α, d.coroot α⟫_ℝ = 2 := by
    rw [d.coroot_def α hα, inner_smul_right, div_mul_cancel₀]
    exact (inner_self_ne_zero.mpr (d.roots_ne_zero α hα))
  simp only [inner_sub_right, inner_smul_right, h_inner]
  push_cast
  module

/-- The affine Weyl group $W_a$ is generated by affine reflections: linear reflections
$s_α$ equal $s_{α,0}$, translations by $±\check α$ are products of two affine reflections,
and every affine reflection factors as a linear reflection composed with translation. -/
theorem reflections_generate_affineWeylGroup :

    (∀ α ∈ d.roots, ∀ v : E,
      d.linearReflFun α v = d.affineReflFun α 0 v) ∧

    (∀ α ∈ d.roots, ∀ v : E,
      v + d.coroot α = d.affineReflFun α 1 (d.affineReflFun α 0 v)) ∧

    (∀ α ∈ d.roots, ∀ v : E,
      v - d.coroot α = d.affineReflFun α (-1) (d.affineReflFun α 0 v)) ∧

    (∀ α ∈ d.roots, ∀ k : ℤ, ∀ v : E,
      d.affineReflFun α k v = d.linearReflFun α v + (k : ℝ) • d.coroot α) := by
  exact ⟨
    fun α _ v => d.linearRefl_eq_affineRefl_zero α v,
    fun α hα v => d.corootTranslation_eq_comp_affineRefls α hα v,
    fun α hα v => d.neg_corootTranslation_eq_comp_affineRefls α hα v,
    fun α hα k v => d.affineRefl_eq_translation_comp_linearRefl α hα k v⟩

/-- Proposition 12.5 (first part): the affine hyperplane arrangement is locally finite. -/
theorem proposition_locallyFinite :
    d.affineArr.IsLocallyFinite :=
  d.locallyFinite

/-- Proposition 12.5 (second part): the semidirect-product structure
$W_a = W ⋉ Λ(\check Φ)$ — every affine reflection decomposes as linear part plus a coroot
translation, $W$ normalizes the coroot lattice, and the kernel of the linear-part map is
trivial. -/
theorem proposition_semidirectProduct :

    (∀ α ∈ d.roots, ∀ k : ℤ, ∀ v : E,
      ∃ (t : E),
        t ∈ d.corootLattice ∧
        d.affineReflFun α k v = d.linearReflFun α v + t) ∧

    (∀ w ∈ d.weylGroup, ∀ v ∈ d.corootLattice,
      (w : E ≃ₗᵢ[ℝ] E) v ∈ d.corootLattice) ∧

    (∀ (w : E ≃ₗᵢ[ℝ] E) (t : E),
      (∀ v : E, w v = v + t) → t = 0 ∧ w = 1) :=
  ⟨d.semidirect_product_affineWeylGroup,
   d.weylGroup_normalizes_lattice,
   linear_inter_translation_trivial⟩

/-- Proposition 12.5 (third part): the affine arrangement is stable under translation by
the coroot lattice and under the action of the linear Weyl group. -/
theorem proposition_stable :

    (∀ v ∈ d.corootLattice, ∀ η ∈ d.affineArr.hyperplanes,
      ∃ η' ∈ d.affineArr.hyperplanes,
        η'.normal = η.normal ∧
        ∀ x : E, x ∈ η'.carrier ↔ (x - v) ∈ η.carrier) ∧

    (∀ w ∈ d.weylGroup, ∀ η ∈ d.affineArr.hyperplanes,
      ∃ η' ∈ d.affineArr.hyperplanes,
        η'.normal = (w : E ≃ₗᵢ[ℝ] E) η.normal ∧
        η'.offset = η.offset) :=
  ⟨d.stable_corootLattice, d.stable_weylGroup⟩

end AffineWeylGroupFullData
