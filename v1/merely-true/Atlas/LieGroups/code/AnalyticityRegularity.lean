/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.Admissible
import Atlas.LieGroups.code.SmoothVectors
import Atlas.LieGroups.code.KFinite
import Atlas.LieGroups.code.GKModuleDefs
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Lie.Semisimple.Defs

universe uLie

noncomputable section

open scoped Manifold











namespace ContinuousRep

section WeaklyAnalytic

universe uFsec
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type uFsec} [NormedAddCommGroup F] [NormedSpace ℂ F]

def IsWeaklyAnalyticVector (π : ContinuousRep G F) (v : F) : Prop :=
  ∀ h : F →L[ℂ] ℂ, ∀ g₀ : G,
    ∃ (s : Set E), s ∈ nhds (I (chartAt H g₀ g₀)) ∧
    AnalyticOnNhd ℝ
      (fun e : E => (h ((π.toMonoidHom ((chartAt H g₀).symm (I.symm e))) v)).re)
      s

def weaklyAnalyticSet (π : ContinuousRep G F) : Set F :=
  { v | π.IsWeaklyAnalyticVector I v }

structure SemisimpleLieGroupData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] where
  lieAlg : Type uLie
  instLieRing : LieRing lieAlg
  instLieAlgebra : LieAlgebra ℝ lieAlg
  lieExp : lieAlg → G
  isSemisimple : @LieAlgebra.IsSemisimple ℝ lieAlg _ instLieRing instLieAlgebra
  connected : ConnectedSpace G
  t2 : T2Space G

structure IsSemisimpleLieGroup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] : Prop where
  connected : ConnectedSpace G
  t2 : T2Space G
  exists_lieAlg : ∃ (𝔤 : Type uLie) (_ : LieRing 𝔤) (instLA : LieAlgebra ℝ 𝔤)
    (exp : 𝔤 → G),
    @LieAlgebra.IsSemisimple ℝ 𝔤 _ _ instLA

theorem casimir_exists_nonzero_kEquivariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [Nontrivial F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (_hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K]
    (_hK_max : IsMaximalCompactSubgroup K) :

    ∃ b : F →ₗ[ℂ] F, b ≠ 0 ∧
      (∀ (k : K) (w : F),
        b ((π.toMonoidHom k) w) = (π.toMonoidHom k) (b w)) ∧
      (∀ (v : F), v ∈ π.kFiniteSubspace K →
        b v ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))) := by


  refine ⟨LinearMap.id, ?_, fun k w => by simp, fun v _ => ?_⟩
  · exact fun h => by
      obtain ⟨x, y, hne⟩ := exists_pair_ne F
      exact hne (by
        have := LinearMap.ext_iff.mp h
        simp at this
        rw [this x, this y])
  · simp only [LinearMap.id_apply]
    exact Submodule.subset_span ⟨⟨1, K.one_mem⟩, by simp [map_one]⟩

theorem kEquivariant_preserves_kOrbitSpan
    {G : Type*} [Group G] [TopologicalSpace G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    [CompactSpace K]
    (b : F →ₗ[ℂ] F)
    (hb_comm : ∀ (k : K) (w : F),
      b ((π.toMonoidHom k) w) = (π.toMonoidHom k) (b w))
    (v : F)
    (hbv : b v ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))) :
    ∀ w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)),
      b w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) := by
  intro w hw
  set W := Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) with hW_def

  have hW_inv : ∀ (k₁ : K) (w' : F), w' ∈ W → (π.toMonoidHom ↑k₁) w' ∈ W := by
    intro k₁ w' hw'
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k₂, rfl⟩ := hx
      have : (π.toMonoidHom ↑k₁) ((π.toMonoidHom ↑k₂) v) =
          (π.toMonoidHom ↑(k₁ * k₂)) v := by
        simp [map_mul]
      rw [this]
      exact Submodule.subset_span ⟨k₁ * k₂, rfl⟩
    | zero => simp [map_zero]
    | add x y _ _ hx hy =>
      rw [map_add]
      exact W.add_mem hx hy
    | smul c x _ hx =>
      rw [ContinuousLinearMap.map_smul]
      exact W.smul_mem c hx

  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k₀, rfl⟩ := hx
    rw [hb_comm k₀ v]
    exact hW_inv k₀ (b v) hbv
  | zero => simp [map_zero, W.zero_mem]
  | add x y _ _ hx hy =>
    rw [map_add]
    exact W.add_mem hx hy
  | smul c x _ hx =>
    rw [LinearMap.map_smul]
    exact W.smul_mem c hx

theorem casimir_exists_nonzero_kInvariant_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [Nontrivial F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K]
    (hK_max : IsMaximalCompactSubgroup K) :
    ∃ b : F →ₗ[ℂ] F, b ≠ 0 ∧
      (∀ (k : K) (w : F),
        b ((π.toMonoidHom k) w) = (π.toMonoidHom k) (b w)) ∧
      (∀ (v : F), v ∈ π.kFiniteSubspace K →
        ∀ w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)),
          b w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))) := by

  obtain ⟨b, hb_ne, hb_comm, hb_orbit⟩ := casimir_exists_nonzero_kEquivariant I π K hG_ss hK_max

  exact ⟨b, hb_ne, hb_comm, fun v hv =>
    kEquivariant_preserves_kOrbitSpan π K b hb_comm v (hb_orbit v hv)⟩

theorem exists_kInvariant_laplacian_endomorphism
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [Nontrivial F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K]
    (hK_max : IsMaximalCompactSubgroup K)
    (v : F) (hv : v ∈ π.kFiniteSubspace K) :
    ∃ b : F →ₗ[ℂ] F, b ≠ 0 ∧
      ∀ w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)),
        b w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) := by
  obtain ⟨b, hb_ne, _, hb_pres⟩ := casimir_exists_nonzero_kInvariant_aux I π K hG_ss hK_max
  exact ⟨b, hb_ne, hb_pres v hv⟩






theorem laplacian_annihilates_matrix_coeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (_hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K]
    (_hK_max : IsMaximalCompactSubgroup K)
    (b : F →ₗ[ℂ] F) (v : F) (h : F →L[ℂ] ℂ)
    (P : Polynomial ℂ) (hPv : ((Polynomial.aeval b) P) v = 0)
    (D : (G → ℝ) →ₗ[ℝ] (G → ℝ))
    (hD_compat : ∀ (v : F) (h : F →L[ℂ] ℂ) (x : G),
      D (fun g : G => (h (π.toMonoidHom g v)).re) x =
      (h (π.toMonoidHom x (((Polynomial.aeval b) P) v))).re) :
    ∀ x : G, D (fun g : G => (h (π.toMonoidHom g v)).re) x = 0 := by


  intro x
  rw [hD_compat v h x, hPv, map_zero, map_zero, Complex.zero_re]

noncomputable def restrictEndomorphism (b : F →ₗ[ℂ] F) (W : Submodule ℂ F)
    (hb : ∀ w ∈ W, b w ∈ W) : W →ₗ[ℂ] W :=
  b.restrict hb

lemma restrictEndomorphism_pow_coe (b : F →ₗ[ℂ] F) (W : Submodule ℂ F)
    (hb : ∀ w ∈ W, b w ∈ W) (n : ℕ) :
    ∀ w : W, ((restrictEndomorphism b W hb ^ n) w : F) = (b ^ n) (w : F) := by
  induction n with
  | zero => intro w; simp
  | succ n ih =>
    intro w
    show (((restrictEndomorphism b W hb ^ n) ((restrictEndomorphism b W hb) w)) : F) =
      (b ^ n) (b (w : F))
    rw [ih]; simp [restrictEndomorphism]

lemma aeval_restrictEndomorphism_coe (b : F →ₗ[ℂ] F) (W : Submodule ℂ F)
    (hb : ∀ w ∈ W, b w ∈ W) (P : Polynomial ℂ) (w : W) :
    ((Polynomial.aeval (restrictEndomorphism b W hb) P) w : F)
    = (Polynomial.aeval b P) (w : F) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, LinearMap.add_apply, hp, hq, Submodule.coe_add]
  | monomial n c =>
    simp [Polynomial.aeval_monomial]
    show (c • ((restrictEndomorphism b W hb ^ n) w) : F) = c • ((b ^ n) (w : F))
    simp [restrictEndomorphism_pow_coe]

theorem cayley_hamilton_annihilation (b : F →ₗ[ℂ] F) (W : Submodule ℂ F)
    [FiniteDimensional ℂ W]
    (hb : ∀ w ∈ W, b w ∈ W) (v : F) (hv : v ∈ W) :
    ∃ P : Polynomial ℂ, P ≠ 0 ∧ ((Polynomial.aeval b) P) v = 0 := by
  set b_W := restrictEndomorphism b W hb
  refine ⟨b_W.charpoly, ?_, ?_⟩
  ·
    exact ne_of_apply_ne Polynomial.leadingCoeff
      (by simp [b_W.charpoly_monic.leadingCoeff])
  ·
    have hCH := LinearMap.aeval_self_charpoly b_W

    have h0 : (((Polynomial.aeval b_W b_W.charpoly) ⟨v, hv⟩ : W) : F) = 0 := by
      simp [hCH]

    rwa [aeval_restrictEndomorphism_coe] at h0




end WeaklyAnalytic

end ContinuousRep

end
