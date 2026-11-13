/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Atlas.DifferentialGeometry.code.Hypersurfaces

noncomputable section

open scoped Topology
open LinearMap (ker range)
open Set Filter

theorem ContinuousLinearMap.range_eq_top_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0) : (f : E →ₗ[ℝ] ℝ).range = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro c
  have ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (ContinuousLinearMap.ext (fun v => h v))
  exact ⟨(c / f v) • v, by simp [hv]⟩





theorem inverse_function_theorem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {φ : E → F} {y : E}
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    {f' : E ≃L[ℝ] F}
    (hf' : HasStrictFDerivAt φ (f' : E →L[ℝ] F) y)
    : ∃ (Φ : OpenPartialHomeomorph E F),
      (∀ x ∈ Φ.source, Φ x = φ x) ∧
      y ∈ Φ.source ∧
      IsOpen Φ.source ∧
      IsOpen Φ.target ∧
      ContDiffOn ℝ ⊤ Φ Φ.source ∧
      ContDiffOn ℝ ⊤ Φ.symm Φ.target := by

  let Φ₀ := hf'.toOpenPartialHomeomorph φ

  have hopen_equiv : IsOpen (Set.range (ContinuousLinearEquiv.toContinuousLinearMap
    (σ₁₂ := RingHom.id ℝ) (M₁ := E) (M₂ := F))) := ContinuousLinearEquiv.isOpen
  have hy_mem : fderiv ℝ φ y ∈ Set.range (ContinuousLinearEquiv.toContinuousLinearMap
    (σ₁₂ := RingHom.id ℝ) (M₁ := E) (M₂ := F)) := ⟨f', (hf'.hasFDerivAt.fderiv).symm⟩
  have htop_ne : (⊤ : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_coe
  have hcont_fderiv : Continuous (fderiv ℝ φ) := hφ_smooth.continuous_fderiv htop_ne
  let W := fderiv ℝ φ ⁻¹' (Set.range ContinuousLinearEquiv.toContinuousLinearMap)
  have hW_open : IsOpen W := hcont_fderiv.isOpen_preimage _ hopen_equiv
  have hy_W : y ∈ W := hy_mem

  let Φ := Φ₀.restrOpen W hW_open
  have hΦ_source : Φ.source = Φ₀.source ∩ W := Φ₀.restrOpen_source W hW_open
  have hy_source : y ∈ Φ.source := by
    rw [hΦ_source]
    exact ⟨hf'.mem_toOpenPartialHomeomorph_source, hy_W⟩

  have hΦ_eq : (Φ : E → F) = φ := by
    have h1 : (Φ₀ : E → F) = φ := hf'.toOpenPartialHomeomorph_coe
    have h2 : (Φ : E → F) = (Φ₀ : E → F) := Φ₀.coe_restrOpen hW_open
    exact h2.trans h1
  refine ⟨Φ, ?_, hy_source, Φ.open_source, Φ.open_target, ?_, ?_⟩

  · intro x _
    exact congr_fun hΦ_eq x

  · exact hΦ_eq ▸ hφ_smooth.contDiffOn

  · rw [Φ.open_target.contDiffOn_iff]
    intro a ha
    have hsymm_source : Φ.symm a ∈ Φ.source := Φ.map_target ha
    have hsymm_W : Φ.symm a ∈ W := by
      rw [hΦ_source] at hsymm_source
      exact hsymm_source.2
    obtain ⟨e, he⟩ := hsymm_W

    have hhas_fderiv_Φ : HasFDerivAt (Φ : E → F) (e : E →L[ℝ] F) (Φ.symm a) := by
      have hfderiv_eq : fderiv ℝ φ (Φ.symm a) = (e : E →L[ℝ] F) := he.symm
      have hhas_fderiv : HasFDerivAt φ (e : E →L[ℝ] F) (Φ.symm a) := by
        rw [← hfderiv_eq]
        exact (hφ_smooth.differentiable htop_ne).differentiableAt.hasFDerivAt
      rw [hΦ_eq]
      exact hhas_fderiv

    have hcd : ContDiffAt ℝ ⊤ (Φ : E → F) (Φ.symm a) := by
      rw [hΦ_eq]
      exact hφ_smooth.contDiffAt
    exact Φ.contDiffAt_symm ha hhas_fderiv_Φ hcd

section InverseFunctionTheoremLemmas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem inverse_function_theorem_local_homeomorph
    (φ : E → F) (y : E)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (f' : E ≃L[ℝ] F)
    (hf' : HasStrictFDerivAt φ (f' : E →L[ℝ] F) y) :
    ∃ (Φ : OpenPartialHomeomorph E F),
      (∀ x ∈ Φ.source, Φ x = φ x) ∧
      y ∈ Φ.source ∧
      IsOpen Φ.source ∧
      IsOpen Φ.target ∧
      ContDiffOn ℝ ⊤ Φ Φ.source := by
  let Φ := hf'.toOpenPartialHomeomorph φ
  exact ⟨Φ, fun _ _ => rfl,
    hf'.mem_toOpenPartialHomeomorph_source,
    Φ.open_source,
    Φ.open_target,
    hφ_smooth.contDiffOn⟩

end InverseFunctionTheoremLemmas

structure IsDiffeomorphism
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : E → F) (V : Set E) (U : Set F) : Prop where
  isOpen_source : IsOpen V
  isOpen_target : IsOpen U
  bijOn : Set.BijOn φ V U
  smooth_forward : ContDiffOn ℝ ⊤ φ V
  smooth_inverse : ∃ g : F → E, ContDiffOn ℝ ⊤ g U ∧
    (∀ x ∈ V, g (φ x) = x) ∧ (∀ y ∈ U, φ (g y) = y)

variable {n : ℕ}

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsLocalDefiningFunction (ψ : E → ℝ) (M : Set E) (y : E) : Prop where
  exists_open_nhd : ∃ U : Set E, IsOpen U ∧ y ∈ U ∧
    ContDiffOn ℝ 1 ψ U ∧ (∀ x ∈ U, x ∈ M ↔ ψ x = 0)
  fderiv_ne_zero : fderiv ℝ ψ y ≠ 0

theorem IsLocalDefiningFunction.differentiableAt {ψ : E → ℝ} {M : Set E} {y : E}
    (hψ : IsLocalDefiningFunction ψ M y) : DifferentiableAt ℝ ψ y := by
  obtain ⟨U, hUo, hyU, hψU, _⟩ := hψ.exists_open_nhd
  exact (hψU.differentiableOn (by norm_num)).differentiableAt (hUo.mem_nhds hyU)

def IsHypersurface (M : Set E) : Prop :=
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsLocalDefiningFunction ψ M y

def tangentSpace (ψ : E → ℝ) (y : E) : Submodule ℝ E :=
  LinearMap.ker (fderiv ℝ ψ y).toLinearMap

def IsRegularPoint (ψ : E → ℝ) (y : E) : Prop :=
  DifferentiableAt ℝ ψ y ∧ fderiv ℝ ψ y ≠ 0

theorem mem_tangentSpace_iff {ψ : E → ℝ} {y v : E} :
    v ∈ tangentSpace ψ y ↔ fderiv ℝ ψ y v = 0 := by
  simp [tangentSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

theorem IsLocalDefiningFunction.eq_zero_of_mem {ψ : E → ℝ} {M : Set E} {y : E}
    (hψ : IsLocalDefiningFunction ψ M y) (hy : y ∈ M) : ψ y = 0 := by
  obtain ⟨U, _, hyU, _, hU⟩ := hψ.exists_open_nhd
  exact (hU y hyU).mp hy

theorem IsLocalDefiningFunction.isRegularPoint {ψ : E → ℝ} {M : Set E} {y : E}
    (hψ : IsLocalDefiningFunction ψ M y) : IsRegularPoint ψ y :=
  ⟨hψ.differentiableAt, hψ.fderiv_ne_zero⟩

structure IsSmoothLocalDefiningFunction (ψ : E → ℝ) (M : Set E) (y : E) : Prop where
  exists_open_nhd : ∃ V : Set E, IsOpen V ∧ y ∈ V ∧
    ContDiffOn ℝ ⊤ ψ V ∧
    (∀ x ∈ V, x ∈ M ↔ ψ x = 0) ∧
    (∀ x ∈ V, x ∈ M → fderiv ℝ ψ x ≠ 0)

theorem IsSmoothLocalDefiningFunction.toIsLocalDefiningFunction {ψ : E → ℝ} {M : Set E} {y : E}
    (hy : y ∈ M) (h : IsSmoothLocalDefiningFunction ψ M y) :
    IsLocalDefiningFunction ψ M y := by
  obtain ⟨V, hVo, hyV, hψV, hzero, hderiv⟩ := h.exists_open_nhd
  exact {
    exists_open_nhd := ⟨V, hVo, hyV, hψV.of_le le_top, hzero⟩
    fderiv_ne_zero := hderiv y hyV hy
  }

theorem IsSmoothLocalDefiningFunction.eq_zero_of_mem {ψ : E → ℝ} {M : Set E} {y : E}
    (hψ : IsSmoothLocalDefiningFunction ψ M y) (hy : y ∈ M) : ψ y = 0 := by
  obtain ⟨V, _, hyV, _, hzero, _⟩ := hψ.exists_open_nhd
  exact (hzero y hyV).mp hy

theorem IsSmoothLocalDefiningFunction.isRegularPoint {ψ : E → ℝ} {M : Set E} {y : E}
    (hψ : IsSmoothLocalDefiningFunction ψ M y) (hy : y ∈ M) : IsRegularPoint ψ y := by
  obtain ⟨V, hVo, hyV, hψV, _, hderiv⟩ := hψ.exists_open_nhd
  exact ⟨(hψV.differentiableOn (by norm_num)).differentiableAt (hVo.mem_nhds hyV),
    hderiv y hyV hy⟩

def IsHypersurfaceSubset (M : Set E) : Prop :=
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsSmoothLocalDefiningFunction ψ M y


def IsConvexHypersurface (M : Set E) : Prop :=
  IsHypersurface M ∧
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsLocalDefiningFunction ψ M y ∧
    (∀ z ∈ M, fderiv ℝ ψ y (z - y) ≤ 0)

end Hypersurface

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsPartialParametrization
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : Set E) where
  ambientNhd : Set E
  ambientNhd_open : IsOpen ambientNhd
  paramDomain : Set F
  paramDomain_open : IsOpen paramDomain
  f : F → E
  smooth : ContDiffOn ℝ ⊤ f paramDomain
  injective : Set.InjOn f paramDomain
  image_eq : f '' paramDomain = M ∩ ambientNhd
  immersion : ∀ x ∈ paramDomain, Function.Injective (fderiv ℝ f x)

def AdmitsPartialParametrization (M : Set E) (y : E) : Prop :=
  ∃ ψ : E → ℝ, IsLocalDefiningFunction ψ M y ∧
    ∃ (P : IsPartialParametrization (F := tangentSpace ψ y) M), y ∈ P.ambientNhd



end Hypersurface

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure IsGaussMap (ν : E → E) (M : Set E) : Prop where
  smooth : ContDiffOn ℝ ⊤ ν M
  norm_eq_one : ∀ y ∈ M, ‖ν y‖ = 1
  orthogonal_tangent : ∀ y ∈ M, ∀ ψ : E → ℝ,
    IsLocalDefiningFunction ψ M y →
      ∀ v ∈ tangentSpace ψ y, @inner ℝ _ _ (ν y) v = 0

def IsOrientable (M : Set E) : Prop :=
  ∃ ν : E → E, IsGaussMap ν M

structure OrientedHypersurface (M : Set E) where
  isHypersurface : IsHypersurface M
  gaussMap : E → E
  isGaussMap : IsGaussMap gaussMap M

end Hypersurface

namespace Hypersurface.Curvature

open scoped InnerProductSpace
open Finset

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gaussCurvatureMatrix (ψ : E → ℝ) (y : E) (Y : Fin n → E)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ E) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun j i =>
    if h : (i : ℕ) < n then
      (fderiv ℝ (fderiv ℝ ψ) y) (Y ⟨i, h⟩) (b j)
    else
      (fderiv ℝ ψ y) (b j)

def gaussCurvatureLevelSet (ψ : E → ℝ) (y : E) (Y : Fin n → E)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ E) : ℝ :=
  (gaussCurvatureMatrix ψ y Y b).det / ‖fderiv ℝ ψ y‖ ^ (n + 1)

def shapeOperatorLevelSet (ψ : E → ℝ) (y : E) (Y : Fin n → E) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (1 / ‖fderiv ℝ ψ y‖) * (fderiv ℝ (fderiv ℝ ψ) y) (Y i) (Y j)

end Hypersurface.Curvature

end







open scoped Topology
open LinearMap (ker range)
open Set Filter

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsTangentCurve (c : ℝ → E) (M : Set E) (y v : E) : Prop where
  at_zero : c 0 = y
  hasDerivAt : HasDerivAt c v 0
  image_in_M : ∀ᶠ t in 𝓝 0, c t ∈ M

theorem tangent_of_curve {ψ : E → ℝ} {M : Set E} {y v : E} {c : ℝ → E}
    (hψ : IsLocalDefiningFunction ψ M y)
    (hc : IsTangentCurve c M y v) :
    v ∈ tangentSpace ψ y := by
  rw [tangentSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  obtain ⟨U, hUo, hyU, hψU, hzero⟩ := hψ.exists_open_nhd
  have hψ_diff : DifferentiableAt ℝ ψ y :=
    (hψU.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt (hUo.mem_nhds hyU)
  have hψ_hasFDerivAt : HasFDerivAt ψ (fderiv ℝ ψ y) y := hψ_diff.hasFDerivAt

  have hchain : HasDerivAt (ψ ∘ c) ((fderiv ℝ ψ y) v) 0 := by
    have key : HasFDerivAt ψ (fderiv ℝ ψ y) (c 0) := by rw [hc.at_zero]; exact hψ_hasFDerivAt
    exact key.comp_hasDerivAt 0 hc.hasDerivAt

  have hconst : HasDerivAt (ψ ∘ c) 0 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    have h1 : ∀ᶠ t in 𝓝 0, c t ∈ U := by
      have hcont : ContinuousAt c 0 := hc.hasDerivAt.continuousAt
      exact hcont.preimage_mem_nhds (by rw [hc.at_zero]; exact hUo.mem_nhds hyU)
    filter_upwards [h1, hc.image_in_M] with t ht1 ht2
    simp [Function.comp, (hzero (c t) ht1).mp ht2]
  exact hchain.unique hconst

theorem curve_of_tangent [FiniteDimensional ℝ E] {ψ : E → ℝ} {M : Set E} {y : E} {v : E}
    (hψ : IsLocalDefiningFunction ψ M y)
    (hy : y ∈ M)
    (hv : v ∈ tangentSpace ψ y)
    (hstrict : HasStrictFDerivAt ψ (fderiv ℝ ψ y) y) :
    ∃ c : ℝ → E, IsTangentCurve c M y v := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hrange : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).range = ⊤ :=
    ContinuousLinearMap.range_eq_top_of_ne_zero _ hψ.fderiv_ne_zero
  let g := hstrict.implicitFunction ψ (fderiv ℝ ψ y) hrange
  have hψ_zero : ψ y = 0 := by
    obtain ⟨U, _, hyU, _, hU⟩ := hψ.exists_open_nhd
    exact (hU y hyU).mp hy
  have hg_zero : g 0 0 = y := by
    have := hstrict.implicitFunction_apply_image hrange
    rwa [hψ_zero] at this
  have hg_map : ∀ᶠ p : ℝ × (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker in
      𝓝 (0, (0 : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker)),
      ψ (g p.1 p.2) = p.1 := by
    have := hstrict.map_implicitFunction_eq hrange
    rwa [hψ_zero] at this
  have hg_deriv : HasStrictFDerivAt (g 0)
      (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker.subtypeL 0 := by
    have := hstrict.to_implicitFunction hrange
    rwa [hψ_zero] at this
  have hv_mem : v ∈ (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker := by
    rwa [tangentSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
  let w : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker := ⟨v, hv_mem⟩

  have hderiv_c : HasDerivAt (fun t : ℝ => g 0 (t • w)) v 0 := by
    have hderiv_smul : HasDerivAt (fun t : ℝ => t • w) w 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have key : (fun t : ℝ => t • w) 0 = 0 := by simp
    have hg' : HasFDerivAt (g 0) (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker.subtypeL
        ((fun t : ℝ => t • w) 0) := by
      rw [key]; exact hg_deriv.hasFDerivAt
    have hcomp := hg'.comp_hasDerivAt (x := (0 : ℝ)) hderiv_smul
    simp at hcomp
    exact hcomp
  let c : ℝ → E := fun t => g 0 (t • w)
  refine ⟨c, ?_, ?_, ?_⟩

  · show g 0 ((0 : ℝ) • w) = y
    simp [hg_zero]

  · exact hderiv_c

  · show ∀ᶠ t in 𝓝 0, g 0 (t • w) ∈ M
    obtain ⟨U, hUo, hyU, _, hzero⟩ := hψ.exists_open_nhd

    have hψ_eq_zero : ∀ᶠ t in 𝓝 (0 : ℝ), ψ (g 0 (t • w)) = 0 := by
      have hcont_tw : ContinuousAt (fun t : ℝ => ((0 : ℝ), t • w)) 0 := by fun_prop
      have h0 : (fun t : ℝ => ((0 : ℝ), t • w)) 0 =
          (0, (0 : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker)) := by simp
      have hmem := hcont_tw.eventually (h0 ▸ hg_map)
      simpa [Function.comp] using hmem

    have hcont_c : ContinuousAt c 0 := hderiv_c.continuousAt
    have hc_in_U : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ U := by
      apply hcont_c.preimage_mem_nhds
      change U ∈ 𝓝 (c 0)
      simp only [c, zero_smul, hg_zero]
      exact hUo.mem_nhds hyU
    filter_upwards [hψ_eq_zero, hc_in_U] with t ht1 ht2
    exact (hzero (g 0 (t • w)) ht2).mpr ht1

end Hypersurface
