/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Atlas.Buildings.code.GeometricAlgebra.WittTheorem
import Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance

namespace Garrett

variable {k : Type*} [Field k] [DecidableEq k] [NeZero (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V]


/-- A linear automorphism `Φ : V ≃ₗ V` is a global isometry of the bilinear form
`B` if it preserves all values of `B`. -/
def IsGlobalIsometry (B : LinearMap.BilinForm k V) (Φ : V ≃ₗ[k] V) : Prop :=
  ∀ v₁ v₂ : V, B (Φ v₁) (Φ v₂) = B v₁ v₂

omit [DecidableEq k] [NeZero (2 : k)] in
omit [DecidableEq k] [NeZero (2 : k)] in
/-- The identity automorphism is always a global isometry. -/
theorem IsGlobalIsometry.refl (B : LinearMap.BilinForm k V) :
    IsGlobalIsometry B (LinearEquiv.refl k V) :=
  fun _ _ => rfl

omit [DecidableEq k] [NeZero (2 : k)] in
/-- The inverse of a global isometry is again a global isometry. -/
theorem IsGlobalIsometry.symm {B : LinearMap.BilinForm k V} {Φ : V ≃ₗ[k] V}
    (hΦ : IsGlobalIsometry B Φ) : IsGlobalIsometry B Φ.symm := by
  intro v₁ v₂
  have h := hΦ (Φ.symm v₁) (Φ.symm v₂)
  simp at h; exact h.symm


/-- An isotropic flag in a formed space `(V, B)` is a strictly increasing chain
of totally isotropic subspaces. -/
structure IsotropicFlag (B : LinearMap.BilinForm k V) where
  len : ℕ
  spaces : Fin len → Submodule k V
  strictMono : StrictMono spaces
  isotropic : ∀ i, IsTotallyIsotropic B (spaces i)

variable {B : LinearMap.BilinForm k V}

/-- The type of an isotropic flag is the sequence of dimensions of its spaces. -/
noncomputable def IsotropicFlag.flagType (F : IsotropicFlag B) : Fin F.len → ℕ :=
  fun i => Module.finrank k (F.spaces i)

/-- Two isotropic flags have the same type if they have the same length and the
same dimension sequence. -/
def IsotropicFlag.sameType (F₁ F₂ : IsotropicFlag B) : Prop :=
  F₁.len = F₂.len ∧
  ∀ (h : F₁.len = F₂.len) (i : Fin F₁.len),
    Module.finrank k (F₁.spaces i) = Module.finrank k (F₂.spaces (Fin.cast h i))


/-- The parabolic subgroup of an isotropic flag `F` consists of all global
isometries of `B` that stabilize every space of `F` setwise. -/
def IsotropicFlag.parabolicSubgroup (F : IsotropicFlag B) : Set (V ≃ₗ[k] V) :=
  { Φ | IsGlobalIsometry B Φ ∧ ∀ i, (F.spaces i).map Φ.toLinearMap = F.spaces i }


omit [DecidableEq k] [NeZero (2 : k)] in
/-- Any linear equivalence between two totally isotropic subspaces is
automatically an isometry of the restricted bilinear form (both forms are zero). -/
theorem isometry_between_isotropic_subspaces
    (U W : Submodule k V)
    (hU : IsTotallyIsotropic B U) (hW : IsTotallyIsotropic B W)
    (φ : U ≃ₗ[k] W) :
    IsSubspaceIsometry B U W φ :=
  fun u₁ u₂ => by rw [hW _ (φ u₁).2 _ (φ u₂).2, hU _ u₁.2 _ u₂.2]

/-- Restriction of a linear automorphism `e : M ≃ₗ M` to a linear equivalence
`U ≃ₗ W` between subspaces `U` and `W = e(U)`. -/
noncomputable def LinearEquiv.restrictSubmodule {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (e : M ≃ₗ[R] M) (U W : Submodule R M)
    (h : U.map e.toLinearMap = W) : U ≃ₗ[R] W :=
  (e.submoduleMap U).trans (LinearEquiv.ofEq _ _ h)

/-- The underlying value of `LinearEquiv.restrictSubmodule` agrees with the
ambient automorphism `e`. -/
theorem LinearEquiv.restrictSubmodule_val {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (e : M ≃ₗ[R] M) (U W : Submodule R M)
    (h : U.map e.toLinearMap = W) (u : U) :
    ((LinearEquiv.restrictSubmodule e U W h) u : M) = e u := by
  simp [LinearEquiv.restrictSubmodule, LinearEquiv.ofEq, LinearEquiv.submoduleMap,
    LinearMap.codRestrict, LinearMap.domRestrict, Equiv.setCongr, Equiv.subtypeEquivProp]

/-- If a linear automorphism `g` stabilizes a submodule `U`, then so does its
inverse `g.symm`. -/
theorem LinearEquiv.symm_stabilizes {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (g : M ≃ₗ[R] M) (U : Submodule R M) (h : U.map g.toLinearMap = U) :
    U.map g.symm.toLinearMap = U := by
  ext w; simp only [Submodule.mem_map]; constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' := hu; rw [← h] at hu'
    obtain ⟨v, hv, rfl⟩ := hu'
    simp; exact hv
  · intro hw
    exact ⟨g w, (by rw [← h]; exact Submodule.mem_map_of_mem hw), by simp⟩


omit [DecidableEq k] in
/-- Two isotropic flags of the same type are conjugate by a global isometry of
the bilinear form `B`. Built using Witt's Extension Theorem. -/
theorem isotropicFlag_equiv_of_sameType
    [FiniteDimensional k V]
    (hBsymm : ∀ x y : V, B x y = B y x)
    (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
    (F₁ F₂ : IsotropicFlag B)
    (hst : F₁.sameType F₂) :
    ∃ Φ : V ≃ₗ[k] V,
      IsGlobalIsometry B Φ ∧
      ∀ i : Fin F₁.len, (F₁.spaces i).map Φ.toLinearMap = F₂.spaces (Fin.cast hst.1 i) := by
  obtain ⟨hlen, hdims⟩ := hst

  match F₁.len, F₂.len, hlen, F₁.spaces, F₂.spaces, F₁.strictMono, F₂.strictMono,
      F₁.isotropic, F₂.isotropic, hdims with
  | 0, 0, rfl, _, _, _, _, _, _, _ =>
    exact ⟨LinearEquiv.refl k V, IsGlobalIsometry.refl B, fun i => Fin.elim0 i⟩
  | n + 1, _, rfl, spaces₁, spaces₂, hm₁, hm₂, hiso₁, hiso₂, hdims =>


    have hdims' : ∀ i : Fin (n + 1),
        Module.finrank k (spaces₁ i) = Module.finrank k (spaces₂ (Fin.cast rfl i)) :=
      fun i => hdims rfl i
    obtain ⟨e, he⟩ := GeometricAlgebra.flag_equiv_aux
      (n + 1) spaces₁ (fun i => spaces₂ (Fin.cast rfl i))
      hm₁
      (fun a b hab => hm₂ (show Fin.cast rfl a < Fin.cast rfl b from hab))
      hdims'

    let last := Fin.last n
    have he_top : (spaces₁ last).map e.toLinearMap = spaces₂ (Fin.cast rfl last) :=
      he last
    let φ := LinearEquiv.restrictSubmodule e _ _ he_top

    have hφ_isom : IsSubspaceIsometry B _ _ φ :=
      isometry_between_isotropic_subspaces _ _
        (hiso₁ last) (hiso₂ (Fin.cast rfl last)) φ

    have hWitt : WittExtensionProp B := Garrett.wittExtensionProp_of_symmetric B hBsymm hnd
    obtain ⟨Φ, hΦ_pres, hΦ_ext⟩ := hWitt hnd _ _ φ hφ_isom


    have hΦ_eq_e : ∀ w ∈ spaces₁ last, Φ w = e w := by
      intro w hw
      have := hΦ_ext ⟨w, hw⟩
      rw [this, LinearEquiv.restrictSubmodule_val]
    refine ⟨Φ, hΦ_pres, fun i => ?_⟩
    ext v
    simp only [Submodule.mem_map, LinearEquiv.coe_toLinearMap]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw_top : w ∈ spaces₁ last := hm₁.monotone (Fin.le_last i) hw
      rw [hΦ_eq_e w hw_top, ← he i]
      exact ⟨w, hw, rfl⟩
    · intro hv
      have hv_top : v ∈ spaces₂ (Fin.cast rfl last) :=
        hm₂.monotone (Fin.le_last (Fin.cast rfl i)) hv
      rw [← he i] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have hw_top : w ∈ spaces₁ last := hm₁.monotone (Fin.le_last i) hw
      exact ⟨w, hw, by rw [hΦ_eq_e w hw_top]; rfl⟩


omit [DecidableEq k] [NeZero (2 : k)] in
/-- Conjugation by a global isometry `Φ` mapping `F₁` to `F₂` provides a bijection
between the parabolic subgroups of `F₁` and `F₂`. -/
theorem parabolicSubgroup_conjugate_of_flag_map
    (F₁ F₂ : IsotropicFlag B) (Φ : V ≃ₗ[k] V)
    (hΦ_isom : IsGlobalIsometry B Φ)
    (hlen : F₁.len = F₂.len)
    (hΦ_maps : ∀ i, (F₁.spaces i).map Φ.toLinearMap = F₂.spaces (Fin.cast hlen i)) :
    ∀ g, g ∈ F₂.parabolicSubgroup ↔
      (Φ.trans (g.trans Φ.symm)) ∈ F₁.parabolicSubgroup := by

  have hΦs := hΦ_isom.symm
  intro g
  simp only [IsotropicFlag.parabolicSubgroup, Set.mem_setOf_eq]
  constructor
  ·
    intro ⟨hg_isom, hg_stab⟩
    constructor
    ·
      intro v₁ v₂
      show B (Φ.symm (g (Φ v₁))) (Φ.symm (g (Φ v₂))) = B v₁ v₂
      rw [hΦs (g (Φ v₁)) (g (Φ v₂)), hg_isom, hΦ_isom]
    ·
      intro i
      ext v; simp only [Submodule.mem_map, LinearEquiv.coe_toLinearMap]
      constructor
      · rintro ⟨w, hw, rfl⟩
        show Φ.symm (g (Φ w)) ∈ F₁.spaces i
        have h1 : Φ w ∈ F₂.spaces (Fin.cast hlen i) := by
          rw [← hΦ_maps i]; exact Submodule.mem_map_of_mem hw
        have h2 : g (Φ w) ∈ F₂.spaces (Fin.cast hlen i) := by
          rw [← hg_stab (Fin.cast hlen i)]; exact Submodule.mem_map_of_mem h1
        rw [← hΦ_maps i] at h2
        simp only [Submodule.mem_map, LinearEquiv.coe_toLinearMap] at h2
        obtain ⟨u, hu, hue⟩ := h2
        rwa [show Φ.symm (g (Φ w)) = u from by
          apply Φ.injective; simp [hue]]
      · intro hv
        refine ⟨Φ.symm (g.symm (Φ v)), ?_, by simp⟩
        have h1 : Φ v ∈ F₂.spaces (Fin.cast hlen i) := by
          rw [← hΦ_maps i]; exact Submodule.mem_map_of_mem hv
        have h2 : g.symm (Φ v) ∈ F₂.spaces (Fin.cast hlen i) := by
          rw [← LinearEquiv.symm_stabilizes g _ (hg_stab (Fin.cast hlen i))]
          exact Submodule.mem_map_of_mem h1
        rw [← hΦ_maps i] at h2
        simp only [Submodule.mem_map, LinearEquiv.coe_toLinearMap] at h2
        obtain ⟨u, hu, hue⟩ := h2
        rwa [show Φ.symm (g.symm (Φ v)) = u from by
          apply Φ.injective; simp [hue]]
  ·
    intro ⟨hconj_isom, hconj_stab⟩
    constructor
    ·
      intro v₁ v₂
      have h := hconj_isom (Φ.symm v₁) (Φ.symm v₂)
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at h
      rw [hΦs (g v₁) (g v₂), hΦs v₁ v₂] at h
      exact h
    ·
      intro j
      let i := Fin.cast hlen.symm j
      have hij : Fin.cast hlen i = j := by simp [i]
      have hconj_i := hconj_stab i
      ext v; constructor
      · rintro ⟨w, hw, rfl⟩
        rw [← hij, ← hΦ_maps i] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        have h1 : (Φ.trans (g.trans Φ.symm)) u ∈ F₁.spaces i := by
          rw [← hconj_i]; exact Submodule.mem_map_of_mem hu
        simp only [LinearEquiv.trans_apply] at h1
        have h2 : Φ (Φ.symm (g (Φ u))) ∈ (F₁.spaces i).map Φ.toLinearMap :=
          Submodule.mem_map_of_mem h1
        rw [hΦ_maps, hij] at h2; simp at h2; exact h2
      · intro hv
        have hv' : v ∈ F₂.spaces (Fin.cast hlen i) := by rwa [hij]
        rw [← hΦ_maps i] at hv'
        obtain ⟨u, hu, rfl⟩ := hv'
        have hinv := LinearEquiv.symm_stabilizes _ _ hconj_i
        refine ⟨g.symm (Φ u), ?_, by simp⟩
        have h1 : (Φ.trans (g.trans Φ.symm)).symm u ∈ F₁.spaces i := by
          rw [← hinv]; exact Submodule.mem_map_of_mem hu
        have h2 : Φ ((Φ.trans (g.trans Φ.symm)).symm u) ∈
            (F₁.spaces i).map Φ.toLinearMap := Submodule.mem_map_of_mem h1
        rw [hΦ_maps, hij] at h2
        simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm,
          LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at h2
        exact h2

omit [DecidableEq k] in
/-- Main theorem: parabolic subgroups of any two isotropic flags of the same type
are conjugate by a global isometry of `B`. -/
theorem isotropicFlag_parabolics_conjugate
    [FiniteDimensional k V]
    (hBsymm : ∀ x y : V, B x y = B y x)
    (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
    (F₁ F₂ : IsotropicFlag B)
    (hst : F₁.sameType F₂) :
    ∃ Φ : V ≃ₗ[k] V,
      IsGlobalIsometry B Φ ∧
      ∀ g, g ∈ F₂.parabolicSubgroup ↔
        (Φ.trans (g.trans Φ.symm)) ∈ F₁.parabolicSubgroup := by
  obtain ⟨Φ, hΦ_isom, hΦ_maps⟩ := isotropicFlag_equiv_of_sameType hBsymm hnd F₁ F₂ hst
  exact ⟨Φ, hΦ_isom, parabolicSubgroup_conjugate_of_flag_map F₁ F₂ Φ hΦ_isom hst.1 hΦ_maps⟩

end Garrett
