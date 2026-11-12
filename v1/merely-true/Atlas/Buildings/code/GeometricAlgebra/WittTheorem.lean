/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Atlas.Buildings.code.GeometricAlgebra.BilinFormComplementation
import Atlas.Buildings.code.GeometricAlgebra.WittExtensionProof

set_option maxHeartbeats 4000000

namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]
variable {V : Type*} [AddCommGroup V] [Module k V]


variable (B : LinearMap.BilinForm k V)

/-- Bilinear reflection of `v` through the hyperplane orthogonal to a non-isotropic
vector `a`: subtracts off twice the `a`-component measured by `B`. -/
noncomputable def bilinReflect (a : V) (_ha : B a a ≠ 0) (v : V) : V :=
  v - (2 * B v a / B a a) • a

/-- The bilinear reflection through `a` packaged as a linear map `V →ₗ[k] V`. -/
noncomputable def bilinReflectLM (a : V) (ha : B a a ≠ 0) : V →ₗ[k] V where
  toFun := bilinReflect B a ha
  map_add' := by
    intro x y
    simp only [bilinReflect, map_add, LinearMap.add_apply]
    module
  map_smul' := by
    intro c x
    simp only [bilinReflect, map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    module

/-- The bilinear reflection is an involution: applying it twice returns the
original vector. -/
theorem bilinReflect_invol (a : V) (ha : B a a ≠ 0) (v : V) :
    bilinReflect B a ha (bilinReflect B a ha v) = v := by
  simp only [bilinReflect]
  set c := 2 * B v a / B a a with hc_def

  have hBva : B (v - c • a) a = B v a - c * B a a := by
    simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hBva]

  have hcoeff : 2 * (B v a - c * B a a) / B a a = -c := by
    rw [hc_def]; field_simp; ring
  rw [hcoeff]

  simp [neg_smul, sub_neg_eq_add, sub_add_cancel]

omit [NeZero (2 : k)] in
/-- The bilinear reflection through a non-isotropic vector preserves a symmetric
bilinear form: `B (Refl v₁) (Refl v₂) = B v₁ v₂`. -/
theorem bilinReflect_preserves (hBsymm : ∀ x y : V, B x y = B y x)
    (a : V) (ha : B a a ≠ 0) (v₁ v₂ : V) :
    B (bilinReflect B a ha v₁) (bilinReflect B a ha v₂) = B v₁ v₂ := by
  simp only [bilinReflect]
  set c₁ := 2 * B v₁ a / B a a
  set c₂ := 2 * B v₂ a / B a a

  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]

  rw [hBsymm a v₂]

  simp only [c₁, c₂]
  field_simp
  ring

/-- The bilinear reflection through `a`, packaged as a linear equivalence
`V ≃ₗ[k] V` (using its involutive property). -/
noncomputable def bilinReflectEquiv (a : V) (ha : B a a ≠ 0) : V ≃ₗ[k] V :=
  LinearEquiv.ofInvolutive (bilinReflectLM B a ha) (bilinReflect_invol B a ha)

omit [NeZero (2 : k)] in
/-- If `x` and `y` have the same `B`-norm and their difference is non-isotropic,
the bilinear reflection through `x - y` sends `x` to `y`. -/
theorem bilinReflect_maps (hBsymm : ∀ x y : V, B x y = B y x)
    (x y : V) (hxy : B (x - y) (x - y) ≠ 0)
    (hBxy : B x x = B y y) :
    bilinReflect B (x - y) hxy x = y := by
  simp only [bilinReflect]

  have hBx_xy : B x (x - y) = B x x - B x y := by
    simp [map_sub]

  have hB_xy_xy : B (x - y) (x - y) = 2 * (B x x - B x y) := by
    simp [map_sub, LinearMap.sub_apply, hBsymm y x]
    rw [hBxy]; ring
  rw [hBx_xy, hB_xy_xy]

  have h2ne : (2 : k) * (B x x - B x y) ≠ 0 := by rwa [hB_xy_xy] at hxy
  rw [show (2 : k) * (B x x - B x y) / (2 * (B x x - B x y)) = 1 from div_self h2ne]

  simp [one_smul]

/-- If `x` is non-isotropic and `B x x = B y y`, then at least one of `x - y`
or `x + y` is also non-isotropic. -/
theorem exists_noniso_difference (hBsymm : ∀ x y : V, B x y = B y x)
    (x y : V) (hBxx : B x x ≠ 0) (hBxy : B x x = B y y) :
    B (x - y) (x - y) ≠ 0 ∨ B (x + y) (x + y) ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  apply hBxx

  have hB_sub : B (x - y) (x - y) = 2 * B x x - 2 * B x y := by
    simp [map_sub, LinearMap.sub_apply, hBsymm y x, hBxy]; ring
  have hB_add : B (x + y) (x + y) = 2 * B x x + 2 * B x y := by
    simp [map_add, LinearMap.add_apply, hBsymm y x, hBxy]; ring
  rw [hB_sub] at h1
  rw [hB_add] at h2

  have eq1 : B x y = B x x :=
    mul_left_cancel₀ (NeZero.ne (2 : k)) (sub_eq_zero.mp h1).symm

  rw [eq1] at h2
  have h4 : (2 + 2) * B x x = 0 := by ring_nf; ring_nf at h2; exact h2

  have h2ne : (2 : k) ≠ 0 := NeZero.ne 2
  have hfour : (2 : k) + 2 ≠ 0 := by
    intro hc
    exact h2ne ((mul_eq_zero.mp (by ring_nf; ring_nf at hc; exact hc)).resolve_left h2ne)
  exact (mul_eq_zero.mp h4).resolve_left hfour

/-- The action of the `bilinReflectEquiv` linear equivalence agrees with the
underlying `bilinReflect` function. -/
theorem bilinReflectEquiv_apply (a : V) (ha : B a a ≠ 0) (v : V) :
    bilinReflectEquiv B a ha v = bilinReflect B a ha v := by
  simp [bilinReflectEquiv, bilinReflectLM, LinearEquiv.ofInvolutive]

/-- The bilinear reflection through `a` sends `-a` back to `a`. -/
theorem bilinReflect_neg_self (a : V) (ha : B a a ≠ 0) :
    bilinReflect B a ha (-a) = a := by
  simp only [bilinReflect, map_neg, LinearMap.neg_apply]
  have : 2 * -B a a / B a a = -2 := by field_simp
  rw [this]; simp [neg_smul]; module

/-- The bilinear reflection linear equivalence preserves the symmetric bilinear
form `B`. -/
theorem bilinReflectEquiv_preserves (hBsymm : ∀ x y : V, B x y = B y x)
    (a : V) (ha : B a a ≠ 0) (v₁ v₂ : V) :
    B (bilinReflectEquiv B a ha v₁) (bilinReflectEquiv B a ha v₂) = B v₁ v₂ := by
  simp only [bilinReflectEquiv_apply]
  exact bilinReflect_preserves B hBsymm a ha v₁ v₂

omit [NeZero (2 : k)] in
/-- Vectors orthogonal to `a` are fixed by the bilinear reflection through `a`. -/
theorem bilinReflect_of_ortho (a : V) (ha : B a a ≠ 0) (v : V) (hv : B v a = 0) :
    bilinReflect B a ha v = v := by
  simp only [bilinReflect, hv, mul_zero, zero_div, zero_smul, sub_zero]

/-- Inductive step in Witt's extension theorem when `U` contains a non-isotropic
vector `x`: assuming the inductive hypothesis for smaller subspaces, the isometry
`φ : U ≃ W` extends to an isometry of the whole space `V`. -/
theorem wittExtension_noniso_step
    [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V)
    (hBsymm : ∀ x y : V, B x y = B y x)
    (_hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
    (U W : Submodule k V) (φ : U ≃ₗ[k] W)
    (hφ : IsSubspaceIsometry B U W φ)
    {x : V} (hxU : x ∈ U) (hx_noniso : B x x ≠ 0)

    (ih : ∀ (U' W' : Submodule k V) (φ' : U' ≃ₗ[k] W'),
      IsSubspaceIsometry B U' W' φ' →
      Module.finrank k U' < Module.finrank k U →
      ∃ Φ : V ≃ₗ[k] V,
        (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧
        (∀ u : U', Φ (u : V) = (φ' u : V))) :
    ∃ Φ : V ≃ₗ[k] V,
      (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧
      (∀ u : U, Φ (u : V) = (φ u : V)) := by


  set y : V := (φ ⟨x, hxU⟩ : V) with hy_def
  have hByy : B y y = B x x := by
    have := hφ ⟨x, hxU⟩ ⟨x, hxU⟩; simp at this; exact this
  have hy_noniso : B y y ≠ 0 := hByy ▸ hx_noniso

  have hx_not_ortho : ¬ LinearMap.BilinForm.IsOrtho B x x := hx_noniso
  have hy_not_ortho : ¬ LinearMap.BilinForm.IsOrtho B y y := hy_noniso

  have hx_ne : x ≠ 0 := by intro h; rw [h] at hx_noniso; simp at hx_noniso


  have hx_compl : IsCompl (k ∙ x) (LinearMap.BilinForm.orthogonal B (k ∙ x)) :=
    LinearMap.BilinForm.isCompl_span_singleton_orthogonal hx_not_ortho

  have hy_compl : IsCompl (k ∙ y) (LinearMap.BilinForm.orthogonal B (k ∙ y)) :=
    LinearMap.BilinForm.isCompl_span_singleton_orthogonal hy_not_ortho


  set xperp := LinearMap.BilinForm.orthogonal B (k ∙ x)
  set yperp := LinearMap.BilinForm.orthogonal B (k ∙ y)
  set U' := U ⊓ xperp
  set W' := W ⊓ yperp


  have hφ_maps : ∀ (u' : U'), (φ (Submodule.inclusion (inf_le_left (a := U) (b := xperp)) u') : V) ∈ W' := by
    intro u'
    constructor
    · exact (φ _).2
    ·
      rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [Submodule.mem_span_singleton] at hn
      obtain ⟨a, rfl⟩ := hn
      unfold LinearMap.BilinForm.IsOrtho
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]


      have hu'_xperp : (u' : V) ∈ xperp := (Submodule.mem_inf.mp u'.2).2
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hu'_xperp
      have hortho := hu'_xperp x (Submodule.mem_span_singleton_self x)
      unfold LinearMap.BilinForm.IsOrtho at hortho

      have hB_eq : B (φ (Submodule.inclusion inf_le_left u') : V) y = B (u' : V) x := by
        have h := hφ (Submodule.inclusion inf_le_left u') ⟨x, hxU⟩
        simp at h; exact h

      rw [hBsymm y _, hB_eq, hBsymm _ x, hortho, mul_zero]


  let φ'_lm : U' →ₗ[k] W' :=
    { toFun := fun u' => ⟨(φ (Submodule.inclusion inf_le_left u') : V), hφ_maps u'⟩
      map_add' := by intro a b; ext; simp [map_add, Submodule.coe_add]
      map_smul' := by intro c a; ext; simp [map_smul] }

  have hφ'_inj : Function.Injective φ'_lm := by
    intro a b h
    have h' : (φ'_lm a : V) = (φ'_lm b : V) := by rw [h]
    simp only [φ'_lm, LinearMap.coe_mk, AddHom.coe_mk] at h'
    have hinj := φ.injective (Subtype.ext h')


    have : (a : V) = (b : V) := by
      have h2 : (Submodule.inclusion inf_le_left a : V) = (Submodule.inclusion inf_le_left b : V) :=
        congr_arg Subtype.val hinj
      simpa using h2
    exact Subtype.ext this


  haveI : FiniteDimensional k U' := inferInstance
  haveI : FiniteDimensional k W' := inferInstance

  have hkx_le_U : (k ∙ x) ≤ U := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxU)
  have hky_le_W : (k ∙ y) ≤ W := by
    rw [Submodule.span_le]; intro v hv
    rw [Set.mem_singleton_iff] at hv; rw [hv]; exact (φ ⟨x, hxU⟩).2

  have hU_eq : (k ∙ x) ⊔ U' = U := by
    have h1 : (k ∙ x) ⊔ U' ≤ U := sup_le hkx_le_U inf_le_left
    have h2 : U ≤ (k ∙ x) ⊔ U' := by
      intro u hu
      have hu_top : u ∈ (⊤ : Submodule k V) := Submodule.mem_top
      rw [← hx_compl.codisjoint.eq_top] at hu_top
      rw [Submodule.mem_sup] at hu_top
      obtain ⟨a, ha, b, hb, hab⟩ := hu_top
      rw [Submodule.mem_sup]
      refine ⟨a, ha, b, ?_, hab⟩
      refine Submodule.mem_inf.mpr ⟨?_, hb⟩
      have hbeq : b = u - a := eq_sub_of_add_eq' hab
      rw [hbeq]; exact U.sub_mem hu (hkx_le_U ha)
    exact le_antisymm h1 h2

  have hkx_inf_U' : (k ∙ x) ⊓ U' = ⊥ := by
    rw [eq_bot_iff]; intro v hv
    rw [Submodule.mem_inf] at hv
    have hv1 := hv.1
    have hv2 : v ∈ xperp := (Submodule.mem_inf.mp hv.2).2
    have := hx_compl.disjoint
    rw [disjoint_iff] at this
    rw [← this]
    exact Submodule.mem_inf.mpr ⟨hv1, hv2⟩

  have hW_eq : (k ∙ y) ⊔ W' = W := by
    have h1 : (k ∙ y) ⊔ W' ≤ W := sup_le hky_le_W inf_le_left
    have h2 : W ≤ (k ∙ y) ⊔ W' := by
      intro w hw
      have hw_top : w ∈ (⊤ : Submodule k V) := Submodule.mem_top
      rw [← hy_compl.codisjoint.eq_top] at hw_top
      rw [Submodule.mem_sup] at hw_top
      obtain ⟨a, ha, b, hb, hab⟩ := hw_top
      rw [Submodule.mem_sup]
      refine ⟨a, ha, b, ?_, hab⟩
      refine Submodule.mem_inf.mpr ⟨?_, hb⟩
      have hbeq : b = w - a := eq_sub_of_add_eq' hab
      rw [hbeq]; exact W.sub_mem hw (hky_le_W ha)
    exact le_antisymm h1 h2
  have hy_ne : y ≠ 0 := by intro h; rw [h] at hy_noniso; simp at hy_noniso
  have hky_inf_W' : (k ∙ y) ⊓ W' = ⊥ := by
    rw [eq_bot_iff]; intro v hv
    rw [Submodule.mem_inf] at hv
    have hv1 := hv.1
    have hv2 : v ∈ yperp := (Submodule.mem_inf.mp hv.2).2
    have := hy_compl.disjoint
    rw [disjoint_iff] at this
    rw [← this]
    exact Submodule.mem_inf.mpr ⟨hv1, hv2⟩

  have hrank_eq : Module.finrank k U' = Module.finrank k W' := by
    have hUW : Module.finrank k U = Module.finrank k W := LinearEquiv.finrank_eq φ
    have hU_rank : Module.finrank k U = 1 + Module.finrank k U' := by
      have := Submodule.finrank_sup_add_finrank_inf_eq (k ∙ x) U'
      rw [hU_eq] at this
      rw [hkx_inf_U'] at this
      simp [finrank_span_singleton hx_ne] at this
      omega
    have hW_rank : Module.finrank k W = 1 + Module.finrank k W' := by
      have := Submodule.finrank_sup_add_finrank_inf_eq (k ∙ y) W'
      rw [hW_eq] at this
      rw [hky_inf_W'] at this
      simp [finrank_span_singleton hy_ne] at this
      omega
    omega


  have hφ'_surj : Function.Surjective φ'_lm := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank_eq]
  let φ' : U' ≃ₗ[k] W' := LinearEquiv.ofBijective φ'_lm ⟨hφ'_inj, hφ'_surj⟩


  have hφ'_isom : IsSubspaceIsometry B U' W' φ' := by
    intro u₁ u₂
    show B ((φ' u₁ : V)) ((φ' u₂ : V)) = B (u₁ : V) (u₂ : V)

    have hcoe : ∀ u : U', (φ' u : V) = (φ (Submodule.inclusion inf_le_left u) : V) := by
      intro u; simp [φ', LinearEquiv.ofBijective_apply, φ'_lm]
    rw [hcoe, hcoe]
    exact hφ _ _


  have hU'_lt : Module.finrank k U' < Module.finrank k U := by
    have hU_rank : Module.finrank k U = 1 + Module.finrank k U' := by
      have := Submodule.finrank_sup_add_finrank_inf_eq (k ∙ x) U'
      rw [hU_eq] at this
      rw [hkx_inf_U'] at this
      simp [finrank_span_singleton hx_ne] at this
      omega
    omega


  obtain ⟨Ψ, hΨ_isom, hΨ_ext⟩ := ih U' W' φ' hφ'_isom hU'_lt


  set z : V := Ψ x
  have hBzz : B z z = B y y := by
    show B (Ψ x) (Ψ x) = B y y
    rw [hΨ_isom x x, hByy]
  have hz_noniso : B z z ≠ 0 := hBzz ▸ hy_noniso

  have hortho_zy : ∀ u' : U', B ((φ' u' : V)) (z - y) = 0 ∧ B ((φ' u' : V)) (z + y) = 0 := by
    intro u'
    have hcoe : (φ' u' : V) = (φ (Submodule.inclusion inf_le_left u') : V) := by
      simp [φ', LinearEquiv.ofBijective_apply, φ'_lm]
    have hBwz : B (φ' u' : V) z = 0 := by


      have hΨu' : Ψ (u' : V) = (φ' u' : V) := by
        have := hΨ_ext u'; rw [this]
      rw [← hΨu']
      show B (Ψ (u' : V)) (Ψ x) = 0
      rw [hΨ_isom]
      have hu'_xperp : (u' : V) ∈ xperp := (Submodule.mem_inf.mp u'.2).2
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hu'_xperp
      have := hu'_xperp x (Submodule.mem_span_singleton_self x)
      unfold LinearMap.BilinForm.IsOrtho at this
      rw [hBsymm] at this
      exact this
    have hBwy : B (φ' u' : V) y = 0 := by
      have hφ'_in_W' : (φ' u' : V) ∈ W' := (φ' u').2
      have hyperp_mem : (φ' u' : V) ∈ yperp := (Submodule.mem_inf.mp hφ'_in_W').2
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hyperp_mem
      have := hyperp_mem y (Submodule.mem_span_singleton_self y)
      unfold LinearMap.BilinForm.IsOrtho at this
      rw [hBsymm] at this
      exact this
    constructor
    · simp [map_sub, hBwz, hBwy]
    · simp [map_add, hBwz, hBwy]


  have hext_from_decomp :
    ∀ (Φ_val : V ≃ₗ[k] V),
    (∀ v₁ v₂, B (Φ_val v₁) (Φ_val v₂) = B v₁ v₂) →
    Φ_val x = y →
    (∀ u' : U', Φ_val (u' : V) = (φ (Submodule.inclusion inf_le_left u') : V)) →
    (∀ u : U, Φ_val (u : V) = (φ u : V)) := by
    intro Φ_val _ hΦx hΦ_on_U' u
    have hu_mem : (u : V) ∈ U := u.2
    have hu_in_sum : (u : V) ∈ (k ∙ x) ⊔ xperp := by
      rw [hx_compl.codisjoint.eq_top]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hu_in_sum
    obtain ⟨sx, hsx, p, hp, hup⟩ := hu_in_sum
    rw [Submodule.mem_span_singleton] at hsx
    obtain ⟨a_coeff, rfl⟩ := hsx
    have hp_U : p ∈ U := by
      have hbeq : p = (u : V) - a_coeff • x := eq_sub_of_add_eq' hup
      rw [hbeq]; exact U.sub_mem hu_mem (U.smul_mem a_coeff hxU)
    have hp_U' : p ∈ U' := Submodule.mem_inf.mpr ⟨hp_U, hp⟩
    have hu_decomp : (u : V) = a_coeff • x + p := hup.symm
    rw [hu_decomp, map_add, map_smul, hΦx, hΦ_on_U' ⟨p, hp_U'⟩]

    have hφx : (φ ⟨x, hxU⟩ : V) = y := rfl


    symm

    have hu_eq : u = a_coeff • ⟨x, hxU⟩ + ⟨p, hp_U⟩ := by
      ext; simp [hu_decomp]
    rw [hu_eq, map_add, map_smul, Submodule.coe_add, Submodule.coe_smul]
    congr 1

  rcases exists_noniso_difference B hBsymm z y hz_noniso hBzz with h_sub | h_add
  ·
    let ρ := bilinReflectEquiv B (z - y) h_sub
    have hρ_maps : ρ z = y := by
      rw [bilinReflectEquiv_apply]
      exact bilinReflect_maps B hBsymm z y h_sub hBzz
    have hρ_preserves : ∀ v₁ v₂, B (ρ v₁) (ρ v₂) = B v₁ v₂ :=
      bilinReflectEquiv_preserves B hBsymm (z - y) h_sub

    have hρ_fixes_W' : ∀ u' : U', ρ (φ' u' : V) = (φ' u' : V) := by
      intro u'
      rw [bilinReflectEquiv_apply]
      exact bilinReflect_of_ortho B (z - y) h_sub (φ' u' : V) (hortho_zy u').1

    let Φ := Ψ.trans ρ
    refine ⟨Φ, ?_, ?_⟩
    ·
      intro v₁ v₂
      simp only [Φ, LinearEquiv.trans_apply]
      rw [hρ_preserves, hΨ_isom]
    ·
      apply hext_from_decomp Φ
      · intro v₁ v₂; simp only [Φ, LinearEquiv.trans_apply]; rw [hρ_preserves, hΨ_isom]
      · show ρ (Ψ x) = y; exact hρ_maps
      · intro u'
        show ρ (Ψ (u' : V)) = (φ (Submodule.inclusion inf_le_left u') : V)
        rw [hΨ_ext u']
        have hcoe : (φ' u' : V) = (φ (Submodule.inclusion inf_le_left u') : V) := by
          simp [φ', LinearEquiv.ofBijective_apply, φ'_lm]
        rw [← hcoe]
        exact hρ_fixes_W' u'
  ·
    let ρ₁ := bilinReflectEquiv B (z + y) h_add
    have hρ₁_maps : ρ₁ z = -y := by
      rw [bilinReflectEquiv_apply]
      simp only [bilinReflect]
      have hBz_zy : B z (z + y) = B z z + B z y := by simp [map_add]
      have hB_zy_zy : B (z + y) (z + y) = 2 * (B z z + B z y) := by
        simp [map_add, LinearMap.add_apply, hBsymm y z]; rw [hBzz]; ring
      rw [hBz_zy, hB_zy_zy]
      have h2ne : (2 : k) * (B z z + B z y) ≠ 0 := by rwa [hB_zy_zy] at h_add
      rw [show (2 : k) * (B z z + B z y) / (2 * (B z z + B z y)) = 1 from div_self h2ne]
      simp [one_smul]
    have hρ₁_preserves : ∀ v₁ v₂, B (ρ₁ v₁) (ρ₁ v₂) = B v₁ v₂ :=
      bilinReflectEquiv_preserves B hBsymm (z + y) h_add
    have hρ₁_fixes_W' : ∀ u' : U', ρ₁ (φ' u' : V) = (φ' u' : V) := by
      intro u'
      rw [bilinReflectEquiv_apply]
      exact bilinReflect_of_ortho B (z + y) h_add (φ' u' : V) (hortho_zy u').2
    let ρ₂ := bilinReflectEquiv B y hy_noniso
    have hρ₂_maps : ρ₂ (-y) = y := by
      rw [bilinReflectEquiv_apply]; exact bilinReflect_neg_self B y hy_noniso
    have hρ₂_preserves : ∀ v₁ v₂, B (ρ₂ v₁) (ρ₂ v₂) = B v₁ v₂ :=
      bilinReflectEquiv_preserves B hBsymm y hy_noniso
    have hρ₂_fixes_W' : ∀ u' : U', ρ₂ (φ' u' : V) = (φ' u' : V) := by
      intro u'
      rw [bilinReflectEquiv_apply]
      apply bilinReflect_of_ortho
      have hφ'_in_W' : (φ' u' : V) ∈ W' := (φ' u').2
      have hyperp_mem : (φ' u' : V) ∈ yperp := (Submodule.mem_inf.mp hφ'_in_W').2
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hyperp_mem
      have := hyperp_mem y (Submodule.mem_span_singleton_self y)
      unfold LinearMap.BilinForm.IsOrtho at this
      rw [hBsymm] at this; exact this

    let Φ := Ψ.trans (ρ₁.trans ρ₂)
    refine ⟨Φ, ?_, ?_⟩
    ·
      intro v₁ v₂
      simp only [Φ, LinearEquiv.trans_apply]
      rw [hρ₂_preserves, hρ₁_preserves, hΨ_isom]
    ·
      apply hext_from_decomp Φ
      · intro v₁ v₂; simp only [Φ, LinearEquiv.trans_apply]
        rw [hρ₂_preserves, hρ₁_preserves, hΨ_isom]
      · show ρ₂ (ρ₁ (Ψ x)) = y; rw [hρ₁_maps, hρ₂_maps]
      · intro u'
        show ρ₂ (ρ₁ (Ψ (u' : V))) = (φ (Submodule.inclusion inf_le_left u') : V)
        rw [hΨ_ext u']
        have hcoe : (φ' u' : V) = (φ (Submodule.inclusion inf_le_left u') : V) := by
          simp [φ', LinearEquiv.ofBijective_apply, φ'_lm]
        rw [← hcoe, hρ₁_fixes_W' u', hρ₂_fixes_W' u']

/-- Inductive step in Witt's extension theorem when `U` contains a nonzero
isotropic vector `u`: reduces to the non-isotropic step (or handles the case where
`U` is totally isotropic) to extend `φ : U ≃ W` to an isometry of all of `V`. -/
theorem wittExtension_isotropic_step
    [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V)
    (hBsymm : ∀ x y : V, B x y = B y x)
    (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
    (U W : Submodule k V) (φ : U ≃ₗ[k] W)
    (hφ : IsSubspaceIsometry B U W φ)
    {u : V} (huU : u ∈ U) (hu_ne : u ≠ 0) (hu_iso : B u u = 0)
    (ih : ∀ (U' W' : Submodule k V) (φ' : U' ≃ₗ[k] W'),
      IsSubspaceIsometry B U' W' φ' →
      Module.finrank k U' < Module.finrank k U →
      ∃ Φ : V ≃ₗ[k] V,
        (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧
        (∀ u : U', Φ (u : V) = (φ' u : V))) :
    ∃ Φ : V ≃ₗ[k] V,
      (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧
      (∀ u : U, Φ (u : V) = (φ u : V)) := by


  by_cases h_exists_noniso : ∃ x ∈ U, B x x ≠ 0
  ·
    obtain ⟨x, hxU, hx_noniso⟩ := h_exists_noniso
    exact wittExtension_noniso_step B hBsymm hnd U W φ hφ hxU hx_noniso ih
  ·
    push_neg at h_exists_noniso


    set y : V := (φ ⟨u, huU⟩ : V) with hy_def
    have hByy : B y y = 0 := by
      have := hφ ⟨u, huU⟩ ⟨u, huU⟩; rw [this]; exact hu_iso
    have hy_ne : y ≠ 0 := by
      intro hy_eq
      have hφ_zero : (φ ⟨u, huU⟩ : V) = 0 := hy_eq
      have : φ ⟨u, huU⟩ = 0 := Subtype.ext hφ_zero
      have : (⟨u, huU⟩ : U) = 0 := φ.injective (this.trans (map_zero φ.toLinearMap).symm)
      exact hu_ne (congr_arg Subtype.val this)

    have hU_tot_iso : ∀ v ∈ U, ∀ w ∈ U, B v w = 0 := by
      intro v hv w hw
      have hvw : v + w ∈ U := U.add_mem hv hw
      have h1 := h_exists_noniso (v + w) hvw
      have h2 := h_exists_noniso v hv
      have h3 := h_exists_noniso w hw
      have hexpand : B (v + w) (v + w) = B v v + 2 * B v w + B w w := by
        simp [map_add, LinearMap.add_apply, hBsymm w v]; ring
      rw [h1, h2, h3] at hexpand; simp at hexpand

      exact hexpand.resolve_left (NeZero.ne 2)


    have hu_not_ortho_all : ∃ w₀ : V, B u w₀ ≠ 0 := by
      by_contra hall; push_neg at hall
      have : u ∈ LinearMap.BilinForm.orthogonal B ⊤ := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro v _; unfold LinearMap.BilinForm.IsOrtho; rw [hBsymm]; exact hall v
      rw [hnd] at this
      exact hu_ne ((Submodule.mem_bot k).mp this)
    obtain ⟨w₀, hw₀⟩ := hu_not_ortho_all

    set w₀perp := LinearMap.BilinForm.orthogonal B (k ∙ w₀)
    set U₁ := U ⊓ w₀perp with hU₁_def

    have hu_not_U₁ : u ∉ U₁ := by
      intro h_mem
      have h_mem_w₀perp : u ∈ w₀perp := (Submodule.mem_inf.mp h_mem).2
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at h_mem_w₀perp
      have := h_mem_w₀perp w₀ (Submodule.mem_span_singleton_self w₀)
      unfold LinearMap.BilinForm.IsOrtho at this

      exact hw₀ (by rw [hBsymm]; exact this)


    let φ_U₁_to_V : U₁ →ₗ[k] V :=
      W.subtype.comp (φ.toLinearMap.comp (Submodule.inclusion inf_le_left))
    set W₁ := Submodule.map φ_U₁_to_V ⊤ with hW₁_def

    have hW₁_le_W : W₁ ≤ W := by
      intro v hv; rw [Submodule.mem_map] at hv
      obtain ⟨u₁, _, rfl⟩ := hv
      exact (φ (Submodule.inclusion inf_le_left u₁)).2


    have hφ₁_inj : Function.Injective φ_U₁_to_V := by
      intro a b hab
      simp only [φ_U₁_to_V, LinearMap.coe_comp, Function.comp_apply,
                  Submodule.subtype_apply] at hab
      have := φ.injective (Subtype.ext hab)
      exact Submodule.inclusion_injective inf_le_left this

    have hφ₁_surj_W₁ : ∀ w ∈ W₁, ∃ u₁ : U₁, φ_U₁_to_V u₁ = w := by
      intro w hw; rw [Submodule.mem_map] at hw
      obtain ⟨u₁, _, rfl⟩ := hw; exact ⟨u₁, rfl⟩

    let φ₁_lm : U₁ →ₗ[k] W₁ :=
      { toFun := fun u₁ => ⟨φ_U₁_to_V u₁, Submodule.mem_map.mpr ⟨u₁, Submodule.mem_top, rfl⟩⟩
        map_add' := by intro a b; ext; simp [φ_U₁_to_V, map_add]
        map_smul' := by intro c a; ext; simp [φ_U₁_to_V, map_smul] }
    have hφ₁_lm_inj : Function.Injective φ₁_lm := by
      intro a b hab
      have : (φ₁_lm a : V) = (φ₁_lm b : V) := by rw [hab]
      simp only [φ₁_lm, LinearMap.coe_mk, AddHom.coe_mk] at this
      exact hφ₁_inj this
    haveI : FiniteDimensional k U₁ := inferInstance
    haveI : FiniteDimensional k W₁ := inferInstance

    have hrank_U₁_W₁ : Module.finrank k U₁ = Module.finrank k W₁ := by
      have hsurj : Function.Surjective φ₁_lm := by
        intro ⟨w, hw⟩
        rw [Submodule.mem_map] at hw
        obtain ⟨u₁, _, rfl⟩ := hw
        exact ⟨u₁, by ext; simp [φ₁_lm, φ_U₁_to_V]⟩
      exact (LinearEquiv.ofBijective φ₁_lm ⟨hφ₁_lm_inj, hsurj⟩).finrank_eq
    have hφ₁_surj : Function.Surjective φ₁_lm := by
      rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank_U₁_W₁]
    let φ₁ : U₁ ≃ₗ[k] W₁ := LinearEquiv.ofBijective φ₁_lm ⟨hφ₁_lm_inj, hφ₁_surj⟩


    have hφ₁_isom : IsSubspaceIsometry B U₁ W₁ φ₁ := by
      intro u₁ u₂
      show B ((φ₁ u₁ : V)) ((φ₁ u₂ : V)) = B (u₁ : V) (u₂ : V)
      have hcoe : ∀ u' : U₁, (φ₁ u' : V) = (φ (Submodule.inclusion inf_le_left u') : V) := by
        intro u'; simp [φ₁, LinearEquiv.ofBijective_apply, φ₁_lm, φ_U₁_to_V]
      rw [hcoe, hcoe]; exact hφ _ _


    have hU₁_lt : Module.finrank k U₁ < Module.finrank k U := by

      have hU₁_le_U : U₁ ≤ U := inf_le_left
      have hU₁_ne_U : U₁ ≠ U := by
        intro h_eq; rw [← h_eq] at huU
        exact hu_not_U₁ huU
      exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hU₁_le_U hU₁_ne_U)


    obtain ⟨Ψ, hΨ_isom, hΨ_ext⟩ := ih U₁ W₁ φ₁ hφ₁_isom hU₁_lt


    set z : V := Ψ u
    have hBzz : B z z = 0 := by
      show B (Ψ u) (Ψ u) = 0; rw [hΨ_isom u u]; exact hu_iso

    have hΨ_on_U₁ : ∀ u₁ : U₁, Ψ (u₁ : V) = (φ (Submodule.inclusion inf_le_left u₁) : V) := by
      intro u₁
      have h1 := hΨ_ext u₁
      have h2 : (φ₁ u₁ : V) = (φ (Submodule.inclusion inf_le_left u₁) : V) := by
        simp [φ₁, LinearEquiv.ofBijective_apply, φ₁_lm, φ_U₁_to_V]
      rw [h1]; exact h2

    have hortho : ∀ u₁ : U₁, B (Ψ (u₁ : V)) (z - y) = 0 := by
      intro u₁
      have hΨu₁ : Ψ (u₁ : V) = (φ (Submodule.inclusion inf_le_left u₁) : V) := hΨ_on_U₁ u₁

      have hBΨu₁z : B (Ψ (u₁ : V)) z = 0 := by
        show B (Ψ (u₁ : V)) (Ψ u) = 0
        rw [hΨ_isom]
        exact hU_tot_iso (u₁ : V) ((Submodule.mem_inf.mp u₁.2).1) u huU

      have hBΨu₁y : B (Ψ (u₁ : V)) y = 0 := by
        rw [hΨu₁]
        have := hφ (Submodule.inclusion inf_le_left u₁) ⟨u, huU⟩
        simp at this; rw [this]
        exact hU_tot_iso (u₁ : V) ((Submodule.mem_inf.mp u₁.2).1) u huU
      simp [map_sub, hBΨu₁z, hBΨu₁y]

    have hortho_add : ∀ u₁ : U₁, B (Ψ (u₁ : V)) (z + y) = 0 := by
      intro u₁
      have hBΨu₁z : B (Ψ (u₁ : V)) z = 0 := by
        show B (Ψ (u₁ : V)) (Ψ u) = 0
        rw [hΨ_isom]
        exact hU_tot_iso (u₁ : V) ((Submodule.mem_inf.mp u₁.2).1) u huU
      have hBΨu₁y : B (Ψ (u₁ : V)) y = 0 := by
        rw [hΨ_on_U₁ u₁]
        have := hφ (Submodule.inclusion inf_le_left u₁) ⟨u, huU⟩
        simp at this; rw [this]
        exact hU_tot_iso (u₁ : V) ((Submodule.mem_inf.mp u₁.2).1) u huU
      simp [map_add, hBΨu₁z, hBΨu₁y]


    have hku_le_U : (k ∙ u) ≤ U := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huU)

    have hku_inf_U₁ : (k ∙ u) ⊓ U₁ = ⊥ := by
      rw [eq_bot_iff]; intro v hv
      rw [Submodule.mem_inf] at hv
      have hv_ku := hv.1
      have hv_U₁ := hv.2
      rw [Submodule.mem_span_singleton] at hv_ku
      obtain ⟨c, rfl⟩ := hv_ku
      by_contra hne
      have hc_ne : c ≠ 0 := by intro hc; exact hne (by rw [hc]; simp)
      have hv_w₀perp : c • u ∈ w₀perp := (Submodule.mem_inf.mp hv_U₁).2
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv_w₀perp
      have := hv_w₀perp w₀ (Submodule.mem_span_singleton_self w₀)
      unfold LinearMap.BilinForm.IsOrtho at this

      simp [map_smul, smul_eq_mul] at this
      rw [hBsymm] at this
      rcases this with h | h
      · exact hc_ne h
      · exact hw₀ h

    have hU_eq : (k ∙ u) ⊔ U₁ = U := by
      apply le_antisymm
      · exact sup_le hku_le_U inf_le_left
      · intro v hv


        set c := B v w₀ / B u w₀ with hc_def
        have hv_minus : v - c • u ∈ U₁ := by
          refine Submodule.mem_inf.mpr ⟨U.sub_mem hv (U.smul_mem c huU), ?_⟩
          rw [LinearMap.BilinForm.mem_orthogonal_iff]
          intro n hn; rw [Submodule.mem_span_singleton] at hn
          obtain ⟨a, rfl⟩ := hn
          unfold LinearMap.BilinForm.IsOrtho
          simp [map_smul, map_sub, LinearMap.smul_apply, smul_eq_mul]
          rw [hBsymm w₀ v, hBsymm w₀ u, hc_def]
          field_simp; ring
        rw [Submodule.mem_sup]
        refine ⟨c • u, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩, v - c • u, hv_minus, ?_⟩
        simp

    have hext_from_decomp :
      ∀ (Φ_val : V ≃ₗ[k] V),
      (∀ v₁ v₂, B (Φ_val v₁) (Φ_val v₂) = B v₁ v₂) →
      Φ_val u = y →
      (∀ u₁ : U₁, Φ_val (u₁ : V) = (φ (Submodule.inclusion inf_le_left u₁) : V)) →
      (∀ u_elem : U, Φ_val (u_elem : V) = (φ u_elem : V)) := by
        intro Φ_val _ hΦu hΦ_on_U₁ u_elem
        have hu_mem : (u_elem : V) ∈ U := u_elem.2
        have hu_in_sum : (u_elem : V) ∈ (k ∙ u) ⊔ U₁ := by rw [hU_eq]; exact hu_mem
        rw [Submodule.mem_sup] at hu_in_sum
        obtain ⟨su, hsu, p, hp, hup⟩ := hu_in_sum
        rw [Submodule.mem_span_singleton] at hsu
        obtain ⟨a_coeff, rfl⟩ := hsu
        have hp_U : p ∈ U := (Submodule.mem_inf.mp hp).1
        have hu_decomp : (u_elem : V) = a_coeff • u + p := hup.symm
        rw [hu_decomp, map_add, map_smul, hΦu, hΦ_on_U₁ ⟨p, hp⟩]
        symm
        have hu_eq : u_elem = a_coeff • ⟨u, huU⟩ + ⟨p, hp_U⟩ := by
          ext; simp [hu_decomp]
        rw [hu_eq, map_add, map_smul, Submodule.coe_add, Submodule.coe_smul]
        congr 1


    by_cases hzy_ne : z = y
    ·
      refine ⟨Ψ, hΨ_isom, ?_⟩
      apply hext_from_decomp Ψ hΨ_isom (show z = y from hzy_ne) (fun u₁ => hΨ_on_U₁ u₁)
    ·
      by_cases h_sub : B (z - y) (z - y) ≠ 0
      ·

        have hBzz_eq : B z z = B y y := by rw [hBzz, hByy]
        let ρ := bilinReflectEquiv B (z - y) h_sub
        have hρ_maps : ρ z = y := by
          rw [bilinReflectEquiv_apply]
          exact bilinReflect_maps B hBsymm z y h_sub hBzz_eq
        have hρ_preserves : ∀ v₁ v₂, B (ρ v₁) (ρ v₂) = B v₁ v₂ :=
          bilinReflectEquiv_preserves B hBsymm (z - y) h_sub

        have hρ_fixes : ∀ u₁ : U₁, ρ (Ψ (u₁ : V)) = (Ψ (u₁ : V)) := by
          intro u₁
          rw [bilinReflectEquiv_apply]
          exact bilinReflect_of_ortho B (z - y) h_sub (Ψ (u₁ : V)) (hortho u₁)

        let Φ := Ψ.trans ρ
        refine ⟨Φ, ?_, ?_⟩
        · intro v₁ v₂; simp only [Φ, LinearEquiv.trans_apply]
          rw [hρ_preserves, hΨ_isom]
        · apply hext_from_decomp Φ
          · intro v₁ v₂; simp only [Φ, LinearEquiv.trans_apply]
            rw [hρ_preserves, hΨ_isom]
          · show ρ (Ψ u) = y; exact hρ_maps
          · intro u₁
            show ρ (Ψ (u₁ : V)) = (φ (Submodule.inclusion inf_le_left u₁) : V)
            rw [hρ_fixes u₁, hΨ_on_U₁ u₁]
      ·
        push_neg at h_sub


        have hzy_ne_zero : z - y ≠ 0 := sub_ne_zero.mpr hzy_ne
        have ⟨v₀, hv₀⟩ : ∃ v₀ : V, B (z - y) v₀ ≠ 0 := by
          by_contra hall; push_neg at hall
          have : z - y ∈ LinearMap.BilinForm.orthogonal B ⊤ := by
            rw [LinearMap.BilinForm.mem_orthogonal_iff]
            intro v _; unfold LinearMap.BilinForm.IsOrtho; rw [hBsymm]; exact hall v
          rw [hnd] at this
          exact hzy_ne_zero ((Submodule.mem_bot k).mp this)

        have hBzy : B z y = 0 := by
          have h_expand : B (z - y) (z - y) = -2 * B z y := by
            simp [map_sub, LinearMap.sub_apply, hBsymm y z]; rw [hBzz, hByy]; ring
          rw [h_sub] at h_expand

          have h_neg2 : (-2 : k) * B z y = 0 := h_expand.symm
          exact (mul_eq_zero.mp h_neg2).resolve_left (by norm_num [NeZero.ne])

        have hBz_ne_By : B z v₀ ≠ B y v₀ := by
          intro heq
          apply hv₀
          simp [map_sub, LinearMap.sub_apply, heq]


        have hBnd : B.Nondegenerate := by
          constructor
          · intro x hx
            have : x ∈ LinearMap.BilinForm.orthogonal B ⊤ := by
              rw [LinearMap.BilinForm.mem_orthogonal_iff]
              intro v _; unfold LinearMap.BilinForm.IsOrtho; rw [hBsymm]; exact hx v
            rw [hnd] at this; exact (Submodule.mem_bot k).mp this
          · intro y hy
            have : y ∈ LinearMap.BilinForm.orthogonal B ⊤ := by
              rw [LinearMap.BilinForm.mem_orthogonal_iff]
              intro v _; unfold LinearMap.BilinForm.IsOrtho; exact hy v
            rw [hnd] at this; exact (Submodule.mem_bot k).mp this
        have hBrefl : B.IsRefl := by intro x y hxy; rw [hBsymm]; exact hxy


        have hz_not_W₁ : z ∉ W₁ := by
          intro hz_mem
          rw [Submodule.mem_map] at hz_mem
          obtain ⟨u₁, _, hu₁_eq⟩ := hz_mem


          have hΨu₁_eq : φ_U₁_to_V u₁ = Ψ (u₁ : V) := by
            simp only [φ_U₁_to_V, LinearMap.coe_comp, Function.comp_apply,
                        Submodule.subtype_apply]
            exact (hΨ_on_U₁ u₁).symm
          have : Ψ u = Ψ (u₁ : V) := by
            change φ_U₁_to_V u₁ = Ψ u at hu₁_eq
            rw [hΨu₁_eq] at hu₁_eq; exact hu₁_eq.symm

          have : u = (u₁ : V) := Ψ.injective this
          have : u ∈ U₁ := this ▸ u₁.2
          exact hu_not_U₁ this
        have hy_not_W₁ : y ∉ W₁ := by
          intro hy_mem
          rw [Submodule.mem_map] at hy_mem
          obtain ⟨u₁, _, hu₁_eq⟩ := hy_mem


          have heq : (φ (Submodule.inclusion inf_le_left u₁) : V) = y := by
            change φ_U₁_to_V u₁ = y at hu₁_eq
            simp only [φ_U₁_to_V, LinearMap.coe_comp, Function.comp_apply,
                        Submodule.subtype_apply] at hu₁_eq
            exact hu₁_eq
          have : (Submodule.inclusion inf_le_left u₁ : U) = (⟨u, huU⟩ : U) := by
            apply φ.injective; ext; simp [heq, hy_def]
          have : (u₁ : V) = u := congr_arg Subtype.val this
          have : u ∈ U₁ := this ▸ u₁.2
          exact hu_not_U₁ this


        have hW₁_perp_perp : B.orthogonal (B.orthogonal W₁) = W₁ :=
          LinearMap.BilinForm.orthogonal_orthogonal hBnd hBrefl W₁

        have ⟨b₁, hb₁_mem, hb₁z⟩ : ∃ b ∈ B.orthogonal W₁, B z b ≠ 0 := by
          by_contra hall; push_neg at hall
          have : z ∈ B.orthogonal (B.orthogonal W₁) := by
            rw [LinearMap.BilinForm.mem_orthogonal_iff]
            intro v hv; unfold LinearMap.BilinForm.IsOrtho
            rw [hBsymm]; exact hall v hv
          rw [hW₁_perp_perp] at this
          exact hz_not_W₁ this
        have ⟨b₂, hb₂_mem, hb₂y⟩ : ∃ b ∈ B.orthogonal W₁, B y b ≠ 0 := by
          by_contra hall; push_neg at hall
          have : y ∈ B.orthogonal (B.orthogonal W₁) := by
            rw [LinearMap.BilinForm.mem_orthogonal_iff]
            intro v hv; unfold LinearMap.BilinForm.IsOrtho
            rw [hBsymm]; exact hall v hv
          rw [hW₁_perp_perp] at this
          exact hy_not_W₁ this


        have ⟨b, hb_mem, hbz, hby⟩ :
            ∃ b ∈ B.orthogonal W₁, B z b ≠ 0 ∧ B y b ≠ 0 := by
          by_cases hyb₁ : B y b₁ ≠ 0
          · exact ⟨b₁, hb₁_mem, hb₁z, hyb₁⟩
          · push_neg at hyb₁

            by_cases hzb₂ : B z b₂ = 0
            ·
              refine ⟨b₁ + b₂, (B.orthogonal W₁).add_mem hb₁_mem hb₂_mem, ?_, ?_⟩
              · simp [map_add, hzb₂]; exact hb₁z
              · simp [map_add, hyb₁]; exact hb₂y
            ·
              exact ⟨b₂, hb₂_mem, hzb₂, hb₂y⟩


        have hz_orth_W₁ : z ∈ B.orthogonal W₁ := by
          rw [LinearMap.BilinForm.mem_orthogonal_iff]
          intro w hw; unfold LinearMap.BilinForm.IsOrtho
          rw [Submodule.mem_map] at hw
          obtain ⟨u₁, _, rfl⟩ := hw

          rw [hBsymm]
          have : φ_U₁_to_V u₁ = Ψ (u₁ : V) := by
            simp only [φ_U₁_to_V, LinearMap.coe_comp, Function.comp_apply,
                        Submodule.subtype_apply]
            exact (hΨ_on_U₁ u₁).symm
          rw [this]

          rw [hΨ_isom]
          exact hU_tot_iso u huU (u₁ : V) ((Submodule.mem_inf.mp u₁.2).1)


        have hy_orth_W₁ : y ∈ B.orthogonal W₁ := by
          rw [LinearMap.BilinForm.mem_orthogonal_iff]
          intro w hw; unfold LinearMap.BilinForm.IsOrtho
          rw [Submodule.mem_map] at hw
          obtain ⟨u₁, _, rfl⟩ := hw
          rw [hBsymm]


          change B y (φ_U₁_to_V u₁) = 0
          show B (↑(φ ⟨u, huU⟩)) (φ_U₁_to_V u₁) = 0
          simp only [φ_U₁_to_V, LinearMap.coe_comp, Function.comp_apply,
                      Submodule.subtype_apply]
          exact (hφ ⟨u, huU⟩ (Submodule.inclusion inf_le_left u₁)).trans
            (hU_tot_iso u huU (u₁ : V) ((Submodule.mem_inf.mp u₁.2).1))


        have ⟨b', hb'_mem, hb'z, hb'y, hb'_noniso⟩ :
            ∃ b' ∈ B.orthogonal W₁, B z b' ≠ 0 ∧ B y b' ≠ 0 ∧ B b' b' ≠ 0 := by
          by_cases hbb : B b b ≠ 0
          · exact ⟨b, hb_mem, hbz, hby, hbb⟩
          · push_neg at hbb

            refine ⟨b + z, (B.orthogonal W₁).add_mem hb_mem hz_orth_W₁, ?_, ?_, ?_⟩
            ·
              simp [map_add, hBzz]; exact hbz
            ·
              simp [map_add, hBzy, hBsymm y z]; exact hby
            ·

              have hexpand : B (b + z) (b + z) = B b b + 2 * B b z + B z z := by
                simp [map_add, LinearMap.add_apply, hBsymm z b]; ring
              rw [hexpand, hbb, hBzz]; simp
              exact ⟨NeZero.ne 2, fun h => hbz (by rw [hBsymm]; exact h)⟩


        let ρ₁ := bilinReflectEquiv B b' hb'_noniso
        set w := ρ₁ z with hw_def
        have hρ₁_preserves : ∀ v₁ v₂, B (ρ₁ v₁) (ρ₁ v₂) = B v₁ v₂ :=
          bilinReflectEquiv_preserves B hBsymm b' hb'_noniso
        have hBww : B w w = 0 := by
          rw [hw_def]; rw [hρ₁_preserves]; exact hBzz


        have hBwy : B w y ≠ 0 := by
          rw [hw_def, bilinReflectEquiv_apply]
          unfold bilinReflect
          simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          rw [hBzy]
          simp

          exact ⟨⟨⟨NeZero.ne 2, hb'z⟩, hb'_noniso⟩,
                 fun h => hb'y (by rw [hBsymm]; exact h)⟩

        have hw_sub_y_noniso : B (w - y) (w - y) ≠ 0 := by
          have hexpand : B (w - y) (w - y) = -(2 * B w y) := by
            simp [map_sub, LinearMap.sub_apply, hBsymm y w, hBww, hByy]; ring
          rw [hexpand]
          simp [NeZero.ne]
          intro h
          exact hBwy h

        have hBww_eq : B w w = B y y := by rw [hBww, hByy]

        let ρ₂ := bilinReflectEquiv B (w - y) hw_sub_y_noniso
        have hρ₂_maps : ρ₂ w = y := by
          rw [bilinReflectEquiv_apply]
          exact bilinReflect_maps B hBsymm w y hw_sub_y_noniso hBww_eq
        have hρ₂_preserves : ∀ v₁ v₂, B (ρ₂ v₁) (ρ₂ v₂) = B v₁ v₂ :=
          bilinReflectEquiv_preserves B hBsymm (w - y) hw_sub_y_noniso


        have hρ₁_fixes : ∀ u₁ : U₁, ρ₁ (Ψ (u₁ : V)) = Ψ (u₁ : V) := by
          intro u₁
          rw [bilinReflectEquiv_apply]
          apply bilinReflect_of_ortho


          have hΨu₁_in_W₁ : Ψ (u₁ : V) ∈ W₁ := by
            rw [Submodule.mem_map]
            refine ⟨u₁, Submodule.mem_top, ?_⟩
            simp only [φ_U₁_to_V, LinearMap.coe_comp, Function.comp_apply,
                        Submodule.subtype_apply]
            exact (hΨ_on_U₁ u₁).symm
          rw [LinearMap.BilinForm.mem_orthogonal_iff] at hb'_mem
          have := hb'_mem (Ψ (u₁ : V)) hΨu₁_in_W₁
          unfold LinearMap.BilinForm.IsOrtho at this
          exact this


        have hρ₂_fixes : ∀ u₁ : U₁, ρ₂ (Ψ (u₁ : V)) = Ψ (u₁ : V) := by
          intro u₁
          rw [bilinReflectEquiv_apply]
          apply bilinReflect_of_ortho

          have hBΨu₁w : B (Ψ (u₁ : V)) w = 0 := by
            rw [hw_def]

            rw [← hρ₁_fixes u₁, hρ₁_preserves]

            show B (Ψ (u₁ : V)) (Ψ u) = 0
            rw [hΨ_isom]
            exact hU_tot_iso (u₁ : V) ((Submodule.mem_inf.mp u₁.2).1) u huU
          have hBΨu₁y : B (Ψ (u₁ : V)) y = 0 := by
            rw [hΨ_on_U₁ u₁]
            have := hφ (Submodule.inclusion inf_le_left u₁) ⟨u, huU⟩
            simp at this; rw [this]
            exact hU_tot_iso (u₁ : V) ((Submodule.mem_inf.mp u₁.2).1) u huU
          simp [map_sub, hBΨu₁w, hBΨu₁y]

        let Φ := (Ψ.trans ρ₁).trans ρ₂
        refine ⟨Φ, ?_, ?_⟩
        ·
          intro v₁ v₂
          simp only [Φ, LinearEquiv.trans_apply]
          rw [hρ₂_preserves, hρ₁_preserves, hΨ_isom]
        ·
          apply hext_from_decomp Φ
          · intro v₁ v₂; simp only [Φ, LinearEquiv.trans_apply]
            rw [hρ₂_preserves, hρ₁_preserves, hΨ_isom]
          ·
            show ρ₂ (ρ₁ (Ψ u)) = y

            change ρ₂ w = y
            exact hρ₂_maps
          ·
            intro u₁
            show ρ₂ (ρ₁ (Ψ (u₁ : V))) = (φ (Submodule.inclusion inf_le_left u₁) : V)
            rw [hρ₁_fixes u₁, hρ₂_fixes u₁, hΨ_on_U₁ u₁]

/-- Witt's Extension Theorem for symmetric nondegenerate bilinear forms in
characteristic not two: any isometry between subspaces extends to an isometry of
the whole space. Proved by strong induction on `Module.finrank k U`, dispatching
to `wittExtension_noniso_step` or `wittExtension_isotropic_step` as appropriate. -/
theorem wittExtensionProp_of_symmetric

    [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V)
    (hBsymm : ∀ x y : V, B x y = B y x)
    (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥) :
    WittExtensionProp B := by
  intro _hnd' U W φ hφ

  suffices h : ∀ (n : ℕ) (U W : Submodule k V) (φ : U ≃ₗ[k] W),
      IsSubspaceIsometry B U W φ → Module.finrank k U = n →
      ∃ Φ : V ≃ₗ[k] V,
        (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧
        (∀ u : U, Φ (u : V) = (φ u : V)) by
    exact h _ U W φ hφ rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih_n =>
    intro U W φ hφ hn
    by_cases hU : U = ⊥
    ·
      subst hU
      exact wittExtension_bot B hnd W φ hφ
    ·
      obtain ⟨u_val, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      by_cases h_noniso : B u_val u_val ≠ 0
      · exact wittExtension_noniso_step B hBsymm hnd U W φ hφ hu_mem h_noniso
          (fun U' W' φ' hφ' hlt => ih_n _ (hn ▸ hlt) U' W' φ' hφ' rfl)
      · push_neg at h_noniso
        exact wittExtension_isotropic_step B hBsymm hnd U W φ hφ hu_mem hu_ne h_noniso
          (fun U' W' φ' hφ' hlt => ih_n _ (hn ▸ hlt) U' W' φ' hφ' rfl)

/-- Witt's Cancellation Theorem for symmetric nondegenerate bilinear forms,
obtained as a corollary of the extension theorem
`wittExtensionProp_of_symmetric`. -/
theorem wittCancellationProp_of_symmetric
    [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V)
    (hBsymm : ∀ x y : V, B x y = B y x)
    (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥) :
    WittCancellationProp B :=
  WittCancellation B (wittExtensionProp_of_symmetric B hBsymm hnd)

end Garrett
