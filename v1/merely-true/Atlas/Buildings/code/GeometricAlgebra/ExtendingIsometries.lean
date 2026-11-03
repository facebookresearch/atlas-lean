/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.RelClasses

namespace Garrett

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- A submodule `U` is totally isotropic for `B` when `B` vanishes on all pairs of
elements of `U`. -/
def IsTotallyIsotropic (B : LinearMap.BilinForm k V) (U : Submodule k V) : Prop :=
  ∀ u₁ ∈ U, ∀ u₂ ∈ U, B u₁ u₂ = 0

/-- A linear isomorphism `φ : U ≃ₗ W` between two submodules is a subspace
isometry for `B` when it preserves the values of `B`. -/
def IsSubspaceIsometry (B : LinearMap.BilinForm k V) (U W : Submodule k V)
    (φ : U ≃ₗ[k] W) : Prop :=
  ∀ u₁ u₂ : U, B (φ u₁ : V) (φ u₂ : V) = B (u₁ : V) (u₂ : V)


/-- Witt extension property for `B`: when `B` is nondegenerate, every subspace
isometry between two submodules extends to a global isometry of `V`. -/
def WittExtensionProp (B : LinearMap.BilinForm k V) : Prop :=
  LinearMap.BilinForm.orthogonal B ⊤ = ⊥ →
  ∀ (U W : Submodule k V) (φ : U ≃ₗ[k] W),
    IsSubspaceIsometry B U W φ →
    ∃ Φ : V ≃ₗ[k] V,
      (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧
      (∀ u : U, Φ (u : V) = (φ u : V))

/-- Witt cancellation property for `B`: when `B` is nondegenerate, every
isometry between two submodules induces an isometry between their orthogonal
complements. -/
def WittCancellationProp (B : LinearMap.BilinForm k V) : Prop :=
  LinearMap.BilinForm.orthogonal B ⊤ = ⊥ →
  ∀ (U₁ U₂ : Submodule k V) (φ : U₁ ≃ₗ[k] U₂),
    IsSubspaceIsometry B U₁ U₂ φ →
    ∃ ψ : (LinearMap.BilinForm.orthogonal B U₁) ≃ₗ[k]
           (LinearMap.BilinForm.orthogonal B U₂),
      IsSubspaceIsometry B
        (LinearMap.BilinForm.orthogonal B U₁)
        (LinearMap.BilinForm.orthogonal B U₂) ψ


/-- The underlying value of `LinearEquiv.ofEq p q h x` agrees with that of `x`
since both submodules are equal. -/
lemma LinearEquiv.ofEq_coe {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {p q : Submodule R M} (h : p = q) (x : p) :
    (LinearEquiv.ofEq p q h x : M) = (x : M) := by
  subst h; rfl

/-- For a reflexive bilinear form `B`, any pair `(u, v)` with `u ∈ U` and
`v` in the orthogonal complement of `U` satisfies `B u v = 0` and `B v u = 0`. -/
lemma orth_cross_zero (B : LinearMap.BilinForm k V)
    (hB_ref : ∀ x y : V, B x y = 0 → B y x = 0)
    (U : Submodule k V) (u : U) (v : LinearMap.BilinForm.orthogonal B U) :
    B (u : V) (v : V) = 0 ∧ B (v : V) (u : V) = 0 := by
  have hv := v.2
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
  have h1 := hv (u : V) u.2
  exact ⟨h1, hB_ref _ _ h1⟩

/-- For a reflexive form `B`, the bilinear values on sums `a + c` and `b + d`
(with `a, b ∈ U` and `c, d` in the orthogonal complement of `U`) split into
`B a b + B c d` because the cross terms vanish. -/
lemma bilinForm_decomp (B : LinearMap.BilinForm k V)
    (hB_ref : ∀ x y : V, B x y = 0 → B y x = 0)
    (U : Submodule k V) (a b : U)
    (c d : LinearMap.BilinForm.orthogonal B U) :
    B (↑a + ↑c) (↑b + ↑d) = B (↑a) (↑b) + B (↑c) (↑d) := by
  simp only [map_add, LinearMap.add_apply]
  have h_ad := (orth_cross_zero B hB_ref U a d).1
  have h_cb := (orth_cross_zero B hB_ref U b c).2
  rw [h_ad, h_cb]; ring


/-- Witt extension implies Witt cancellation: if every subspace isometry of `B`
extends globally, then any isometry between two submodules also induces an
isometry between their orthogonal complements. -/
theorem WittCancellation (B : LinearMap.BilinForm k V)
    (hWE : WittExtensionProp B) : WittCancellationProp B := by
  intro hnd U₁ U₂ φ hφ
  obtain ⟨Φ, hΦ_isom, hΦ_ext⟩ := hWE hnd U₁ U₂ φ hφ

  have hΦ_orth_map : Submodule.map Φ.toLinearMap (LinearMap.BilinForm.orthogonal B U₁) =
      LinearMap.BilinForm.orthogonal B U₂ := by
    ext w
    simp only [Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    ·
      rintro ⟨v, hv, rfl⟩
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
      intro n hn
      unfold LinearMap.BilinForm.IsOrtho

      obtain ⟨u, rfl⟩ : ∃ u : U₁, (φ u : V) = n := ⟨φ.symm ⟨n, hn⟩, by simp⟩

      rw [← hΦ_ext u, hΦ_isom]
      exact hv (u : V) u.2
    ·
      intro hw
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw
      refine ⟨Φ.symm w, ?_, by simp⟩
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      unfold LinearMap.BilinForm.IsOrtho
      have hΦn : Φ n ∈ U₂ := by rw [hΦ_ext ⟨n, hn⟩]; exact (φ ⟨n, hn⟩).2
      have := hw (Φ n) hΦn
      unfold LinearMap.BilinForm.IsOrtho at this
      calc B n (Φ.symm w) = B (Φ n) (Φ (Φ.symm w)) := by rw [hΦ_isom]
        _ = B (Φ n) w := by simp
        _ = 0 := this

  let ψ := (Φ.submoduleMap (LinearMap.BilinForm.orthogonal B U₁)).trans
    (LinearEquiv.ofEq _ _ hΦ_orth_map)
  refine ⟨ψ, ?_⟩

  intro x₁ x₂
  show B ((ψ x₁ : V)) ((ψ x₂ : V)) = B (x₁ : V) (x₂ : V)
  have h1 : ∀ x : LinearMap.BilinForm.orthogonal B U₁, (ψ x : V) = Φ (x : V) := by
    intro x
    simp only [ψ, LinearEquiv.trans_apply]
    rw [LinearEquiv.ofEq_coe, LinearEquiv.submoduleMap_apply]
  rw [h1, h1]
  exact hΦ_isom _ _


/-- Witt cancellation implies Witt extension, given that `B` is reflexive and
each subspace is complemented by its orthogonal complement: any subspace
isometry of `B` then extends to a global isometry. -/
theorem WittExtension (B : LinearMap.BilinForm k V)
    (hWC : WittCancellationProp B)
    (hB_ref : ∀ x y : V, B x y = 0 → B y x = 0)
    (hCompl : ∀ (S : Submodule k V),
      IsCompl S (LinearMap.BilinForm.orthogonal B S)) :
    WittExtensionProp B := by
  intro hnd U W φ hφ

  obtain ⟨ψ, hψ⟩ := hWC hnd U W φ hφ

  let decompU := Submodule.prodEquivOfIsCompl U (LinearMap.BilinForm.orthogonal B U) (hCompl U)
  let decompW := Submodule.prodEquivOfIsCompl W (LinearMap.BilinForm.orthogonal B W) (hCompl W)

  let Φ : V ≃ₗ[k] V := decompU.symm.trans ((φ.prodCongr ψ).trans decompW)
  use Φ
  constructor
  ·
    intro v₁ v₂

    set d₁ := decompU.symm v₁
    set d₂ := decompU.symm v₂
    have hv₁ : v₁ = ↑d₁.1 + ↑d₁.2 := by
      conv_lhs => rw [← LinearEquiv.apply_symm_apply decompU v₁]
      rw [Submodule.coe_prodEquivOfIsCompl']
    have hv₂ : v₂ = ↑d₂.1 + ↑d₂.2 := by
      conv_lhs => rw [← LinearEquiv.apply_symm_apply decompU v₂]
      rw [Submodule.coe_prodEquivOfIsCompl']

    have hΦv₁ : Φ v₁ = ↑(φ d₁.1) + ↑(ψ d₁.2) := by
      simp only [Φ, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, d₁]
      rw [Submodule.coe_prodEquivOfIsCompl']
    have hΦv₂ : Φ v₂ = ↑(φ d₂.1) + ↑(ψ d₂.2) := by
      simp only [Φ, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, d₂]
      rw [Submodule.coe_prodEquivOfIsCompl']

    rw [hΦv₁, hΦv₂, hv₁, hv₂]
    rw [bilinForm_decomp B hB_ref U d₁.1 d₂.1 d₁.2 d₂.2]
    rw [bilinForm_decomp B hB_ref W (φ d₁.1) (φ d₂.1) (ψ d₁.2) (ψ d₂.2)]
    rw [hφ, hψ]
  ·
    intro u
    show Φ (u : V) = (φ u : V)
    simp only [Φ, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]

    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]

    rw [Submodule.coe_prodEquivOfIsCompl']
    simp [add_zero]

end Garrett
