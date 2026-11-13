/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.BilinearForm.Basic

namespace Oriflamme

section ExtendAutomorphism

variable {k : Type*} [Field k]
  {U U' V : Type*} [AddCommGroup U] [AddCommGroup U'] [AddCommGroup V]
  [Module k U] [Module k U'] [Module k V]

/-- Given an isomorphism $e : U \oplus U' \cong V$ and automorphisms $\alpha$ of $U$, $\beta$ of $U'$,
the conjugated map $h = e \circ (\alpha \oplus \beta) \circ e^{-1}$ has determinant
$\det h = \det \alpha \cdot \det \beta$. -/
theorem extend_lagrangian_auto_det
    [Module.Free k U] [Module.Free k U'] [Module.Finite k U] [Module.Finite k U']
    (e : (U × U') ≃ₗ[k] V) (α : U ≃ₗ[k] U) (β : U' ≃ₗ[k] U') :
    let h : V →ₗ[k] V := e.toLinearMap ∘ₗ (α.toLinearMap.prodMap β.toLinearMap) ∘ₗ e.symm.toLinearMap
    LinearMap.det h = LinearMap.det α.toLinearMap * LinearMap.det β.toLinearMap := by
  intro h
  show LinearMap.det (e.toLinearMap ∘ₗ (α.toLinearMap.prodMap β.toLinearMap)
    ∘ₗ e.symm.toLinearMap) = _
  rw [LinearMap.det_conj]
  exact LinearMap.det_prodMap α.toLinearMap β.toLinearMap

/-- Specialization: if $\det \beta = (\det \alpha)^{-1}$, then the extended automorphism $h$
has determinant $1$, lying in the special isometry group. -/
theorem extend_lagrangian_auto_det_one
    [Module.Free k U] [Module.Free k U'] [Module.Finite k U] [Module.Finite k U']
    (e : (U × U') ≃ₗ[k] V) (α : U ≃ₗ[k] U) (β : U' ≃ₗ[k] U')
    (hβ : LinearMap.det β.toLinearMap = (LinearMap.det α.toLinearMap)⁻¹) :
    let h : V →ₗ[k] V := e.toLinearMap ∘ₗ (α.toLinearMap.prodMap β.toLinearMap) ∘ₗ e.symm.toLinearMap
    LinearMap.det h = 1 := by
  intro h
  rw [extend_lagrangian_auto_det e α β, hβ]
  exact mul_inv_cancel₀ (by rw [← LinearEquiv.coe_det]; exact Units.ne_zero _)

/-- The extended automorphism $h$ restricted to the Lagrangian subspace $e(U \times \{0\})$
acts as $\alpha$: $h(e(u, 0)) = e(\alpha u, 0)$. -/
theorem extend_lagrangian_auto_restricts
    (e : (U × U') ≃ₗ[k] V) (α : U ≃ₗ[k] U) (β : U' ≃ₗ[k] U') :
    let h : V →ₗ[k] V := e.toLinearMap ∘ₗ (α.toLinearMap.prodMap β.toLinearMap) ∘ₗ e.symm.toLinearMap
    ∀ u : U, h (e (u, 0)) = e (α u, 0) := by
  intro h u
  show (e.toLinearMap ∘ₗ (α.toLinearMap.prodMap β.toLinearMap) ∘ₗ e.symm.toLinearMap)
    (e (u, 0)) = e (α u, 0)
  simp only [LinearMap.comp_apply, LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply,
    LinearEquiv.coe_coe, map_zero]

/-- **Lagrangian extension is an isometry**: given that $e(U \times \{0\})$ and $e(\{0\} \times U')$
are isotropic Lagrangians and $\alpha, \beta$ are mutually adjoint, the extended map
$h = e \circ (\alpha \oplus \beta) \circ e^{-1}$ preserves the bilinear form $B$. -/
theorem extend_lagrangian_auto_isometry
    (e : (U × U') ≃ₗ[k] V) (α : U ≃ₗ[k] U) (β : U' ≃ₗ[k] U')
    (B : V →ₗ[k] V →ₗ[k] k)

    (hU_iso : ∀ u₁ u₂ : U, B (e (u₁, 0)) (e (u₂, 0)) = 0)

    (hU'_iso : ∀ u'₁ u'₂ : U', B (e (0, u'₁)) (e (0, u'₂)) = 0)


    (hadj : ∀ (u : U) (u' : U'), B (e (α u, 0)) (e (0, β u')) = B (e (u, 0)) (e (0, u')))

    (hadj' : ∀ (u' : U') (u : U),
      B (e (0, β u')) (e (α u, 0)) = B (e (0, u')) (e (u, 0))) :
    let h : V →ₗ[k] V := e.toLinearMap ∘ₗ (α.toLinearMap.prodMap β.toLinearMap) ∘ₗ e.symm.toLinearMap
    ∀ v w : V, B (h v) (h w) = B v w := by
  intro h v w

  suffices ∀ (p q : U × U'),
    B (e (α p.1, β p.2)) (e (α q.1, β q.2)) = B (e p) (e q) by
    have hv : h v = e (α (e.symm v).1, β (e.symm v).2) := by
      show (e.toLinearMap ∘ₗ (α.toLinearMap.prodMap β.toLinearMap) ∘ₗ e.symm.toLinearMap) v = _
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.prodMap_apply]
    have hw : h w = e (α (e.symm w).1, β (e.symm w).2) := by
      show (e.toLinearMap ∘ₗ (α.toLinearMap.prodMap β.toLinearMap) ∘ₗ e.symm.toLinearMap) w = _
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.prodMap_apply]
    rw [hv, hw, this, e.apply_symm_apply, e.apply_symm_apply]
  intro p q

  have hdec : ∀ (a : U) (b : U'), e (a, b) = e (a, 0) + e (0, b) := by
    intro a b
    have : (a, b) = (a, (0 : U')) + ((0 : U), b) := by ext <;> simp
    rw [this, map_add]

  rw [hdec (α p.1) (β p.2), hdec (α q.1) (β q.2)]
  rw [show p = (p.1, p.2) from Prod.mk.eta.symm, hdec p.1 p.2,
      show q = (q.1, q.2) from Prod.mk.eta.symm, hdec q.1 q.2]

  simp only [map_add, LinearMap.add_apply]

  rw [hU_iso (α p.1) (α q.1), hU_iso p.1 q.1,
      hU'_iso (β p.2) (β q.2), hU'_iso p.2 q.2,
      hadj p.1 q.2, hadj' p.2 q.1]

end ExtendAutomorphism

end Oriflamme
