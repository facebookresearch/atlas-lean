/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Atlas.Buildings.code.GeometricAlgebra.WittExtensionProof
import Atlas.Buildings.code.GeometricAlgebra.WittTheorem

namespace Garrett

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]

end Garrett

/-- Isometry extension lemma (Witt's theorem, extension form): every
subspace isometry $\varphi : U \to W$ of a non-degenerate symmetric bilinear
space $(V, B)$ extends to a global isometry $\Phi : V \to V$ with
$B(\Phi v_1, \Phi v_2) = B(v_1, v_2)$ and $\Phi|_U = \varphi$. -/
theorem isometry_extension_lemma
    {k : Type*} [Field k] [NeZero (2 : k)]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V)
    (hBsymm : ∀ x y : V, B x y = B y x)
    (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
    (U W : Submodule k V) (φ : U ≃ₗ[k] W)
    (hφ : Garrett.IsSubspaceIsometry B U W φ) :
    ∃ Φ : V ≃ₗ[k] V,
      (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧
      (∀ u : U, Φ (u : V) = (φ u : V)) :=
  Garrett.wittExtensionProp_of_symmetric B hBsymm hnd hnd U W φ hφ

/-- Witt cancellation: any subspace isometry $\varphi : U_1 \to U_2$ of a
non-degenerate symmetric bilinear space induces an isometry between the
orthogonal complements $U_1^{\perp}$ and $U_2^{\perp}$. -/
theorem witt_cancellation
    {k : Type*} [Field k] [NeZero (2 : k)]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V)
    (hBsymm : ∀ x y : V, B x y = B y x)
    (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
    (U₁ U₂ : Submodule k V) (φ : U₁ ≃ₗ[k] U₂)
    (hφ : Garrett.IsSubspaceIsometry B U₁ U₂ φ) :
    ∃ ψ : (LinearMap.BilinForm.orthogonal B U₁) ≃ₗ[k]
           (LinearMap.BilinForm.orthogonal B U₂),
      Garrett.IsSubspaceIsometry B
        (LinearMap.BilinForm.orthogonal B U₁)
        (LinearMap.BilinForm.orthogonal B U₂) ψ :=
  Garrett.wittCancellationProp_of_symmetric B hBsymm hnd hnd U₁ U₂ φ hφ

/-- Witt's theorem (Section 7.3): for non-degenerate symmetric bilinear
spaces, both the extension lemma and Witt cancellation hold simultaneously. -/
theorem witt_theorem_section_7_3
    {k : Type*} [Field k] [NeZero (2 : k)]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V)
    (hBsymm : ∀ x y : V, B x y = B y x)
    (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥) :

    (∀ (U W : Submodule k V) (φ : U ≃ₗ[k] W),
      Garrett.IsSubspaceIsometry B U W φ →
      ∃ Φ : V ≃ₗ[k] V,
        (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧
        (∀ u : U, Φ (u : V) = (φ u : V))) ∧

    (∀ (U₁ U₂ : Submodule k V) (φ : U₁ ≃ₗ[k] U₂),
      Garrett.IsSubspaceIsometry B U₁ U₂ φ →
      ∃ ψ : (LinearMap.BilinForm.orthogonal B U₁) ≃ₗ[k]
             (LinearMap.BilinForm.orthogonal B U₂),
        Garrett.IsSubspaceIsometry B
          (LinearMap.BilinForm.orthogonal B U₁)
          (LinearMap.BilinForm.orthogonal B U₂) ψ) :=
  ⟨fun U W φ hφ => isometry_extension_lemma B hBsymm hnd U W φ hφ,
   fun U₁ U₂ φ hφ => witt_cancellation B hBsymm hnd U₁ U₂ φ hφ⟩
