/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Maps

set_option maxHeartbeats 800000

noncomputable section

open TensorProduct

namespace FiberFunctorEnd

variable (k : Type*) [CommSemiring k]
variable (M N : Type*) [AddCommMonoid M] [AddCommMonoid N]
  [Module k M] [Module k N]

/-- Right-tensoring by `φ : End M` and left-tensoring by `ψ : End N` commute as
endomorphisms of `M ⊗ N`. -/
theorem rTensor_lTensor_commute (φ : Module.End k M) (ψ : Module.End k N) :
    Commute (Module.End.rTensorAlgHom k M N φ) (Module.End.lTensorAlgHom k N M ψ) := by
  show LinearMap.rTensor N φ * LinearMap.lTensor M ψ =
    LinearMap.lTensor M ψ * LinearMap.rTensor N φ
  show (LinearMap.rTensor N φ).comp (LinearMap.lTensor M ψ) =
    (LinearMap.lTensor M ψ).comp (LinearMap.rTensor N φ)
  ext m n; simp

/-- The canonical `k`-algebra homomorphism `End(M) ⊗ End(N) →ₐ End(M ⊗ N)` obtained by
combining right- and left-tensoring with the universal property of the algebra tensor
product. -/
def endTensorEndAlgHom :
    (Module.End k M) ⊗[k] (Module.End k N) →ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.lift
    (Module.End.rTensorAlgHom k M N)
    (Module.End.lTensorAlgHom k N M)
    (rTensor_lTensor_commute k M N)

/-- The algebra homomorphism `endTensorEndAlgHom` sends the elementary tensor
`φ ⊗ ψ` to the endomorphism `TensorProduct.map φ ψ` of `M ⊗ N`. -/
@[simp]
theorem endTensorEndAlgHom_tmul (φ : Module.End k M) (ψ : Module.End k N) :
    endTensorEndAlgHom k M N (φ ⊗ₜ ψ) = TensorProduct.map φ ψ := by
  simp only [endTensorEndAlgHom, Algebra.TensorProduct.lift_tmul]
  ext m n
  simp [Module.End.rTensorAlgHom, Module.End.lTensorAlgHom,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul]

variable [Module.Free k M] [Module.Finite k M]
  [Module.Free k N] [Module.Finite k N]

/-- For finite free `k`-modules `M` and `N`, the canonical algebra map upgrades to a
`k`-algebra isomorphism `End(M) ⊗ End(N) ≃ₐ End(M ⊗ N)`. -/
def endTensorEndAlgEquiv :
    (Module.End k M) ⊗[k] (Module.End k N) ≃ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (homTensorHomEquiv k M N M N)
    (fun φ₁ φ₂ ψ₁ ψ₂ => by
      simp only [homTensorHomEquiv_apply, homTensorHomMap_apply]
      exact TensorProduct.map_mul φ₁ φ₂ ψ₁ ψ₂)
    (by simp [homTensorHomMap_apply])

/-- The algebra isomorphism `endTensorEndAlgEquiv` sends `φ ⊗ ψ` to
`TensorProduct.map φ ψ`. -/
@[simp]
theorem endTensorEndAlgEquiv_tmul (φ : Module.End k M) (ψ : Module.End k N) :
    endTensorEndAlgEquiv k M N (φ ⊗ₜ ψ) = TensorProduct.map φ ψ := by
  simp [endTensorEndAlgEquiv, homTensorHomMap_apply]

/-- Named alias of `endTensorEndAlgEquiv`, used as a downstream reference. -/
def endTensorEndAlgEquiv_named :
    (Module.End k M) ⊗[k] (Module.End k N) ≃ₐ[k] Module.End k (M ⊗[k] N) :=
  endTensorEndAlgEquiv k M N

end FiberFunctorEnd

end
