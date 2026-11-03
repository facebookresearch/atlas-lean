/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false

open scoped TensorProduct

namespace SymplecticGeometry


/-- The wedge product $\omega \wedge \eta$ of two scalar-valued alternating forms,
producing an alternating $(m + k)$-form on $E$. -/
noncomputable def AlternatingMap.scalarWedge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m k : ℕ} (ω : E [⋀^Fin m]→ₗ[ℝ] ℝ) (η : E [⋀^Fin k]→ₗ[ℝ] ℝ) :
    E [⋀^Fin (m + k)]→ₗ[ℝ] ℝ :=
  ((TensorProduct.lid ℝ ℝ).toLinearMap.compAlternatingMap (ω.domCoprod η)).domDomCongr
    finSumFinEquiv

/-- The $n$-th wedge power $\omega^{\wedge n} = \underbrace{\omega \wedge \cdots \wedge \omega}_{n}$
of a $2$-form, yielding a $2n$-form. -/
noncomputable def AlternatingMap.wedgePower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) : (n : ℕ) → E [⋀^Fin (2 * n)]→ₗ[ℝ] ℝ
  | 0 => AlternatingMap.constOfIsEmpty ℝ E (ι := Fin 0) 1
  | n + 1 => by
      have h : 2 * (n + 1) = 2 + 2 * n := by ring
      exact h ▸ AlternatingMap.scalarWedge ω (AlternatingMap.wedgePower ω n)


/-- A symplectic manifold of dimension $2n$: a $2$-form $\omega$ on $E$ that is closed
($d\omega = 0$) and nondegenerate (the top wedge $\omega^n$ is a volume form). -/
structure SymplecticManifold (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  ω : E → (E [⋀^Fin 2]→L[ℝ] ℝ)
  dim_eq : Module.finrank ℝ E = 2 * n
  closed : ∀ x : E, extDeriv ω x = 0
  nondegenerate : ∀ x : E, AlternatingMap.wedgePower ((ω x).toAlternatingMap) n ≠ 0


variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The musical isomorphism $\flat : T_xE \to T^*_xE$ at $x$, sending $v$ to
$\omega_x(v, \cdot)$. -/
noncomputable def SymplecticManifold.flat (S : SymplecticManifold n E) (x : E) :
    E →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) :=
  (S.ω x).curryLeft

/-- Antisymmetry of $\omega_x$: permuting inputs by $\sigma$ multiplies by $\mathrm{sgn}(\sigma)$. -/
theorem SymplecticManifold.map_perm (S : SymplecticManifold n E) (x : E)
    (v : Fin 2 → E) (σ : Equiv.Perm (Fin 2)) :
    (S.ω x) (v ∘ σ) = Equiv.Perm.sign σ • (S.ω x) v :=
  (S.ω x).map_perm v σ

/-- A symplectic form is closed: $d\omega = 0$ at every point $x$. -/
theorem SymplecticManifold.isClosed (S : SymplecticManifold n E) (x : E) :
    extDeriv S.ω x = 0 :=
  S.closed x

/-- Nondegeneracy: the top wedge power $\omega_x^n$ is nonzero at every $x$. -/
theorem SymplecticManifold.isNondegenerate (S : SymplecticManifold n E) (x : E) :
    AlternatingMap.wedgePower ((S.ω x).toAlternatingMap) n ≠ 0 :=
  S.nondegenerate x

end SymplecticGeometry
