/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.RiemannRoch

namespace Theorem22_20

open RiemannRochSpace CurveWithOrd

variable {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]


/-- **Theorem 22.20 (Serre duality for curves).** Given a nonzero differential
$\omega_0$ with divisor $W = \mathrm{div}(\omega_0)$, the Riemann–Roch space
$L(W - D)$ is naturally isomorphic as a $k$-vector space to the space of
differentials $\Omega(D)$ regular at $D$. -/
noncomputable def duality_iso
    {Ω : Type*} [AddCommGroup Ω] [Module F Ω] [Module k Ω] [IsScalarTower k F Ω]
    (divΩ : Ω → CurveDivisor C)
    (W : CurveDivisor C) (D : CurveDivisor C)
    (ω₀ : Ω) (hω₀ : ω₀ ≠ 0)
    (hW_eq : W = divΩ ω₀)
    (h_add : ∀ ω₁ ω₂ : Ω, ω₁ + ω₂ ≠ 0 →
      ∀ P, min ((divΩ ω₁) P) ((divΩ ω₂) P) ≤ (divΩ (ω₁ + ω₂)) P)
    (h_smul : ∀ (c : k) (ω : Ω), c • ω ≠ 0 →
      ∀ P, (divΩ ω) P ≤ (divΩ (c • ω)) P)
    (div_smul_F_eq : ∀ (f : F) (hf : f ≠ 0),
      divΩ (f • ω₀) = principalDivisor (Units.mk0 f hf) + divΩ ω₀)
    (omega_one_dim : ∀ ω' : Ω, ω' ≠ 0 → ∃ (f : F), f ≠ 0 ∧ ω' = f • ω₀)
    (smul_faithful : ∀ (f : F), f • ω₀ = 0 → f = 0) :
    (riemannRochSpace (F := F) (k := k) (W - D)) ≃ₗ[k]
      (differentialSpaceD (k := k) divΩ D h_add h_smul) :=
  duality_theorem_iso
    divΩ W D ω₀ hω₀ hW_eq h_add h_smul div_smul_F_eq omega_one_dim smul_faithful


end Theorem22_20
