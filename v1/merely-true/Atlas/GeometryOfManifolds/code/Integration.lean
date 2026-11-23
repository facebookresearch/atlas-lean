/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.HodgeTheory

set_option autoImplicit false

open DifferentialFormSpace


/-- An integration structure on a differential form space supporting Stokes' theorem:
provides a top dimension $n$, a wedge-pairing $\langle \alpha, \beta \rangle$ on $p$-forms,
an integral $\int : \Omega^n \to \mathbb{R}$, and the Leibniz/integration-by-parts identity
$\int (d\alpha) \wedge \beta = (-1)^{p+1} \int \alpha \wedge d\beta$. -/
structure StokesIntegration
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  n : ℕ
  wedge_star : ∀ (p : ℕ), Ω p → Ω p → Ω n
  integrate : Ω n → ℝ
  linear_integrate : Ω n →ₗ[ℝ] ℝ
  linear_integrate_eq : ∀ (ω : Ω n), linear_integrate ω = integrate ω
  wedge_star_linear_left : ∀ (p : ℕ) (r : ℝ) (α₁ α₂ β : Ω p),
    wedge_star p (r • α₁ + α₂) β = r • wedge_star p α₁ β + wedge_star p α₂ β
  wedge_star_linear_right : ∀ (p : ℕ) (r : ℝ) (α β₁ β₂ : Ω p),
    wedge_star p α (r • β₁ + β₂) = r • wedge_star p α β₁ + wedge_star p α β₂
  d_top : ∀ (_p : ℕ), Ω _p → Ω _p → Ω n
  stokes_on_exact : ∀ (p : ℕ) (α β : Ω p),
    integrate (d_top p α β) = 0
  wedge_star_d : ∀ (_p : ℕ), Ω _p → Ω (_p + 1) → Ω n
  leibniz_rule : ∀ (p : ℕ) (α : Ω p) (β : Ω (p + 1)),
    integrate (wedge_star (p + 1) (inst.d α) β) =
    (-1 : ℝ)^(p + 1) • integrate (wedge_star_d p α β)


namespace StokesIntegration

variable {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]

/-- The $L^2$ inner product on $p$-forms induced by the Hodge-star pairing:
$\langle \alpha, \beta \rangle = \int \alpha \wedge \star \beta$. -/
def inner_prod (S : StokesIntegration (inst := inst)) (p : ℕ) (α β : Ω p) : ℝ :=
  S.integrate (S.wedge_star p α β)

/-- Linearity of the inner product in the first argument:
$\langle r\alpha_1 + \alpha_2, \beta \rangle = r\langle \alpha_1, \beta \rangle + \langle \alpha_2, \beta \rangle$. -/
theorem inner_product_linear (S : StokesIntegration (inst := inst))
    (p : ℕ) (r : ℝ) (α₁ α₂ β : Ω p) :
    S.inner_prod p (r • α₁ + α₂) β =
    r * S.inner_prod p α₁ β + S.inner_prod p α₂ β := by
  unfold inner_prod
  rw [S.wedge_star_linear_left]
  simp [← S.linear_integrate_eq, map_add, map_smul]


/-- Adjointness from Stokes' theorem: $\langle d\alpha, \beta \rangle = (-1)^{p+1} \int \alpha \wedge d\beta$,
identifying $d$ as (up to sign) the formal adjoint to itself in the pairing. -/
theorem stokes_adjoint_identity (S : StokesIntegration (inst := inst))
    (p : ℕ) (α : Ω p) (β : Ω (p + 1)) :
    S.inner_prod (p + 1) (inst.d α) β =
    (-1 : ℝ)^(p + 1) • S.integrate (S.wedge_star_d p α β) := by
  unfold inner_prod
  exact S.leibniz_rule p α β


end StokesIntegration
