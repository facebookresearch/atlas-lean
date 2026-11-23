/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.RiemannRoch

open WeilDifferential in
/-- **Theorem 22.14.** The space $\Omega$ of Weil differentials of the function
field $F/k$ is a one-dimensional $F$-vector space: $\dim_F \Omega = 1$. -/
theorem weil_differentials_dim_eq_one
    {F : Type*} [Field F]
    {k : Type*} [Field k] [Algebra k F]
    {Ω : Type*} [AddCommGroup Ω] [Module F Ω] [Module k Ω]
    [Nontrivial Ω]
    (hsd : WeilDifferentialSubspaceData F k Ω) :
    Module.finrank F Ω = 1 :=
  weil_differentials_finrank_eq_one (F := F) (k := k) hsd

/-- Any two nonzero Weil differentials are proportional over $F$: there exists a
nonzero scalar $f \in F$ with $\omega_2 = f \cdot \omega_1$. -/
theorem weil_differentials_one_dim_basis
    {F : Type*} [Field F]
    {k : Type*} [Field k] [Algebra k F]
    {Ω : Type*} [AddCommGroup Ω] [Module F Ω] [Module k Ω]
    [Nontrivial Ω]
    (hsd : WeilDifferentialSubspaceData F k Ω)
    (ω₁ ω₂ : Ω) (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0) :
    ∃ f : F, f ≠ 0 ∧ ω₂ = f • ω₁ :=
  WeilDifferential.omega_one_dim_of_proportional
    (WeilDifferential.weil_differentials_proportional (F := F) (k := k) hsd) ω₁ ω₂ hω₁ hω₂

/-- Every Weil differential $\omega$ is an $F$-multiple of any fixed nonzero
differential $\omega_0$. -/
theorem weil_differentials_span_singleton
    {F : Type*} [Field F]
    {k : Type*} [Field k] [Algebra k F]
    {Ω : Type*} [AddCommGroup Ω] [Module F Ω] [Module k Ω]
    [Nontrivial Ω]
    (hsd : WeilDifferentialSubspaceData F k Ω)
    (ω₀ : Ω) (hω₀ : ω₀ ≠ 0) (ω : Ω) :
    ∃ f : F, ω = f • ω₀ := by
  by_cases hω : ω = 0
  · exact ⟨0, by simp [hω]⟩
  · obtain ⟨f, _, hf⟩ := weil_differentials_one_dim_basis (F := F) (k := k) hsd ω₀ ω hω₀ hω
    exact ⟨f, hf⟩

/-- The action of $F$ on a nonzero Weil differential is faithful: if
$f \cdot \omega_0 = 0$ and $\omega_0 \neq 0$, then $f = 0$. -/
theorem weil_differentials_faithful_action
    {F : Type*} [Field F]
    {k : Type*} [Field k] [Algebra k F]
    {Ω : Type*} [AddCommGroup Ω] [Module F Ω] [Module k Ω]
    (ω₀ : Ω) (hω₀ : ω₀ ≠ 0) (f : F) (hf : f • ω₀ = 0) :
    f = 0 := by
  by_contra hf_ne
  have : f • ω₀ ≠ 0 := by
    intro h
    have := congr_arg (f⁻¹ • ·) h
    simp [smul_smul, inv_mul_cancel₀ hf_ne] at this
    exact hω₀ this
  exact absurd hf this
