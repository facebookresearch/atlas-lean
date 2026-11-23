/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.DedekindCurve
import Atlas.AlgebraicGeometryI.code.SheafCohomology

open scoped TensorProduct
open nonZeroDivisors

noncomputable section


namespace SerreDualityDedekind

/-- `h⁰` of the ideal sheaf `I` on a Dedekind curve, defined as the `k`-dimension
of `I` viewed as a submodule. -/
def h0_ideal (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (I : Ideal A) : ℕ :=
  Module.finrank k (I : Submodule A A)

/-- `h¹` of the ideal sheaf `I`, defined via Serre duality as the `k`-dimension
of `Hom_A(I, Ω_{A/k})`. -/
def h1_ideal (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (I : Ideal A) : ℕ :=
  Module.finrank k ((I : Submodule A A) →ₗ[A] Ω[A⁄k])


/-- Serre duality definition for ideal sheaves: `h¹(I) = dim_k Hom_A(I, Ω_{A/k})`. -/
theorem serre_duality_ideal :
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (I : Ideal A),
    h1_ideal k A I = Module.finrank k ((I : Submodule A A) →ₗ[A] Ω[A⁄k]) :=
  fun _ _ _ _ _ _ _ _ _ => rfl


/-- For the unit ideal `I = ⊤`, the Serre-dual definition `h¹(I)` agrees
with `h¹(O_X)` defined as `dim_k Ω_{A/k}`. -/
theorem h1_ideal_top_eq_h1_O :
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A],
    h1_ideal k A ⊤ = DedekindCurve.h1_O k A := by
  intro k _ A _ _ _ _ _
  simp only [h1_ideal, DedekindCurve.h1_O]
  exact (((LinearEquiv.arrowCongr Submodule.topEquiv
    (LinearEquiv.refl A (Ω[A⁄k]))).restrictScalars k).trans
    (LinearMap.ringLmapEquivSelf A k (Ω[A⁄k]))).finrank_eq


/-- `Hom_A(⊤, Ω_{A/k}) ≃ₗ[k] Ω_{A/k}`: evaluating at `1 ∈ A`. -/
def homTopOmegaEquivK (k : Type*) [Field k] (A : Type*) [CommRing A]
    [Algebra k A] :
    ((⊤ : Submodule A A) →ₗ[A] Ω[A⁄k]) ≃ₗ[k] Ω[A⁄k] :=
  ((LinearEquiv.arrowCongr Submodule.topEquiv
    (LinearEquiv.refl A (Ω[A⁄k]))).restrictScalars k).trans
    (LinearMap.ringLmapEquivSelf A k (Ω[A⁄k]))

/-- The `k`-dimension of `Hom_A(⊤, Ω_{A/k})` equals that of `Ω_{A/k}`. -/
theorem finrank_hom_top_eq_finrank_omega (k : Type*) [Field k]
    (A : Type*) [CommRing A] [Algebra k A] :
    Module.finrank k ((⊤ : Submodule A A) →ₗ[A] Ω[A⁄k]) =
    Module.finrank k (Ω[A⁄k]) :=
  (homTopOmegaEquivK k A).finrank_eq


/-- Serre duality consistency check: `h¹(O_X) = dim_k Ω_{A/k}`,
combining the ideal-sheaf duality with the `Hom(⊤, Ω) ≃ Ω` equivalence. -/
theorem serre_duality_structure_sheaf_consistent
    (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] :
    DedekindCurve.h1_O k A = Module.finrank k (Ω[A⁄k]) := by


  have h1 : h1_ideal k A ⊤ = DedekindCurve.h1_O k A :=
    h1_ideal_top_eq_h1_O k A
  have h2 : h1_ideal k A ⊤ = Module.finrank k ((⊤ : Submodule A A) →ₗ[A] Ω[A⁄k]) :=
    serre_duality_ideal k A ⊤
  have h3 : Module.finrank k ((⊤ : Submodule A A) →ₗ[A] Ω[A⁄k]) =
            Module.finrank k (Ω[A⁄k]) :=
    finrank_hom_top_eq_finrank_omega k A
  linarith

/-- `h¹` of the unit ideal sheaf equals `dim_k Ω_{A/k}`, the geometric genus. -/
theorem h1_ideal_top_eq_genus
    (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] :
    h1_ideal k A ⊤ = Module.finrank k (Ω[A⁄k]) := by
  rw [serre_duality_ideal, finrank_hom_top_eq_finrank_omega]


/-- Euler characteristic of an ideal sheaf on a Dedekind curve:
`χ(I) = h⁰(I) − h¹(I)`. -/
def DedekindCurve.chi_ideal {k : Type*} [Field k] (C : DedekindCurve k) (I : Ideal C.A) : ℤ :=
  (h0_ideal k C.A I : ℤ) - (h1_ideal k C.A I : ℤ)


/-- Serre duality on `ℙ¹` (nonneg case): for `n ≥ 0`,
`dim H¹(O(n)) = dim H⁰(O(-2 - n))`. -/
theorem cech_serre_duality_P1_nonneg (k : Type) [Field k] (n : ℤ) (hn : 0 ≤ n) :
    Module.finrank k (SheafCohomology.H1 k n) =
    Module.finrank k (SheafCohomology.H0 k (-2 - n)) :=
  SheafCohomology.serre_duality_nonneg k n hn

/-- Serre duality on `ℙ¹` (negative case): for `n < 0`,
`dim H¹(O(n)) = dim H⁰(O(-2 - n))`. -/
theorem cech_serre_duality_P1_neg (k : Type) [Field k] (n : ℤ) (hn : n < 0) :
    Module.finrank k (SheafCohomology.H1 k n) =
    Module.finrank k (SheafCohomology.H0 k (-2 - n)) :=
  SheafCohomology.serre_duality_neg k n hn

/-- Serre duality on `ℙ¹` for all `n`: `dim H¹(O(n)) = dim H⁰(O(-2 - n))`. -/
theorem cech_serre_duality_P1_all (k : Type) [Field k] (n : ℤ) :
    Module.finrank k (SheafCohomology.H1 k n) =
    Module.finrank k (SheafCohomology.H0 k (-2 - n)) := by
  by_cases hn : 0 ≤ n
  · exact cech_serre_duality_P1_nonneg k n hn
  · push Not at hn
    exact cech_serre_duality_P1_neg k n hn


/-- Alternative name for `h¹` of an ideal sheaf, emphasizing the sheaf perspective. -/
def h1_ideal_sheaf (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (I : Ideal A) : ℕ :=
  Module.finrank k ((I : Submodule A A) →ₗ[A] Ω[A⁄k])

/-- Sheaf-theoretic Serre duality: `h¹(I) = dim_k Hom_A(I, Ω_{A/k})`. -/
theorem serre_duality_ideal_sheaf :
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (I : Ideal A),
    h1_ideal_sheaf k A I = Module.finrank k ((I : Submodule A A) →ₗ[A] Ω[A⁄k]) :=
  fun _ _ _ _ _ _ _ _ _ => rfl


end SerreDualityDedekind
