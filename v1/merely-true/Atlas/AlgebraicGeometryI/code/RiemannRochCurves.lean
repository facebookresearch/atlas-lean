/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
import Atlas.AlgebraicGeometryI.code.GrothendieckGroup
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Dimension.Finrank

open scoped TensorProduct
open nonZeroDivisors

noncomputable section

namespace RiemannRochCurves


/-- Euler characteristic packaged as an integer, defaulting to `1 - g_a`
(the value at the structure sheaf). -/
def eulerChar (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (structureSheafEuler : ℤ := 1 - (RiemannRochGeneral.arithmeticGenus k A : ℤ)) :
    ℤ := structureSheafEuler

/-- Genus of a curve presented by an affine Dedekind algebra: defined as
`dim_k Ω_{A/k}`. -/
def curveGenus (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  Module.finrank k (Ω[A⁄k])

/-- Degree of an ideal `I` of `A`: `dim_k (A / I)`. -/
def idealDeg (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] (I : Ideal A) : ℕ :=
  Module.finrank k (A ⧸ I)

/-- Generic rank of an `A`-module `M` (for `A` a domain): the dimension over
`Frac A` of the base-change `Frac A ⊗_A M`. -/
def moduleRk (A : Type*) [CommRing A] [IsDomain A]
    (M : Type*) [AddCommGroup M] [Module A M] : ℕ :=
  Module.finrank (FractionRing A) (FractionRing A ⊗[A] M)


open DegreeAdditivity in
/-- An additive homomorphism `ℤ × ℤ → ℤ` is determined by its values on the
generators `(1, 0)` and `(0, 1)`. -/
theorem additive_hom_determined_by_generators (f : ℤ × ℤ →+ ℤ) :
    ∀ p : ℤ × ℤ, f p = p.1 * f (1, 0) + p.2 * f (0, 1) := by
  intro ⟨r, d⟩
  show f (r, d) = r * f (1, 0) + d * f (0, 1)
  have h1 : (r, d) = (r, 0) + (0, d) := by ext <;> simp
  rw [h1, map_add]
  congr 1
  · have : (r, (0 : ℤ)) = r • (1, 0) := by ext <;> simp
    rw [this, map_zsmul, smul_eq_mul]
  · have : ((0 : ℤ), d) = d • (0, 1) := by ext <;> simp
    rw [this, map_zsmul, smul_eq_mul]

/-- Two additive homomorphisms `ℤ × ℤ → ℤ` agreeing on the two generators
`(1, 0)` and `(0, 1)` are equal. -/
theorem additive_homs_eq_of_generators_eq (f g : ℤ × ℤ →+ ℤ)
    (h_OX : f (1, 0) = g (1, 0))
    (h_Ox : f (0, 1) = g (0, 1)) :
    f = g := by
  ext ⟨r, d⟩
  rw [additive_hom_determined_by_generators f,
      additive_hom_determined_by_generators g, h_OX, h_Ox]


/-- The Riemann–Roch additive homomorphism for genus `g`:
`(r, d) ↦ d - r(g - 1)`. -/
def rrHom (g : ℤ) : ℤ × ℤ →+ ℤ where
  toFun p := p.2 - p.1 * (g - 1)
  map_zero' := by simp
  map_add' := by intro ⟨r₁, d₁⟩ ⟨r₂, d₂⟩; simp; ring

/-- Evaluation formula for `rrHom`: `rrHom g (r, d) = d - r(g - 1)`. -/
theorem rrHom_apply (g : ℤ) (r d : ℤ) : rrHom g (r, d) = d - r * (g - 1) := rfl


/-- The Riemann–Roch hom on `(1, 0)` (structure sheaf): `1 - g`. -/
theorem rr_value_structure_sheaf (g : ℤ) : rrHom g (1, 0) = 1 - g := by
  show 0 - 1 * (g - 1) = 1 - g; ring

/-- The Riemann–Roch hom on `(0, 1)` (skyscraper of length 1): `1`. -/
theorem rr_value_skyscraper (g : ℤ) : rrHom g (0, 1) = 1 := by
  show 1 - 0 * (g - 1) = 1; ring


/-- For a short exact sequence `0 → W → V → V/W → 0` of finite-dimensional
`k`-vector spaces, dimensions are additive: `dim V = dim W + dim V/W`. -/
theorem finrank_additive_ses (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (W : Submodule k V) :
    (Module.finrank k V : ℤ) =
      (Module.finrank k W : ℤ) + (Module.finrank k (V ⧸ W) : ℤ) := by
  have h := Submodule.finrank_quotient_add_finrank W
  omega

/-- Riemann–Roch for curves (Thm 24.2, Lec 24): the Euler characteristic
homomorphism is `χ(r, d) = d - r(g - 1)`, determined by its values on the
structure sheaf and a skyscraper. -/
theorem riemann_roch_curves_thm (g : ℤ) (χ : ℤ × ℤ →+ ℤ)
    (hχ_struct : χ (1, 0) = 1 - g)
    (hχ_sky : χ (0, 1) = 1) :
    ∀ r d : ℤ, χ (r, d) = d - r * (g - 1) := by
  intro r d
  have heq : χ = rrHom g :=
    additive_homs_eq_of_generators_eq χ (rrHom g)
      (by rw [hχ_struct, rr_value_structure_sheaf])
      (by rw [hχ_sky, rr_value_skyscraper])
  calc χ (r, d) = (rrHom g) (r, d) := by rw [heq]
    _ = d - r * (g - 1) := rrHom_apply g r d

/-- Genus-zero Riemann–Roch (i.e. on `ℙ¹`): `χ(r, d) = d + r`. -/
theorem rr_genus_zero (χ : ℤ × ℤ →+ ℤ)
    (hχ_struct : χ (1, 0) = 1) (hχ_sky : χ (0, 1) = 1) :
    ∀ r d : ℤ, χ (r, d) = d + r := by
  intro r d
  have := riemann_roch_curves_thm 0 χ (by simpa using hχ_struct) hχ_sky r d
  simpa using this

/-- The unit ideal has degree zero: `dim_k (A / A) = 0`. -/
theorem idealDeg_top (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] : idealDeg k A ⊤ = 0 := by
  unfold idealDeg
  haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

/-- The zero ideal has degree `dim_k A`: `idealDeg k A ⊥ = dim_k A`. -/
theorem idealDeg_bot (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] : idealDeg k A ⊥ = Module.finrank k A := by
  unfold idealDeg
  rw [LinearEquiv.finrank_eq (AlgEquiv.quotientBot k A).toLinearEquiv]

end RiemannRochCurves
