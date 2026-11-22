/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec20GrassmannianTangent

open Module

noncomputable section

universe u v

section Proposition37Cotangent

variable (F : Type u) [Field F]
variable (W : Type v) [AddCommGroup W] [Module F W]

/-- The trace pairing on the Grassmannian: a `k`-bilinear pairing
`T_V Gr × T^*_V Gr → F`, sending `(φ, ψ) ↦ tr(ψ ∘ φ)`. -/
def grassmannianTracePairing (kk : ℕ) (V : Module.Grassmannian F W kk)
    [FiniteDimensional F V.toSubmodule] :
    (grassmannianTangentSpace F W kk V) →ₗ[F]
    (grassmannianCotangentSpace F W kk V) →ₗ[F] F where
  toFun φ := {
    toFun := fun ψ => LinearMap.trace F V.toSubmodule (ψ.comp φ)
    map_add' := by intro ψ₁ ψ₂; simp [LinearMap.add_comp, map_add]
    map_smul' := by intro c ψ; simp [LinearMap.smul_comp, map_smul]
  }
  map_add' := by intro φ₁ φ₂; ext ψ; simp [LinearMap.comp_add, map_add]
  map_smul' := by intro c φ; ext ψ; simp [LinearMap.comp_smul, map_smul]

/-- The natural map `T^*_V Gr → (T_V Gr)*` induced by the trace pairing. -/
def cotangentToDualTangent (kk : ℕ) (V : Module.Grassmannian F W kk)
    [FiniteDimensional F V.toSubmodule] :
    (grassmannianCotangentSpace F W kk V) →ₗ[F]
    Module.Dual F (grassmannianTangentSpace F W kk V) where
  toFun ψ := {
    toFun := fun φ => LinearMap.trace F V.toSubmodule (ψ.comp φ)
    map_add' := by intro φ₁ φ₂; simp [LinearMap.comp_add, map_add]
    map_smul' := by intro c φ; simp [LinearMap.comp_smul, map_smul]
  }
  map_add' := by intro ψ₁ ψ₂; ext φ; simp [LinearMap.add_comp, map_add]
  map_smul' := by intro c ψ; ext φ; simp [LinearMap.smul_comp, map_smul]

/-- Proposition 37 (Lecture 20). The cotangent space `Hom(W/V, V)` at a point `V ∈ Gr(k, W)`
has dimension `k · (dim W - k)`. -/
theorem prop37_cotangent_dim_explicit
    [FiniteDimensional F W] (kk : ℕ) (V : Module.Grassmannian F W kk) :
    Module.finrank F (grassmannianCotangentSpace F W kk V) =
      kk * (Module.finrank F W - kk) := by
  haveI : FiniteDimensional F (W ⧸ V.toSubmodule) := V.finite_quotient
  haveI : FiniteDimensional F V.toSubmodule := Submodule.finiteDimensional_of_le le_top
  haveI : Module.Free F (↥V.toSubmodule) := Module.Free.of_divisionRing F _
  haveI : Module.Free F (W ⧸ V.toSubmodule) := Module.Free.of_divisionRing F _
  change Module.finrank F ((W ⧸ V.toSubmodule) →ₗ[F] ↥V.toSubmodule) = _
  rw [Module.finrank_linearMap F F]
  rw [grassmannian_quotient_finrank F W kk V, grassmannian_submodule_finrank F W kk V]

/-- Proposition 37 (tangent form). The tangent space `Hom(V, W/V)` at a point `V ∈ Gr(k, W)`
has dimension `(dim W - k) · k`. -/
theorem prop37_tangent_dim_explicit
    [FiniteDimensional F W] (kk : ℕ) (V : Module.Grassmannian F W kk) :
    Module.finrank F (grassmannianTangentSpace F W kk V) =
      (Module.finrank F W - kk) * kk := by
  haveI : FiniteDimensional F (W ⧸ V.toSubmodule) := V.finite_quotient
  haveI : FiniteDimensional F V.toSubmodule := Submodule.finiteDimensional_of_le le_top
  haveI : Module.Free F (↥V.toSubmodule) := Module.Free.of_divisionRing F _
  haveI : Module.Free F (W ⧸ V.toSubmodule) := Module.Free.of_divisionRing F _
  change Module.finrank F (↥V.toSubmodule →ₗ[F] (W ⧸ V.toSubmodule)) = _
  rw [Module.finrank_linearMap F F]
  rw [grassmannian_quotient_finrank F W kk V, grassmannian_submodule_finrank F W kk V]

/-- The tangent and cotangent spaces at a point of the Grassmannian have equal dimension. -/
theorem prop37_tangent_cotangent_dim_eq
    [FiniteDimensional F W] (kk : ℕ) (V : Module.Grassmannian F W kk) :
    Module.finrank F (grassmannianTangentSpace F W kk V) =
    Module.finrank F (grassmannianCotangentSpace F W kk V) := by
  rw [prop37_tangent_dim_explicit, prop37_cotangent_dim_explicit]
  ring

/-- Dimension of the Grassmannian `Gr(k, n)` via its cotangent space: `k · (n - k)`. -/
theorem prop37_grassmannian_dimension
    (n kk : ℕ) [FiniteDimensional F W]
    (hW : Module.finrank F W = n)
    (V : Module.Grassmannian F W kk) :
    Module.finrank F (grassmannianCotangentSpace F W kk V) = kk * (n - kk) := by
  rw [prop37_cotangent_dim_explicit, hW]

/-- Specialisation to projective space: the cotangent space at a point of `ℙⁿ` has
dimension `n`. -/
theorem prop37_projective_cotangent_dim
    (n : ℕ) [FiniteDimensional F W]
    (hW : Module.finrank F W = n + 1)
    (V : Module.Grassmannian F W 1) :
    Module.finrank F (grassmannianCotangentSpace F W 1 V) = n := by
  rw [prop37_cotangent_dim_explicit, hW]
  simp

end Proposition37Cotangent

end
