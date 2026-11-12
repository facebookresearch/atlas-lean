/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Prod

noncomputable section

open Module (finrank)

namespace Grassmannian

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

/-- Grassmannian chart at a point `V` with chosen complement `V'`: a linear map `V → V'` is sent
to its graph, viewed as a subspace of `W` via the splitting `W ≃ V × V'`. -/
def chart (V V' : Submodule F W) (hc : IsCompl V V')
    (φ : V →ₗ[F] V') : Submodule F W :=
  (LinearMap.graph φ).map (Submodule.prodEquivOfIsCompl V V' hc).toLinearMap

/-- The chart sends the zero map to the basepoint `V` itself. -/
theorem chart_zero (V V' : Submodule F W) (hc : IsCompl V V') :
    chart V V' hc 0 = V := by
  ext w
  simp only [chart, Submodule.mem_map, LinearMap.mem_graph_iff,
    LinearMap.zero_apply, LinearEquiv.coe_toLinearMap]
  constructor
  · rintro ⟨⟨a, b⟩, hb, heq⟩
    change b = 0 at hb
    subst hb
    simp only [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero] at heq
    rw [← heq]; exact a.2
  · intro hw
    exact ⟨⟨⟨w, hw⟩, 0⟩, rfl, by
      simp only [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]⟩

/-- Chart injectivity: distinct linear maps yield distinct graph subspaces. -/
theorem chart_injective (V V' : Submodule F W) (hc : IsCompl V V') :
    Function.Injective (chart V V' hc) := by
  intro φ ψ h
  simp only [chart] at h
  have hinj := (Submodule.prodEquivOfIsCompl V V' hc).injective
  have hgraph : LinearMap.graph φ = LinearMap.graph ψ :=
    Submodule.map_injective_of_injective hinj h
  ext v
  have hmem : (v, φ v) ∈ LinearMap.graph ψ :=
    hgraph ▸ (LinearMap.mem_graph_iff φ _).2 rfl
  exact congr_arg Subtype.val ((LinearMap.mem_graph_iff ψ _).1 hmem)

/-- Tangent-space identification at `V` (Prop 37, Lec 20): `Hom(V, V') ≃ Hom(V, W / V)`. -/
def tangentSpaceIso (V V' : Submodule F W) (hc : IsCompl V V') :
    (V →ₗ[F] V') ≃ₗ[F] (V →ₗ[F] (W ⧸ V)) :=
  LinearEquiv.arrowCongr (LinearEquiv.refl F V)
    (Submodule.quotientEquivOfIsCompl V V' hc).symm

/-- Cotangent-space identification at `V`: `Hom(V', V) ≃ Hom(W / V, V)` (dual of `tangentSpaceIso`). -/
def cotangentSpaceIso (V V' : Submodule F W) (hc : IsCompl V V') :
    (V' →ₗ[F] V) ≃ₗ[F] ((W ⧸ V) →ₗ[F] V) :=
  LinearEquiv.arrowCongr (Submodule.quotientEquivOfIsCompl V V' hc).symm
    (LinearEquiv.refl F V)

/-- Explicit formula: `tangentSpaceIso` sends `φ` to the map `v ↦ [φ v] ∈ W / V`. -/
theorem tangentSpaceIso_apply (V V' : Submodule F W) (hc : IsCompl V V')
    (φ : V →ₗ[F] V') (v : V) :
    (tangentSpaceIso V V' hc φ) v = Submodule.mkQ V (φ v : W) := by
  simp [tangentSpaceIso, LinearEquiv.arrowCongr_apply,
    Submodule.quotientEquivOfIsCompl]

/-- The tangent-space identification is independent of the chosen complement: maps `φ₁, φ₂`
that agree modulo `V` produce the same element of `Hom(V, W / V)`. -/
theorem tangentSpaceIso_independent (V V'₁ V'₂ : Submodule F W)
    (h₁ : IsCompl V V'₁) (h₂ : IsCompl V V'₂)
    (φ₁ : V →ₗ[F] V'₁) (φ₂ : V →ₗ[F] V'₂)
    (hcompat : ∀ v : V, Submodule.mkQ V (φ₁ v : W) = Submodule.mkQ V (φ₂ v : W)) :
    tangentSpaceIso V V'₁ h₁ φ₁ = tangentSpaceIso V V'₂ h₂ φ₂ := by
  ext v
  rw [tangentSpaceIso_apply, tangentSpaceIso_apply]
  exact hcompat v

/-- Comparison isomorphism between tangent-space models for two different complements `V'₁, V'₂`. -/
def complementChangeIso
    (V V'₁ V'₂ : Submodule F W) (h₁ : IsCompl V V'₁) (h₂ : IsCompl V V'₂) :
    (V →ₗ[F] V'₁) ≃ₗ[F] (V →ₗ[F] V'₂) :=
  (tangentSpaceIso V V'₁ h₁).trans (tangentSpaceIso V V'₂ h₂).symm

/-- The change-of-complement isomorphism factors through the common quotient model. -/
theorem complementChangeIso_factors
    (V V'₁ V'₂ : Submodule F W) (h₁ : IsCompl V V'₁) (h₂ : IsCompl V V'₂)
    (φ : V →ₗ[F] V'₁) :
    tangentSpaceIso V V'₂ h₂ (complementChangeIso V V'₁ V'₂ h₁ h₂ φ) =
    tangentSpaceIso V V'₁ h₁ φ := by
  simp [complementChangeIso, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- Dimension of `Hom(Sub, V/Sub)` is `(dim Sub) · (dim V/Sub)`. -/
theorem tangent_finrank_eq (k : Type*) [Field k] (V : Type*) [AddCommGroup V]
    [Module k V] [Module.Finite k V] (Sub : Submodule k V) :
    finrank k (Sub →ₗ[k] (V ⧸ Sub)) = finrank k Sub * finrank k (V ⧸ Sub) :=
  Module.finrank_linearMap k k Sub (V ⧸ Sub)

/-- Dimension of `Hom(Sub, V/Sub)` as `(dim Sub) · (dim V - dim Sub)`. -/
theorem tangent_finrank_formula (k : Type*) [Field k] (V : Type*) [AddCommGroup V]
    [Module k V] [Module.Finite k V] (Sub : Submodule k V) :
    finrank k (Sub →ₗ[k] (V ⧸ Sub)) = finrank k Sub * (finrank k V - finrank k Sub) := by
  rw [tangent_finrank_eq]
  congr 1
  have h := Sub.finrank_quotient_add_finrank
  omega

/-- Explicit tangent-dimension formula `dim T_V Gr(d, n) = d(n - d)`. -/
theorem tangent_finrank_explicit (k : Type*) [Field k] (V : Type*) [AddCommGroup V]
    [Module k V] [Module.Finite k V] (Sub : Submodule k V)
    (hd : finrank k Sub = d) (hn : finrank k V = n) :
    finrank k (Sub →ₗ[k] (V ⧸ Sub)) = d * (n - d) := by
  rw [tangent_finrank_formula, hd, hn]

end Grassmannian

section TangentCone

/-- `I^{n+1} ⊆ I^n` for any ideal `I` and natural number `n`. -/
theorem ideal_pow_succ_le {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    I ^ (n + 1) ≤ I ^ n :=
  Ideal.pow_le_pow_right (Nat.le_succ n)

/-- The `n`-th graded piece `I^n / I^{n+1}` of the associated graded of `I`. -/
abbrev associatedGradedComponent (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) :=
  (I ^ n : Submodule R R) ⧸
    Submodule.comap (I ^ n).subtype ((I ^ (n + 1) : Ideal R).restrictScalars R)

/-- The canonical map `I^n → I^n / I^{n+1}` projecting onto the `n`-th graded piece. -/
def associatedGradedComponent.mk {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    (I ^ n : Submodule R R) →ₗ[R] associatedGradedComponent R I n :=
  Submodule.mkQ _

/-- The quotient map onto each graded piece is surjective. -/
theorem associatedGradedComponent.mk_surjective {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) : Function.Surjective (associatedGradedComponent.mk I n) :=
  Submodule.mkQ_surjective _

end TangentCone
