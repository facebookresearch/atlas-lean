/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.FourManifoldsSW

set_option autoImplicit false


/-- A spin-c connection on a spin-c structure: a pair of additive connections
$\nabla^\pm$ on the positive/negative spinor bundles $S^\pm$, compatible with Clifford
multiplication in the Leibniz sense
$\nabla^-_v(\gamma(u)\psi) = \gamma(u)(\nabla^+_v\psi)$. -/
structure SpinCConnection
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  nabla_plus : Ω1 → spinc.SectionsPlus → spinc.SectionsPlus
  nabla_minus : Ω1 → spinc.SectionsMinus → spinc.SectionsMinus
  nabla_plus_add : ∀ (v : Ω1) (ψ₁ ψ₂ : spinc.SectionsPlus),
    nabla_plus v (ψ₁ + ψ₂) = nabla_plus v ψ₁ + nabla_plus v ψ₂
  nabla_minus_add : ∀ (v : Ω1) (φ₁ φ₂ : spinc.SectionsMinus),
    nabla_minus v (φ₁ + φ₂) = nabla_minus v φ₁ + nabla_minus v φ₂
  leibniz_clifford : ∀ (v u : Ω1) (ψ : spinc.SectionsPlus),
    nabla_minus v (spinc.γ_plus_to_minus u ψ) =
      spinc.γ_plus_to_minus u (nabla_plus v ψ)


/-- The "difference" of two spin-c connections is recorded by a real $1$-form $a$ together
with an imaginary factor $i$, so two spin-c connections differ by $i a \otimes \mathrm{id}_{S^\pm}$. -/
structure SpinCConnectionDifference
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  a : Ω1
  imaginary_factor : ℂ := Complex.I


/-- The space of spin-c connections is an **affine space over $\Omega^1(M)$**: any two
connections differ by a $1$-form, translation by $0$ is the identity, and translation is
additive. This is the abstract statement that "any two spin-c connections differ by
$ia \otimes \mathrm{id}_{S^\pm}$". -/
class SpinCConnectionsAffine
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  ConnectionSpace : Type
  translate : Ω1 → ConnectionSpace → ConnectionSpace
  difference : ConnectionSpace → ConnectionSpace → Ω1
  translate_difference : ∀ (A B : ConnectionSpace), translate (difference A B) B = A
  difference_translate : ∀ (a : Ω1) (A : ConnectionSpace), difference (translate a A) A = a
  translate_zero : ∀ (A : ConnectionSpace), translate 0 A = A
  translate_add : ∀ (a b : Ω1) (A : ConnectionSpace),
    translate a (translate b A) = translate (a + b) A



/-- The determinant line bundle $L = \wedge^2 S^+$: sections are antisymmetric wedge
products $\psi \wedge \varphi$ of positive spinors, with $\psi \wedge \varphi = -\varphi \wedge \psi$. -/
structure DeterminantLineBundle
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  SectionsL : Type
  [instACGL : AddCommGroup SectionsL]
  [instModL : Module ℝ SectionsL]
  wedge_product : spinc.SectionsPlus → spinc.SectionsPlus → SectionsL
  wedge_antisymm : ∀ (ψ φ : spinc.SectionsPlus),
    wedge_product ψ φ = -wedge_product φ ψ

attribute [instance] DeterminantLineBundle.instACGL DeterminantLineBundle.instModL

/-- **A spin-c connection is determined by its induced connection on the determinant line
bundle $L = \wedge^2 S^+$.** The map sending a spin-c connection $A$ to the induced
connection on $L$ is a bijection. -/
class SpinCConnectionDetermination
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2)
    [aff : SpinCConnectionsAffine spinc] where
  ConnectionOnL : Type
  induced_on_L : aff.ConnectionSpace → ConnectionOnL
  connection_determines_spinc : ∀ (A₁ A₂ : aff.ConnectionSpace),
    induced_on_L A₁ = induced_on_L A₂ → A₁ = A₂
  connection_surjective : ∀ (B : ConnectionOnL),
    ∃ (A : aff.ConnectionSpace), induced_on_L A = B
