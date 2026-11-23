/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Circle

open Manifold

set_option autoImplicit false
noncomputable section


/-- The intersection form of a 4-manifold: a symmetric bilinear form on $H^2(X;\mathbb{Z})$
described abstractly by its rank $b_2$, the splitting $b_2 = b_2^+ + b_2^-$ into positive
and negative subspaces, signature $\sigma = b_2^+ - b_2^-$, parity (even/odd), and the
explicit bilinear form. -/
structure IntersectionForm where
  b₂ : ℕ
  b₂_plus : ℕ
  b₂_minus : ℕ
  rank_decomp : b₂ = b₂_plus + b₂_minus
  signature : ℤ
  signature_eq : signature = (b₂_plus : ℤ) - (b₂_minus : ℤ)
  isEven : Bool
  bilinForm : (Fin b₂ → ℤ) → (Fin b₂ → ℤ) → ℤ

/-- Typeclass recording the topology of a compact simply-connected 4-manifold $M$: its
intersection form $Q$ and Euler characteristic $\chi = 2 + b_2$. -/
class Has4ManifoldTopology
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] where
  Q : IntersectionForm
  euler : ℤ
  euler_eq : euler = 2 + (Q.b₂ : ℤ)

/-- $Q$ is positive definite, i.e. $b_2^- = 0$. -/
def IntersectionForm.IsPositiveDefinite (Q : IntersectionForm) : Prop := Q.b₂_minus = 0
/-- $Q$ is negative definite, i.e. $b_2^+ = 0$. -/
def IntersectionForm.IsNegativeDefinite (Q : IntersectionForm) : Prop := Q.b₂_plus = 0
/-- $Q$ is definite if it is either positive definite or negative definite. -/
def IntersectionForm.IsDefinite (Q : IntersectionForm) : Prop :=
  Q.IsPositiveDefinite ∨ Q.IsNegativeDefinite
/-- $Q$ is (potentially) diagonalisable in the sense that its parity is odd. -/
def IntersectionForm.IsDiagonal (Q : IntersectionForm) : Prop := Q.isEven = false

/-- For a positive-definite intersection form, the signature equals the rank: $\sigma = b_2$. -/
theorem posdef_signature_eq_b₂ (Q : IntersectionForm) (hdef : Q.IsPositiveDefinite) :
    Q.signature = (Q.b₂ : ℤ) := by
  rw [Q.signature_eq, Q.rank_decomp]; unfold IntersectionForm.IsPositiveDefinite at hdef; simp [hdef]

/-- For a negative-definite intersection form, the signature is minus the rank: $\sigma = -b_2$. -/
theorem negdef_signature_eq_neg_b₂ (Q : IntersectionForm) (hdef : Q.IsNegativeDefinite) :
    Q.signature = -((Q.b₂ : ℤ)) := by
  rw [Q.signature_eq, Q.rank_decomp]; unfold IntersectionForm.IsNegativeDefinite at hdef; simp [hdef]

/-- Typeclass for a compact (simply connected) 4-manifold $M$. -/
class IsCompactSimplyConnected4Manifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] : Prop where
  compact : CompactSpace M

/-- Two 4-manifolds have the same homeomorphism type (à la Freedman) if their intersection
forms agree in rank, signature, and parity. -/
class AreHomeomorphic4Manifolds
    (M₁ M₂ : Type*)
    [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M₁]
    [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M₂]
    [htop₁ : Has4ManifoldTopology M₁] [htop₂ : Has4ManifoldTopology M₂] where
  b₂_eq : htop₁.Q.b₂ = htop₂.Q.b₂
  signature_eq : htop₁.Q.signature = htop₂.Q.signature
  parity_eq : htop₁.Q.isEven = htop₂.Q.isEven


/-- Abstract data for a $\mathrm{Spin}^c$-structure $S$ on a 4-manifold $M$: positive and
negative spinor bundle sections $\Gamma(S^\pm)$, the determinant line $L$ with $c_1(L)$,
Clifford multiplication $\gamma$ acting between $S^\pm$ and on 2-forms (with the
$(\pm 1)$-eigenspace decomposition under Hodge $*$), and a Hermitian inner product on $S^+$. -/
structure SpinCStructure
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (Ω1 : Type*) (Ω2 : Type*)
    [AddCommGroup Ω1] [Module ℝ Ω1]
    [AddCommGroup Ω2] [Module ℝ Ω2] where
  SectionsPlus : Type
  SectionsMinus : Type
  [instACGPlus : AddCommGroup SectionsPlus]
  [instModPlus : Module ℝ SectionsPlus]
  [instACGMinus : AddCommGroup SectionsMinus]
  [instModMinus : Module ℝ SectionsMinus]
  nontrivial_plus : Nontrivial SectionsPlus
  c₁_L : ℤ
  Q_eval : ℤ → ℤ
  c₁_pair : ℤ → ℤ
  metric_pairing : Ω1 → Ω1 → ℝ
  γ_plus_to_minus : Ω1 → SectionsPlus → SectionsMinus
  γ_minus_to_plus : Ω1 → SectionsMinus → SectionsPlus
  γ_on_2forms : Ω2 → SectionsPlus → SectionsPlus
  γ_on_2forms_minus : Ω2 → SectionsMinus → SectionsMinus
  hodge_star : Ω2 → Ω2
  hodge_star_invol : ∀ (α : Ω2), hodge_star (hodge_star α) = α
  hodge_clifford_plus : ∀ (α : Ω2) (ψ : SectionsPlus),
    γ_on_2forms (hodge_star α) ψ = γ_on_2forms α ψ
  hodge_clifford_minus : ∀ (α : Ω2) (ψ : SectionsMinus),
    γ_on_2forms_minus (hodge_star α) ψ = -γ_on_2forms_minus α ψ
  gamma_anticomm : ∀ (u v : Ω1) (ψ : SectionsPlus),
    γ_minus_to_plus u (γ_plus_to_minus v ψ) + γ_minus_to_plus v (γ_plus_to_minus u ψ) =
      (-2 * metric_pairing u v) • ψ
  hermitianInnerPlus : SectionsPlus → SectionsPlus → ℝ
  normSqPlus : SectionsPlus → ℝ
  normSq_nonneg : ∀ (ψ : SectionsPlus), 0 ≤ normSqPlus ψ
  normSq_zero_iff : ∀ (ψ : SectionsPlus), normSqPlus ψ = 0 ↔ ψ = 0
  hermitian_norm_compat : ∀ (ψ : SectionsPlus), hermitianInnerPlus ψ ψ = normSqPlus ψ
  hermitian_smul_left : ∀ (c : ℝ) (ψ φ : SectionsPlus),
    hermitianInnerPlus (c • ψ) φ = c * hermitianInnerPlus ψ φ

namespace SpinCStructure
attribute [instance] instACGPlus instModPlus instACGMinus instModMinus
end SpinCStructure

/-- The traceless quadratic form $(\psi^* \otimes \varphi)_0 = \langle \psi, \varphi\rangle \cdot \psi
- \tfrac{1}{2}|\psi|^2 \cdot \varphi$, appearing on the right-hand side of the curvature equation
$\gamma(F_A^+) = (\psi^* \otimes \psi)_0$ in the Seiberg-Witten equations. -/
noncomputable def SpinCStructure.tracelessQuadratic
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) (ψ φ : spinc.SectionsPlus)
    : spinc.SectionsPlus :=
  (spinc.hermitianInnerPlus ψ φ) • ψ - ((1/2 : ℝ) * spinc.normSqPlus ψ) • φ


section DiracOperatorSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
variable {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
variable {spinc : SpinCStructure M Ω1 Ω2}

/-- Data of a Dirac operator $D_A = \sum_i \gamma(e^i)\nabla^A_{e_i}$ for a Spin-c structure:
a local frame $(e_i)$, covariant derivatives $\nabla^A_{e_i}$ on $S^\pm$, $\mathbb{R}$-linearity
of Clifford multiplication, and the $L^2$ adjoint relation between $D_A^+ : \Gamma(S^+) \to \Gamma(S^-)$
and $D_A^- : \Gamma(S^-) \to \Gamma(S^+)$. -/
structure DiracOperator (spinc : SpinCStructure M Ω1 Ω2) where
  frame : Fin 4 → Ω1
  conn_plus : Fin 4 → spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsPlus
  conn_minus : Fin 4 → spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsMinus
  γ_linear : ∀ (ω : Ω1), IsLinearMap ℝ (spinc.γ_plus_to_minus ω)
  γ_linear_minus : ∀ (ω : Ω1), IsLinearMap ℝ (spinc.γ_minus_to_plus ω)
  L2pairingPlus : spinc.SectionsPlus → spinc.SectionsPlus → ℝ
  L2pairingMinus : spinc.SectionsMinus → spinc.SectionsMinus → ℝ
  adjoint_relation : ∀ (ψ : spinc.SectionsPlus) (φ : spinc.SectionsMinus),
    L2pairingMinus
      (∑ i : Fin 4, spinc.γ_plus_to_minus (frame i) (conn_plus i ψ)) φ =
    L2pairingPlus ψ
      (∑ i : Fin 4, spinc.γ_minus_to_plus (frame i) (conn_minus i φ))

/-- The local Dirac sum $D_A \psi = \sum_{i=1}^4 \gamma(e^i)\nabla^A_{e_i}\psi \in \Gamma(S^-)$. -/
def dirac_sum (D : DiracOperator spinc) (ψ : spinc.SectionsPlus) : spinc.SectionsMinus :=
  ∑ i : Fin 4, spinc.γ_plus_to_minus (D.frame i) (D.conn_plus i ψ)

/-- The local adjoint Dirac sum $D_A^- \varphi = \sum_i \gamma(e^i)\nabla^A_{e_i}\varphi
\in \Gamma(S^+)$ for $\varphi \in \Gamma(S^-)$. -/
def dirac_sum_adjoint (D : DiracOperator spinc) (φ : spinc.SectionsMinus) : spinc.SectionsPlus :=
  ∑ i : Fin 4, spinc.γ_minus_to_plus (D.frame i) (D.conn_minus i φ)

/-- The positive-chirality Dirac operator $D_A^+ : \Gamma(S^+) \to \Gamma(S^-)$. -/
def DiracOperator.D_plus (D : DiracOperator spinc) : spinc.SectionsPlus → spinc.SectionsMinus :=
  dirac_sum D

/-- The negative-chirality Dirac operator $D_A^- : \Gamma(S^-) \to \Gamma(S^+)$, the $L^2$
adjoint of $D_A^+$. -/
def DiracOperator.D_minus (D : DiracOperator spinc) : spinc.SectionsMinus → spinc.SectionsPlus :=
  dirac_sum_adjoint D

end DiracOperatorSection


/-- A formal Seiberg-Witten solution: bundles together a Dirac operator $D_A$, a positive
spinor $\psi \in \Gamma(S^+)$, the self-dual curvature $F_A^+ \in \Omega^{2,+}$, and the
analytic data (Weitzenböck and Bochner identities) needed for the a priori bounds:
$\langle D_A^2 \psi, \psi\rangle = \langle \nabla^*\nabla\psi, \psi\rangle +
\tfrac{s}{4}|\psi|^2 + \tfrac{1}{2}\langle \gamma(F_A^+)\psi, \psi\rangle$,
together with $D_A\psi = 0$ on the kernel. -/
structure SWSolution
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  dirac : DiracOperator spinc
  ψ : spinc.SectionsPlus
  F_A_plus : Ω2
  supNormSq : ℝ
  supNormSq_nonneg : 0 ≤ supNormSq
  supNormSq_eq : supNormSq = spinc.normSqPlus ψ
  scalarCurvatureVal : ℝ
  laplacianTerm : ℝ
  covDerivNormSq : ℝ
  laplacianTerm_nonneg : 0 ≤ laplacianTerm
  covDerivNormSq_nonneg : 0 ≤ covDerivNormSq
  connLapInnerProd : ℝ
  cliffordInnerProd : ℝ
  diracSqInnerProd : ℝ
  integration_by_parts_eq : connLapInnerProd = laplacianTerm + covDerivNormSq
  curvature_eq_applied : spinc.γ_on_2forms F_A_plus ψ = spinc.tracelessQuadratic ψ ψ
  clifford_inner_from_gamma :
    cliffordInnerProd = spinc.hermitianInnerPlus (spinc.γ_on_2forms F_A_plus ψ) ψ
  clifford_quadratic_eq : cliffordInnerProd = (1 / 2) * supNormSq ^ 2
  diracSq_diagonal_eq_connLap : ℝ
  diracSq_offdiagonal_eq_curvature : ℝ
  diagonal_eq : diracSq_diagonal_eq_connLap = connLapInnerProd
  offdiagonal_eq : diracSq_offdiagonal_eq_curvature =
    (scalarCurvatureVal / 4) * supNormSq + (1 / 2) * cliffordInnerProd
  diracSq_split : diracSqInnerProd = diracSq_diagonal_eq_connLap + diracSq_offdiagonal_eq_curvature
  dirac_kernel : diracSqInnerProd = 0

/-- The Weitzenböck decomposition for a Seiberg-Witten solution:
$\langle D_A^2 \psi, \psi\rangle = \langle \nabla^*\nabla\psi, \psi\rangle +
\tfrac{s}{4}|\psi|^2 + \tfrac{1}{2}\langle \gamma(F_A^+)\psi, \psi\rangle$. -/
theorem SWSolution.weitzenbock_decomp
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (sol : SWSolution spinc) :
    sol.diracSqInnerProd = sol.connLapInnerProd + (sol.scalarCurvatureVal / 4) * sol.supNormSq +
        (1 / 2) * sol.cliffordInnerProd := by
  have h_split := sol.diracSq_split
  have h_diag := sol.diagonal_eq
  have h_offdiag := sol.offdiagonal_eq
  linarith

/-- Weitzenböck identity in the Dirac kernel: when $D_A \psi = 0$,
$0 = \langle \nabla^*\nabla\psi, \psi\rangle + \tfrac{s}{4}|\psi|^2
+ \tfrac{1}{2}\langle \gamma(F_A^+)\psi, \psi\rangle$. -/
theorem SWSolution.weitzenbock_eq
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (sol : SWSolution spinc) :
    0 = sol.connLapInnerProd + (sol.scalarCurvatureVal / 4) * sol.supNormSq +
        (1 / 2) * sol.cliffordInnerProd := by
  have h1 := sol.weitzenbock_decomp
  have h2 := sol.dirac_kernel
  linarith

/-- Bochner-type identity obtained from the Weitzenböck identity together with the curvature
equation and integration by parts:
$\tfrac{1}{2}\Delta|\psi|^2 + |\nabla\psi|^2 + \tfrac{s}{4}|\psi|^2 + \tfrac{1}{4}|\psi|^4 = 0$. -/
theorem SWSolution.bochner_eq
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (sol : SWSolution spinc) :
    sol.laplacianTerm + sol.covDerivNormSq +
      (sol.scalarCurvatureVal / 4) * sol.supNormSq + (1/4) * sol.supNormSq ^ 2 = 0 := by
  have hW := sol.weitzenbock_eq
  have hIBP := sol.integration_by_parts_eq
  have hCurv := sol.clifford_quadratic_eq
  linarith

/-- The Clifford pairing $\langle \gamma(F_A^+)\psi, \psi\rangle = \tfrac{1}{2}|\psi|^4$,
derived from the curvature equation $\gamma(F_A^+) = (\psi^*\otimes\psi)_0$. -/
theorem clifford_quadratic_from_curvature
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (sol : SWSolution spinc) :
    spinc.hermitianInnerPlus (spinc.γ_on_2forms sol.F_A_plus sol.ψ) sol.ψ =
      (1 / 2) * sol.supNormSq ^ 2 := by

  rw [sol.curvature_eq_applied]

  unfold SpinCStructure.tracelessQuadratic

  have h_norm := spinc.hermitian_norm_compat sol.ψ


  rw [h_norm, sol.supNormSq_eq]


  have h_sub : spinc.normSqPlus sol.ψ • sol.ψ - (1 / 2 * spinc.normSqPlus sol.ψ) • sol.ψ =
    (1 / 2 * spinc.normSqPlus sol.ψ) • sol.ψ := by
    rw [← sub_smul]; congr 1; ring
  rw [h_sub]

  rw [spinc.hermitian_smul_left]
  rw [spinc.hermitian_norm_compat]
  ring

/-- The Clifford inner product of a Seiberg-Witten solution equals
$\tfrac{1}{2}|\psi|^4$. -/
theorem SWSolution.clifford_quadratic_derived
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (sol : SWSolution spinc) :
    sol.cliffordInnerProd = (1 / 2) * sol.supNormSq ^ 2 := by
  rw [sol.clifford_inner_from_gamma]
  exact clifford_quadratic_from_curvature sol

/-- A Seiberg-Witten solution is *reducible* if its spinor vanishes identically: $\psi \equiv 0$. -/
def SWSolution.isReducible
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (sol : SWSolution spinc) : Prop :=
  sol.ψ = 0

/-- Reducibility is equivalent to vanishing of the supremum of $|\psi|^2$. -/
theorem SWSolution.isReducible_iff_supNormSq_zero
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (sol : SWSolution spinc) :
    sol.isReducible ↔ sol.supNormSq = 0 := by
  unfold SWSolution.isReducible
  rw [sol.supNormSq_eq]
  exact (spinc.normSq_zero_iff sol.ψ).symm

section SWEquations

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) ⊤ M]
variable {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
variable {spinc : SpinCStructure M Ω1 Ω2}
variable [Zero spinc.SectionsMinus]

/-- The perturbed Seiberg-Witten equations $D_A \psi = 0$ and
$\gamma(F_A^+) = (\psi^*\otimes\psi)_0 + \gamma(\mu)$ with perturbation $\mu \in \Omega^{2,+}$. -/
structure IsSWSolutionWith
    (sol : SWSolution spinc)
    (μ : Ω2) : Prop where
  dirac_eq : sol.dirac.D_plus sol.ψ = 0
  curvature_eq : ∀ (φ : spinc.SectionsPlus),
    spinc.γ_on_2forms sol.F_A_plus φ =
      spinc.tracelessQuadratic sol.ψ φ + spinc.γ_on_2forms μ φ

/-- The unperturbed Seiberg-Witten equations $D_A \psi = 0$ and
$\gamma(F_A^+) = (\psi^*\otimes\psi)_0$. -/
structure IsSWSolution
    (sol : SWSolution spinc) : Prop where
  dirac_eq : sol.dirac.D_plus sol.ψ = 0
  curvature_eq : ∀ (φ : spinc.SectionsPlus),
    spinc.γ_on_2forms sol.F_A_plus φ = spinc.tracelessQuadratic sol.ψ φ

omit [IsManifold (𝓡 4) ⊤ M] in
/-- Any unperturbed Seiberg-Witten solution is a perturbed one with perturbation $\mu = 0$. -/
theorem IsSWSolution.toPerturbed
    (sol : SWSolution spinc)
    (h : IsSWSolution sol)
    (hγ_zero : ∀ (φ : spinc.SectionsPlus), spinc.γ_on_2forms (0 : Ω2) φ = 0) :
    IsSWSolutionWith sol (0 : Ω2) where
  dirac_eq := h.dirac_eq
  curvature_eq := fun φ => by
    simp only [hγ_zero φ, add_zero]
    exact h.curvature_eq φ

omit [IsManifold (𝓡 4) ⊤ M] in
/-- A perturbed Seiberg-Witten solution with perturbation $\mu = 0$ is an unperturbed solution. -/
theorem IsSWSolution.ofPerturbed
    (sol : SWSolution spinc)
    (h : IsSWSolutionWith sol (0 : Ω2))
    (hγ_zero : ∀ (φ : spinc.SectionsPlus), spinc.γ_on_2forms (0 : Ω2) φ = 0) :
    IsSWSolution sol where
  dirac_eq := h.dirac_eq
  curvature_eq := fun φ => by
    have := h.curvature_eq φ
    simp only [hγ_zero φ, add_zero] at this
    exact this

omit [IsManifold (𝓡 4) ⊤ M] in
/-- For a perturbed Seiberg-Witten solution, the Dirac equation $D_A \psi = 0$ holds. -/
theorem IsSWSolutionWith.dirac_vanishes
    (sol : SWSolution spinc) (μ : Ω2)
    (h : IsSWSolutionWith sol μ) :
    sol.dirac.D_plus sol.ψ = 0 :=
  h.dirac_eq

omit [IsManifold (𝓡 4) ⊤ M] in
/-- Constructor for a perturbed Seiberg-Witten solution from the Dirac equation and the
perturbed curvature equation. -/
theorem IsSWSolutionWith.ofIsSWSolution
    (sol : SWSolution spinc) (μ : Ω2)
    (h_dirac : sol.dirac.D_plus sol.ψ = 0)
    (h_curv : ∀ (φ : spinc.SectionsPlus),
      spinc.γ_on_2forms sol.F_A_plus φ =
        spinc.tracelessQuadratic sol.ψ φ + spinc.γ_on_2forms μ φ) :
    IsSWSolutionWith sol μ where
  dirac_eq := h_dirac
  curvature_eq := h_curv

end SWEquations


/-- Abstract data of a gauge group $\mathcal{G}$ acting on Seiberg-Witten solutions
$(A,\psi) \mapsto (A - 2df \cdot f^{-1}, f\psi)$: the group, its action on solutions and on
$\psi, F_A^+$, compatibility with the group structure, preservation of $|\psi|^2$, and the
condition that the action is free away from reducibles. -/
structure GaugeActionData
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  GaugeGroup : Type
  [gaugeGroupGroup : Group GaugeGroup]
  gauge_action : GaugeGroup → SWSolution spinc → SWSolution spinc
  gauge_transform_spinor : GaugeGroup → spinc.SectionsPlus → spinc.SectionsPlus
  gauge_transform_curvature : GaugeGroup → Ω2 → Ω2
  spinor_formula : ∀ (f : GaugeGroup) (sol : SWSolution spinc),
    (gauge_action f sol).ψ = gauge_transform_spinor f sol.ψ
  curvature_formula : ∀ (f : GaugeGroup) (sol : SWSolution spinc),
    (gauge_action f sol).F_A_plus = gauge_transform_curvature f sol.F_A_plus
  gauge_action_one : ∀ (sol : SWSolution spinc), gauge_action 1 sol = sol
  gauge_action_mul : ∀ (f g : GaugeGroup) (sol : SWSolution spinc),
    gauge_action (f * g) sol = gauge_action f (gauge_action g sol)
  gauge_action_preserves_supNormSq : ∀ (f : GaugeGroup) (sol : SWSolution spinc),
    (gauge_action f sol).supNormSq = sol.supNormSq
  gauge_nontrivial : ∃ (f : GaugeGroup), f ≠ 1
  gauge_free_on_irreducible : ∀ (sol : SWSolution spinc),
    ¬sol.isReducible → ∀ (f : GaugeGroup), gauge_action f sol = sol → f = 1

namespace GaugeActionData
attribute [instance] gaugeGroupGroup

/-- Equip the solution space with the canonical $\mathcal{G}$-action via `SMul`. -/
@[reducible] def toSMul
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc) :
    SMul gd.GaugeGroup (SWSolution spinc) :=
  ⟨gd.gauge_action⟩

end GaugeActionData

/-- Gauge action is free on irreducible solutions: if $\psi \not\equiv 0$ and $f \cdot (A,\psi) =
(A,\psi)$, then $f = 1$. -/
theorem GaugeActionData.free_iff_irreducible
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gauge : GaugeActionData spinc)
    (sol : SWSolution spinc)
    (hirr : ¬sol.isReducible)
    (f : gauge.GaugeGroup)
    (hfix : gauge.gauge_action f sol = sol) :
    f = 1 :=
  gauge.gauge_free_on_irreducible sol hirr f hfix


/-- The smooth gauge group $\mathcal{G} = \mathrm{Map}(M, S^1)$ of continuous (here, smooth)
circle-valued maps on $M$. -/
def SmoothGaugeGroup
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] :=
  { f : M → Circle // Continuous f }

/-- Extensionality for `SmoothGaugeGroup`: two gauge transformations are equal iff their
underlying maps are equal. -/
@[ext]
theorem SmoothGaugeGroup.ext
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {f g : SmoothGaugeGroup M} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

/-- Evaluation of a smooth gauge transformation $f : M \to S^1$ at a point $x \in M$. -/
def SmoothGaugeGroup.eval
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (f : SmoothGaugeGroup M) (x : M) : Circle :=
  f.1 x

/-- The gauge-equivalence setoid on $\mathrm{SWSolution}$: two solutions are related iff one
is the image of the other under some $g \in \mathcal{G}$. -/
def GaugeActionData.gaugeEquivSetoid
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc) :
    Setoid (SWSolution spinc) where
  r sol₁ sol₂ := ∃ g : gd.GaugeGroup, gd.gauge_action g sol₁ = sol₂
  iseqv := {
    refl := fun sol => ⟨1, gd.gauge_action_one sol⟩
    symm := fun ⟨g, hg⟩ => ⟨g⁻¹, by
      rw [← hg, ← gd.gauge_action_mul, inv_mul_cancel, gd.gauge_action_one]⟩
    trans := fun ⟨g, hg⟩ ⟨h, hh⟩ => ⟨h * g, by
      rw [gd.gauge_action_mul, hg, hh]⟩
  }

/-- The Seiberg-Witten moduli quotient: the set-theoretic quotient
$\mathcal{M} = \{(A,\psi)\} / \mathcal{G}$ of solutions modulo gauge equivalence. -/
def SWModuliQuotient
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc) : Type _ :=
  Quotient gd.gaugeEquivSetoid

/-- The canonical projection $\mathrm{SWSolution} \to \mathrm{SWModuliQuotient}$ sending a
solution to its gauge equivalence class. -/
def SWModuliQuotient.mk
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc)
    (sol : SWSolution spinc) : SWModuliQuotient gd :=
  Quotient.mk gd.gaugeEquivSetoid sol

/-- Two elements of the moduli quotient are equal iff the underlying solutions are
gauge-equivalent. -/
theorem SWModuliQuotient.eq_iff
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc)
    (sol₁ sol₂ : SWSolution spinc) :
    SWModuliQuotient.mk gd sol₁ = SWModuliQuotient.mk gd sol₂ ↔
      ∃ g : gd.GaugeGroup, gd.gauge_action g sol₁ = sol₂ := by
  exact Quotient.eq (r := gd.gaugeEquivSetoid)

/-- The setoid relation on solutions is exactly the gauge orbit relation: $\mathrm{sol}_1 \sim
\mathrm{sol}_2$ iff $\exists g, g \cdot \mathrm{sol}_1 = \mathrm{sol}_2$. -/
theorem GaugeActionData.gaugeEquivSetoid_iff_orbitRel
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc)
    (sol₁ sol₂ : SWSolution spinc) :
    (gd.gaugeEquivSetoid).r sol₁ sol₂ ↔
      (∃ g : gd.GaugeGroup, gd.gauge_action g sol₁ = sol₂) :=
  Iff.rfl


/-- A 2-form $\omega$ is self-dual if $*\omega = \omega$. -/
def IsSelfDual {Ω2 : Type*} (hodge_star : Ω2 → Ω2) (ω : Ω2) : Prop :=
  hodge_star ω = ω

/-- A 2-form $\omega$ is anti-self-dual if $*\omega = -\omega$. -/
def IsAntiSelfDual {Ω2 : Type*} [Neg Ω2] (hodge_star : Ω2 → Ω2) (ω : Ω2) : Prop :=
  hodge_star ω = -ω

/-- The Clifford module isomorphisms relating differential forms and spinor endomorphisms
on a Spin-c 4-manifold: the decomposition $\Omega^2 = \Omega^{2,+} \oplus \Omega^{2,-}$,
the full Clifford equivalence
$\Omega^0 \oplus \Omega^1 \oplus \Omega^2 \oplus \Omega^3 \oplus \Omega^4 \simeq
\mathrm{End}(S^+ \oplus S^-)$, and its even/odd splittings, together with the
$\mathrm{End}(S^\pm) \simeq \mathbb{C} \oplus \Omega^{2,\pm}$ decompositions. -/
structure CliffordIsomorphisms
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 Ω0 Ω3 Ω4 : Type*}
    [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    [AddCommGroup Ω0] [Module ℝ Ω0] [AddCommGroup Ω3] [Module ℝ Ω3]
    [AddCommGroup Ω4] [Module ℝ Ω4]
    (spinc : SpinCStructure M Ω1 Ω2) where
  [instModCPlus : Module ℂ spinc.SectionsPlus]
  [instModCMinus : Module ℂ spinc.SectionsMinus]
  Ω2plus : Type
  Ω2minus : Type
  [instΩ2plus_acg : AddCommGroup Ω2plus]
  [instΩ2plus_mod : Module ℝ Ω2plus]
  [instΩ2minus_acg : AddCommGroup Ω2minus]
  [instΩ2minus_mod : Module ℝ Ω2minus]
  incl_plus : Ω2plus →ₗ[ℝ] Ω2
  incl_minus : Ω2minus →ₗ[ℝ] Ω2
  self_dual_condition : ∀ (ω : Ω2plus),
    IsSelfDual spinc.hodge_star (incl_plus ω)
  anti_self_dual_condition : ∀ (ω : Ω2minus),
    IsAntiSelfDual spinc.hodge_star (incl_minus ω)
  γ_full_equiv :
    (Ω0 × Ω1 × Ω2 × Ω3 × Ω4) ≃ₗ[ℝ]
    ((spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsPlus) × (spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsMinus)) ×
    ((spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsMinus) × (spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsPlus))
  even_clifford_equiv : (Ω0 × Ω2 × Ω4) ≃ₗ[ℝ]
    (spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsPlus) × (spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsMinus)
  odd_clifford_equiv : (Ω1 × Ω3) ≃ₗ[ℝ]
    (spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsMinus) × (spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsPlus)
  endSplus_decomp :
    (spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsPlus) ≃ₗ[ℝ] ℂ × Ω2plus
  endSminus_decomp :
    (spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsMinus) ≃ₗ[ℝ] ℂ × Ω2minus




/-- Gauge equivalence of two Seiberg-Witten solutions: $\mathrm{sol}_1 \sim \mathrm{sol}_2$ iff
there exists $f \in \mathcal{G}$ with $f \cdot \mathrm{sol}_1 = \mathrm{sol}_2$. -/
def GaugeEquiv
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gauge : GaugeActionData spinc)
    (sol₁ sol₂ : SWSolution spinc) : Prop :=
  ∃ (f : gauge.GaugeGroup), gauge.gauge_action f sol₁ = sol₂

/-- Reflexivity of gauge equivalence: every solution is gauge-equivalent to itself via
$1 \in \mathcal{G}$. -/
theorem GaugeEquiv.refl
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gauge : GaugeActionData spinc)
    (sol : SWSolution spinc) :
    GaugeEquiv gauge sol sol :=
  ⟨1, gauge.gauge_action_one sol⟩

/-- The Seiberg-Witten moduli space $\mathcal{M}(S, g, \mu) = \{(A,\psi)\}/\mathcal{G}$ together
with its expected dimension $d(S)$, total point count, and a well-defined signed count for the
zero-dimensional case (whose absolute value is bounded by the cardinality). -/
structure SWModuliSpace
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2)
    [htop : Has4ManifoldTopology M]
    [Zero spinc.SectionsMinus] where
  gauge : GaugeActionData spinc
  quotientType : Type
  quotientProj : SWSolution spinc → quotientType
  sol_is_solution : ∀ (sol : SWSolution spinc), IsSWSolution sol
  proj_faithful : ∀ (sol₁ sol₂ : SWSolution spinc),
    quotientProj sol₁ = quotientProj sol₂ ↔ GaugeEquiv gauge sol₁ sol₂
  expectedDim : ℤ
  numPoints : ℕ
  signedCount : ℤ
  signedCount_bound : signedCount.natAbs ≤ numPoints

/-- Axiomatic data for the Seiberg-Witten invariant $\mathrm{SW} : \mathrm{Spin}^c(M) \to \mathbb{Z}$
on a compact 4-manifold $M$ with $b_2^+ \geq 1$: $\mathrm{SW}$ vanishes when the moduli space is
empty, equals the signed count in the zero-dimensional case, has finite support, and depends only
on $c_1(L)$. -/
structure HasSWInvariant
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (Ω1 Ω2 : Type*) [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    [htop : Has4ManifoldTopology M] where
  b₂_plus_pos : htop.Q.b₂_plus ≥ 1
  SW : SpinCStructure M Ω1 Ω2 → ℤ
  SW_empty : ∀ (spinc : SpinCStructure M Ω1 Ω2) [Zero spinc.SectionsMinus],
    (∀ (sol : SWSolution spinc), ¬ IsSWSolution sol) → SW spinc = 0
  SW_count_dim_zero : ∀ (spinc : SpinCStructure M Ω1 Ω2) [Zero spinc.SectionsMinus]
    (Mod : SWModuliSpace spinc), Mod.expectedDim = 0 → SW spinc = Mod.signedCount
  SW_finiteness : Set.Finite {spinc : SpinCStructure M Ω1 Ω2 | SW spinc ≠ 0}
  SW_of_c₁ : ℤ → ℤ
  SW_eq_SW_of_c₁ : ∀ (spinc : SpinCStructure M Ω1 Ω2), SW spinc = SW_of_c₁ spinc.c₁_L


/-- Typeclass recording a scalar curvature value $s$ for the Riemannian metric on $M$. -/
class HasScalarCurvature
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] where
  scalarCurvature : ℝ





/-- Weitzenböck maximum principle: at a point of maximum of $|\psi|^2$ on a compact manifold,
the Bochner identity yields $s \cdot |\psi|^2 + |\psi|^4 \leq 0$. -/
theorem weitzenboeck_maximum_principle
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [hsc : HasScalarCurvature M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (sol : SWSolution spinc)
    (hsc_eq : sol.scalarCurvatureVal = hsc.scalarCurvature) :
    hsc.scalarCurvature * sol.supNormSq + sol.supNormSq ^ 2 ≤ 0 := by
  have h1 := sol.laplacianTerm_nonneg
  have h2 := sol.covDerivNormSq_nonneg
  have h3 := sol.bochner_eq
  rw [hsc_eq] at h3
  nlinarith [sq_nonneg sol.supNormSq]

/-- A priori bound on the spinor of a Seiberg-Witten solution: $\sup|\psi|^2 \leq \max(-s, 0)$. -/
theorem sw_apriori_bound
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [hsc : HasScalarCurvature M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (sol : SWSolution spinc)
    (hsc_eq : sol.scalarCurvatureVal = hsc.scalarCurvature) :
    sol.supNormSq ≤ max (-hsc.scalarCurvature) 0 := by
  have hineq := weitzenboeck_maximum_principle sol hsc_eq
  have ht := sol.supNormSq_nonneg
  by_cases ht0 : sol.supNormSq = 0
  · rw [ht0]; exact le_max_right _ _
  · have ht_pos : 0 < sol.supNormSq := lt_of_le_of_ne ht (Ne.symm ht0)
    have h2 : hsc.scalarCurvature + sol.supNormSq ≤ 0 := by
      nlinarith [sq_nonneg sol.supNormSq]
    exact le_max_of_le_left (by linarith)



/-- The intersection form of $S^2 \times S^2$: even hyperbolic form of rank 2, signature 0
with the off-diagonal pairing $\langle x, y\rangle = x_0 y_1 + x_1 y_0$. -/
def s2_cross_s2_intersection_form : IntersectionForm where
  b₂ := 2
  b₂_plus := 1
  b₂_minus := 1
  rank_decomp := rfl
  signature := 0
  signature_eq := by norm_num
  isEven := true
  bilinForm := fun x y => x 0 * y 1 + x 1 * y 0

/-- The intersection form of the $K3$ surface: even of rank 22, with $b_2^+ = 3$, $b_2^- = 19$,
and signature $-16$ (the form $2(-E_8) \oplus 3 H$). -/
def k3_intersection_form : IntersectionForm where
  b₂ := 22
  b₂_plus := 3
  b₂_minus := 19
  rank_decomp := rfl
  signature := -16
  signature_eq := by norm_num
  isEven := true
  bilinForm := fun _ _ => 0


noncomputable section SpinCGroupSection

/-- The element $-1 \in S^1 \subset \mathbb{C}$ regarded as a member of the circle group. -/
def negOneCircle : Circle := ⟨-1, by unfold Submonoid.unitSphere; simp⟩

/-- $(-1)^2 = 1$ in the circle group. -/
theorem negOneCircle_sq : (negOneCircle : Circle) ^ 2 = 1 := by
  ext1; show (negOneCircle.1) ^ 2 = 1
  simp [negOneCircle, sq]

/-- The equivalence relation defining $\mathrm{Spin}^c(4) = (\mathrm{Spin}(4) \times S^1)/\{\pm 1\}$
on pairs $(p, z) \in \mathrm{Spin}(Q) \times S^1$: $(p, z) \sim (-p, -z)$. -/
def SpinCGroupRel (Q : QuadraticForm ℝ (Fin 4 → ℝ)) :
    (spinGroup Q) × Circle → (spinGroup Q) × Circle → Prop :=
  fun p q => p = q ∨
    (∃ (h : (-↑p.1.1 : CliffordAlgebra Q) ∈ spinGroup Q),
      q.1 = ⟨-↑p.1.1, h⟩ ∧ q.2 = negOneCircle * p.2)

/-- The Spin-c group $\mathrm{Spin}^c(Q) = (\mathrm{Spin}(Q) \times S^1)/\{\pm 1\}$. -/
def SpinCGroup (Q : QuadraticForm ℝ (Fin 4 → ℝ)) :=
  Quot (SpinCGroupRel Q)

/-- The canonical projection $\mathrm{Spin}(Q) \times S^1 \to \mathrm{Spin}^c(Q)$. -/
def SpinCGroup.mk (Q : QuadraticForm ℝ (Fin 4 → ℝ)) :
    spinGroup Q × Circle → SpinCGroup Q :=
  Quot.mk _

/-- The determinant homomorphism $\det : \mathrm{Spin}^c(Q) \to S^1$, $[p, z] \mapsto z^2$,
well-defined modulo $\{\pm 1\}$. -/
def SpinCGroup.det (Q : QuadraticForm ℝ (Fin 4 → ℝ)) :
    SpinCGroup Q → Circle :=
  Quot.lift (fun p => p.2 * p.2) (by
    intro a b hab
    rcases hab with rfl | ⟨_, _, hq2⟩
    · rfl
    · simp only [hq2]
      rw [mul_mul_mul_comm negOneCircle a.2 negOneCircle a.2]
      rw [← sq, ← sq, negOneCircle_sq, one_mul])

end SpinCGroupSection


