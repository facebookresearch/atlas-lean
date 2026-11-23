/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Topology.VectorBundle.Basic

set_option autoImplicit false

noncomputable section


/-- The Seiberg–Witten gauge group $\mathcal{G} = C^\infty(M, S^1)$ on a manifold $M$. -/
abbrev SWGaugeGroup (M : Type*) [TopologicalSpace M] := C(M, Circle)

namespace SWGaugeGroup

variable {M : Type*} [TopologicalSpace M]

/-- The embedding $S^1 \hookrightarrow \mathcal{G}$ as constant maps; its image is the central stabilizer of reducible solutions. -/
def constEmb : Circle →* SWGaugeGroup M where
  toFun z := ContinuousMap.const M z
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- A gauge transformation $f \in \mathcal{G}$ is constant if $f \equiv z \in S^1$ everywhere. -/
def IsConstant (f : SWGaugeGroup M) : Prop :=
  ∃ z : Circle, f = constEmb z

end SWGaugeGroup


/-- Concrete data packaging the Seiberg–Witten setup on a $4$-manifold: spaces of connections, spinors, self-dual $2$-forms, the logarithmic derivative $f \mapsto f^{-1}df$, the Dirac operator, the self-dual curvature, Clifford multiplication, the traceless quadratic $\psi \otimes \psi^*$, and a perturbation $\mu$, together with the gauge-equivariance axioms. -/
structure ConcreteGaugeActionData
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2] where
  Connection : Type
  SpinorSection : Type
  NegativeSpinorSection : Type
  SelfDualTwoForm : Type
  [instACGConn : AddCommGroup Connection]
  [instModConn : Module ℝ Connection]
  [instACGSpinor : AddCommGroup SpinorSection]
  [instModSpinor : Module ℝ SpinorSection]
  [instACGNeg : AddCommGroup NegativeSpinorSection]
  [instModNeg : Module ℝ NegativeSpinorSection]
  [instACGSD : AddCommGroup SelfDualTwoForm]
  [instModSD : Module ℝ SelfDualTwoForm]
  instNontrivialSpinor : Nontrivial SpinorSection
  logDeriv : SWGaugeGroup M → Connection
  gaugeOnSpinor : SWGaugeGroup M → SpinorSection → SpinorSection
  supNormSq : SpinorSection → ℝ
  supNormSq_nonneg : ∀ (ψ : SpinorSection), 0 ≤ supNormSq ψ
  DiracOp : Connection → SpinorSection → NegativeSpinorSection
  selfDualCurvature : Connection → SelfDualTwoForm
  cliffordMap : SelfDualTwoForm → SpinorSection → SpinorSection
  tracelessQuadratic : SpinorSection → SpinorSection → SpinorSection
  perturbation : SelfDualTwoForm
  logDeriv_mul : ∀ (f g : SWGaugeGroup M), logDeriv (f * g) = logDeriv f + logDeriv g
  logDeriv_one : logDeriv 1 = 0
  logDeriv_const : ∀ (z : Circle), logDeriv (SWGaugeGroup.constEmb z) = 0
  gaugeOnSpinor_mul : ∀ (f g : SWGaugeGroup M) (ψ : SpinorSection),
    gaugeOnSpinor (f * g) ψ = gaugeOnSpinor f (gaugeOnSpinor g ψ)
  gaugeOnSpinor_one : ∀ (ψ : SpinorSection), gaugeOnSpinor 1 ψ = ψ
  gaugeOnSpinor_preserves_norm : ∀ (f : SWGaugeGroup M) (ψ : SpinorSection),
    supNormSq (gaugeOnSpinor f ψ) = supNormSq ψ
  gaugeOnNegSpinor : SWGaugeGroup M → NegativeSpinorSection → NegativeSpinorSection
  gaugeOnNegSpinor_zero : ∀ (f : SWGaugeGroup M), gaugeOnNegSpinor f 0 = 0
  DiracOp_gauge_equivariant : ∀ (f : SWGaugeGroup M) (A : Connection) (ψ : SpinorSection),
    DiracOp (A - (2 : ℝ) • logDeriv f) (gaugeOnSpinor f ψ) =
      gaugeOnNegSpinor f (DiracOp A ψ)
  selfDualCurvature_gauge_invariant : ∀ (f : SWGaugeGroup M) (A : Connection),
    selfDualCurvature (A - (2 : ℝ) • logDeriv f) = selfDualCurvature A
  tracelessQuadratic_gauge_invariant : ∀ (f : SWGaugeGroup M) (ψ φ : SpinorSection),
    tracelessQuadratic (gaugeOnSpinor f ψ) φ = tracelessQuadratic ψ φ

namespace ConcreteGaugeActionData

attribute [instance] instACGConn instModConn instACGSpinor instModSpinor instACGNeg instModNeg
  instACGSD instModSD instNontrivialSpinor

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
variable {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
variable (ga : @ConcreteGaugeActionData M _ _ Ω1 Ω2 _ _ _ _)

/-- The gauge action on a connection: $A \mapsto A - 2 f^{-1} df$. -/
def gaugeOnConnection (f : SWGaugeGroup M) (A : ga.Connection) : ga.Connection :=
  A - (2 : ℝ) • ga.logDeriv f

/-- The combined gauge action on pairs $(A, \psi) \mapsto (A - 2 df \cdot f^{-1}, f\psi)$. -/
def gaugeAction (f : SWGaugeGroup M) (p : ga.Connection × ga.SpinorSection) :
    ga.Connection × ga.SpinorSection :=
  (ga.gaugeOnConnection f p.1, ga.gaugeOnSpinor f p.2)

/-- The (perturbed) Seiberg–Witten equations: $D_A \psi = 0$ and $F_A^+ \cdot \varphi = \sigma(\psi)\varphi - \mu \cdot \varphi$ for all spinors $\varphi$. -/
def IsSWSolution (A : ga.Connection) (ψ : ga.SpinorSection) : Prop :=
  ga.DiracOp A ψ = 0 ∧
  (∀ φ : ga.SpinorSection,
    ga.cliffordMap (ga.selfDualCurvature A) φ =
      ga.tracelessQuadratic ψ φ - ga.cliffordMap ga.perturbation φ)

end ConcreteGaugeActionData


section Proposition1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
variable {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]

/-- Proposition 1: the gauge action $(A, \psi) \mapsto (A - 2 df \cdot f^{-1}, f\psi)$ preserves the space of SW solutions (gauge invariance of the SW equations). -/
theorem gauge_action_preserves_solutions
    (ga : @ConcreteGaugeActionData M _ _ Ω1 Ω2 _ _ _ _)
    (f : SWGaugeGroup M) (A : ga.Connection) (ψ : ga.SpinorSection)
    (hsol : ga.IsSWSolution A ψ) :
    ga.IsSWSolution (ga.gaugeAction f (A, ψ)).1 (ga.gaugeAction f (A, ψ)).2 := by
  obtain ⟨hDirac, hCurv⟩ := hsol
  refine ⟨?_, ?_⟩
  ·

    show ga.DiracOp (ga.gaugeAction f (A, ψ)).1 (ga.gaugeAction f (A, ψ)).2 = 0
    simp only [ConcreteGaugeActionData.gaugeAction, ConcreteGaugeActionData.gaugeOnConnection]
    rw [ga.DiracOp_gauge_equivariant, hDirac, ga.gaugeOnNegSpinor_zero]
  ·

    show ∀ φ, ga.cliffordMap (ga.selfDualCurvature (ga.gaugeAction f (A, ψ)).1) φ =
      ga.tracelessQuadratic (ga.gaugeAction f (A, ψ)).2 φ -
        ga.cliffordMap ga.perturbation φ
    simp only [ConcreteGaugeActionData.gaugeAction, ConcreteGaugeActionData.gaugeOnConnection]
    intro φ
    rw [ga.selfDualCurvature_gauge_invariant, ga.tracelessQuadratic_gauge_invariant]
    exact hCurv φ

end Proposition1
