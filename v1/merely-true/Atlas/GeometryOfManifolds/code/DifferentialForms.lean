/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option autoImplicit false

/-- Axiomatic structure of a graded space $\Omega^\bullet$ of differential forms together with a space $VF$ of vector fields: includes wedge with functions and $1$-forms, exterior derivative $d$, interior product $\iota$, Lie derivative $\mathcal{L}$ and the algebraic relations they satisfy. -/
class DifferentialFormSpace (Ω : ℕ → Type*) (VF : Type*) where
  [instAddCommGroup : ∀ p, AddCommGroup (Ω p)]
  [instModule : ∀ p, Module ℝ (Ω p)]
  fMul : ∀ {p : ℕ}, Ω 0 → Ω p → Ω p
  wedge1 : ∀ {p : ℕ}, Ω 1 → Ω p → Ω (p + 1)
  d : ∀ {p : ℕ}, Ω p → Ω (p + 1)
  ι : VF → ∀ {p : ℕ}, Ω (p + 1) → Ω p
  L : VF → ∀ {p : ℕ}, Ω p → Ω p
  d_add : ∀ {p : ℕ} (α β : Ω p), d (α + β) = d α + d β
  d_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω p), d (r • α) = r • d α
  d_squared : ∀ {p : ℕ} (α : Ω p), d (d α) = 0
  d_fMul : ∀ {p : ℕ} (f : Ω 0) (α : Ω p),
    d (fMul f α) = wedge1 (d f) α + fMul f (d α)
  fMul_add_left : ∀ {p : ℕ} (f g : Ω 0) (α : Ω p),
    fMul (f + g) α = fMul f α + fMul g α
  fMul_add_right : ∀ {p : ℕ} (f : Ω 0) (α β : Ω p),
    fMul f (α + β) = fMul f α + fMul f β
  fMul_smul : ∀ {p : ℕ} (r : ℝ) (f : Ω 0) (α : Ω p),
    fMul (r • f) α = r • fMul f α
  wedge1_add_right : ∀ {p : ℕ} (ω : Ω 1) (α β : Ω p),
    wedge1 ω (α + β) = wedge1 ω α + wedge1 ω β
  wedge1_smul_right : ∀ {p : ℕ} (ω : Ω 1) (r : ℝ) (α : Ω p),
    wedge1 ω (r • α) = r • wedge1 ω α
  ι_add : ∀ (X : VF) {p : ℕ} (α β : Ω (p + 1)),
    ι X (α + β) = ι X α + ι X β
  ι_smul : ∀ (X : VF) {p : ℕ} (r : ℝ) (α : Ω (p + 1)),
    ι X (r • α) = r • ι X α
  ι_fMul : ∀ (X : VF) {p : ℕ} (f : Ω 0) (α : Ω (p + 1)),
    ι X (fMul f α) = fMul f (ι X α)
  ι_wedge1 : ∀ (X : VF) {p : ℕ} (ω : Ω 1) (α : Ω (p + 1)),
    ι X (wedge1 ω α) = fMul (ι X ω) α - wedge1 ω (ι X α)
  ι_squared : ∀ (X : VF) {p : ℕ} (α : Ω (p + 1 + 1)), ι X (ι X α) = 0
  ι_ι_anticomm : ∀ (X Y : VF) {p : ℕ} (α : Ω (p + 1 + 1)),
    ι X (ι Y α) = -(ι Y (ι X α))

  L_add : ∀ (X : VF) {p : ℕ} (α β : Ω p),
    L X (α + β) = L X α + L X β
  L_smul : ∀ (X : VF) {p : ℕ} (r : ℝ) (α : Ω p),
    L X (r • α) = r • L X α
  L_zero_eq_ι_d : ∀ (X : VF) (f : Ω 0), L X f = ι X (d f)
  L_comm_d : ∀ (X : VF) {p : ℕ} (α : Ω p), L X (d α) = d (L X α)
  L_fMul : ∀ (X : VF) {p : ℕ} (f : Ω 0) (α : Ω p),
    L X (fMul f α) = fMul (L X f) α + fMul f (L X α)
  ext_fdα : ∀ {p : ℕ} (T : Ω (p + 1) → Ω (p + 1)),
    (∀ (α β : Ω (p + 1)), T (α + β) = T α + T β) →
    (∀ (r : ℝ) (α : Ω (p + 1)), T (r • α) = r • T α) →
    (∀ (f : Ω 0) (α : Ω p), T (fMul f (d α)) = 0) →
    ∀ (β : Ω (p + 1)), T β = 0
  ι_one_form_nondegenerate : ∀ (α : Ω 1),
    (∀ (X : VF), ι X α = (0 : Ω 0)) → α = 0
  ι_two_form_nondegenerate : ∀ (ω : Ω 2),
    (∀ (X : VF), ι X ω = (0 : Ω 1)) → ω = 0

attribute [reducible, instance] DifferentialFormSpace.instAddCommGroup
attribute [reducible, instance] DifferentialFormSpace.instModule

/-- Provides a compatible $\mathbb{C}$-module structure on each $\Omega^p$ via scalar-tower with $\mathbb{R}$, used for complex-valued differential forms. -/
class HasComplexScalars (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  [instComplexModule : ∀ p, Module ℂ (Ω p)]
  [instScalarTower : ∀ p, IsScalarTower ℝ ℂ (Ω p)]
  [instSMulCommClass : ∀ p, SMulCommClass ℝ ℂ (Ω p)]

attribute [instance] HasComplexScalars.instComplexModule
attribute [instance] HasComplexScalars.instScalarTower
attribute [instance] HasComplexScalars.instSMulCommClass

namespace DifferentialFormSpace

variable {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]

/-- Multiplication of a function by the zero $p$-form yields zero: $f \cdot 0 = 0$. -/
lemma fMul_zero {p : ℕ} (f : Ω 0) : inst.fMul f (0 : Ω p) = 0 := by
  have h : inst.fMul f (0 : Ω p) + inst.fMul f (0 : Ω p) =
           inst.fMul f (0 : Ω p) := by
    rw [← inst.fMul_add_right, add_zero]
  have h2 := congr_arg (· - inst.fMul f (0 : Ω p)) h
  simp [add_sub_cancel_right] at h2; exact h2

/-- The exterior derivative of the zero form is zero: $d\,0 = 0$. -/
lemma d_zero_val {p : ℕ} : inst.d (0 : Ω p) = (0 : Ω (p + 1)) := by
  have h := inst.d_smul (0 : ℝ) (0 : Ω p)
  simp [zero_smul] at h; exact h

/-- Interior product with the zero form is zero: $\iota_X 0 = 0$. -/
lemma ι_zero_val (X : VF) {p : ℕ} :
    inst.ι X (0 : Ω (p + 1)) = (0 : Ω p) := by
  have h := inst.ι_smul X (0 : ℝ) (0 : Ω (p + 1))
  simp [zero_smul] at h; exact h

/-- The exterior derivative commutes with negation: $d(-\alpha) = -d\alpha$. -/
lemma d_neg {p : ℕ} (α : Ω p) : inst.d (-α) = -(inst.d α) := by
  have h := inst.d_smul (-1 : ℝ) α; simp at h; exact h

/-- Inductive step in the proof of Cartan's magic formula: from the relation $d(\mathcal{L}_X \gamma) = d(\iota_X d\gamma)$ at degree $p$, deduce $\mathcal{L}_X \beta = d(\iota_X \beta) + \iota_X(d\beta)$ at degree $p+1$. -/
theorem cartan_step (X : VF) {p : ℕ}
    (ih : ∀ (γ : Ω p), inst.d (inst.L X γ) = inst.d (inst.ι X (inst.d γ)))
    (β : Ω (p + 1)) :
    inst.L X β = inst.d (inst.ι X β) + inst.ι X (inst.d β) := by

  have key : inst.L X β - inst.d (inst.ι X β) - inst.ι X (inst.d β) = 0 := by
    apply inst.ext_fdα
      (fun β => inst.L X β - inst.d (inst.ι X β) - inst.ι X (inst.d β))
    ·
      intro a b
      simp only [inst.L_add, inst.ι_add, inst.d_add]
      abel
    ·
      intro r a
      simp only [inst.L_smul, inst.ι_smul, inst.d_smul]
      rw [smul_sub, smul_sub]
    ·
      intro f α

      have lhs_eq : inst.L X (inst.fMul f (inst.d α)) =
        inst.fMul (inst.ι X (inst.d f)) (inst.d α) +
        inst.fMul f (inst.d (inst.ι X (inst.d α))) := by
        rw [inst.L_fMul, inst.L_comm_d, inst.L_zero_eq_ι_d, ih]

      have d_fdα : inst.d (inst.fMul f (inst.d α)) =
        inst.wedge1 (inst.d f) (inst.d α) := by
        rw [inst.d_fMul, inst.d_squared, fMul_zero, add_zero]

      have rhs_eq : inst.d (inst.ι X (inst.fMul f (inst.d α))) +
        inst.ι X (inst.d (inst.fMul f (inst.d α))) =
        inst.fMul (inst.ι X (inst.d f)) (inst.d α) +
        inst.fMul f (inst.d (inst.ι X (inst.d α))) := by
        rw [inst.ι_fMul, inst.d_fMul, d_fdα, inst.ι_wedge1]
        abel
      rw [lhs_eq, ← rhs_eq]; abel

  have heq : inst.L X β = inst.L X β - inst.d (inst.ι X β) -
    inst.ι X (inst.d β) + (inst.d (inst.ι X β) + inst.ι X (inst.d β)) := by abel
  rw [key, zero_add] at heq; exact heq

/-- Cartan's magic formula: $\mathcal{L}_X \alpha = d(\iota_X \alpha) + \iota_X(d\alpha)$ on any differential form. -/
theorem cartan_formula (X : VF) {p : ℕ} (α : Ω (p + 1)) :
    inst.L X α = inst.d (inst.ι X α) + inst.ι X (inst.d α) := by
  induction p with
  | zero =>

    exact cartan_step X (fun γ => by rw [inst.L_zero_eq_ι_d]) α
  | succ n ih_ind =>

    exact cartan_step X (fun γ => by
      rw [ih_ind γ, inst.d_add, inst.d_squared, zero_add]) α

/-- A differential form $\alpha$ is closed when $d\alpha = 0$. -/
def IsClosed' (VF : Type*) [inst : DifferentialFormSpace Ω VF] {p : ℕ} (α : Ω p) : Prop :=
  inst.d α = 0

/-- A differential $(p+1)$-form $\alpha$ is exact when $\alpha = d\beta$ for some $p$-form $\beta$. -/
def IsExact' (VF : Type*) [inst : DifferentialFormSpace Ω VF] {p : ℕ} (α : Ω (p + 1)) : Prop :=
  ∃ (β : Ω p), α = inst.d β

/-- Every exact form is closed, since $d^2 = 0$. -/
theorem exact_is_closed {p : ℕ} (α : Ω (p + 1)) (h : IsExact' VF α) : IsClosed' VF α := by
  obtain ⟨β, hβ⟩ := h
  unfold IsClosed'
  rw [hβ, inst.d_squared]

/-- The setoid on closed $(p+1)$-forms whose quotient yields the de Rham cohomology $H^{p+1}_{dR}$: $\alpha \sim \beta$ iff $\alpha - \beta$ is exact. -/
def deRhamSetoid (p : ℕ) :
    Setoid {α : Ω (p + 1) // IsClosed' VF (inst := inst) α} where
  r α β := IsExact' VF (inst := inst) (α.val - β.val)
  iseqv := {
    refl := fun _ => ⟨0, by rw [sub_self]; exact d_zero_val.symm⟩
    symm := by
      intro a b ⟨γ, hγ⟩
      exact ⟨-γ, by rw [d_neg, ← hγ, neg_sub]⟩
    trans := by
      intro a b c ⟨δ₁, h₁⟩ ⟨δ₂, h₂⟩
      exact ⟨δ₁ + δ₂, by
        have : (↑a : Ω (p + 1)) - (↑c : Ω (p + 1)) =
          ((↑a : Ω (p + 1)) - (↑b : Ω (p + 1))) +
          ((↑b : Ω (p + 1)) - (↑c : Ω (p + 1))) := by abel
        rw [this, h₁, h₂, inst.d_add]⟩
  }

end DifferentialFormSpace

/-- Marker class for a differential form space modelled on Euclidean space of positive dimension `dim`. -/
class IsEuclideanDFS (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF] where
  dim : ℕ
  dim_pos : 0 < dim



/-- A morphism of differential form spaces: a pullback on forms that is linear and commutes with the exterior derivative. -/
structure DFSMorphism (Ω₁ : ℕ → Type*) (VF₁ : Type*)
    (Ω₂ : ℕ → Type*) (VF₂ : Type*)
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂] where
  pullback : ∀ {p : ℕ}, Ω₂ p → Ω₁ p
  pullback_add : ∀ {p : ℕ} (α β : Ω₂ p),
    pullback (α + β) = pullback α + pullback β
  pullback_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω₂ p),
    pullback (r • α) = r • pullback α
  pullback_comm_d : ∀ {p : ℕ} (α : Ω₂ p),
    pullback (inst₂.d α) = inst₁.d (pullback α)

/-- The pullback of a closed form along a morphism of differential form spaces is closed. -/
theorem DFSMorphism.pullback_closed {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂)
    {p : ℕ} (α : Ω₂ p) (h : DifferentialFormSpace.IsClosed' VF₂ α) :
    DifferentialFormSpace.IsClosed' VF₁ (φ.pullback α) := by
  unfold DifferentialFormSpace.IsClosed' at *
  rw [← φ.pullback_comm_d, h]

  have : φ.pullback (0 : Ω₂ (p + 1)) = 0 := by
    have := φ.pullback_smul (0 : ℝ) (0 : Ω₂ (p + 1))
    simp [zero_smul] at this; exact this
  exact this

/-- The pullback of an exact form along a morphism of differential form spaces is exact. -/
theorem DFSMorphism.pullback_exact {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂)
    {p : ℕ} (α : Ω₂ (p + 1)) (h : DifferentialFormSpace.IsExact' VF₂ α) :
    DifferentialFormSpace.IsExact' VF₁ (φ.pullback α) := by
  obtain ⟨β, hβ⟩ := h
  exact ⟨φ.pullback β, by rw [hβ, φ.pullback_comm_d]⟩

/-- The identity morphism of differential form spaces, with trivial pullback. -/
def DFSMorphism.id {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] : DFSMorphism Ω VF Ω VF where
  pullback α := α
  pullback_add _ _ := rfl
  pullback_smul _ _ := rfl
  pullback_comm_d _ := rfl

/-- The identity DFS-morphism acts as the identity on forms. -/
@[simp]
theorem DFSMorphism.id_pullback {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {p : ℕ} (α : Ω p) : (@DFSMorphism.id Ω VF inst).pullback α = α := rfl
