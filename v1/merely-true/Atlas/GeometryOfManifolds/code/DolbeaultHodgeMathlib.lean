/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open ContinuousAlternatingMap

namespace DolbeaultHodgeMathlib

/-- The space $\Omega^k(\mathbb{R}^n)$ of (continuous) differential $k$-forms on Euclidean
$n$-space, modelled as maps from points to continuous alternating $k$-linear forms. -/
def DiffForm (n k : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ

/-- Pointwise additive group structure on $k$-forms. -/
noncomputable instance instAddCommGroup (n k : ℕ) : AddCommGroup (DiffForm n k) :=
  Pi.addCommGroup
/-- Pointwise $\mathbb{R}$-module structure on $k$-forms. -/
noncomputable instance instModule (n k : ℕ) : Module ℝ (DiffForm n k) :=
  Pi.module _ _ _

/-- Axiomatic $L^2$ inner product on differential forms of each degree, satisfying
positivity, symmetry, and bilinearity. -/
structure L2InnerProduct (n : ℕ) where
  inner : ∀ {k : ℕ}, DiffForm n k → DiffForm n k → ℝ
  inner_self_eq_zero : ∀ {k : ℕ} (α : DiffForm n k), inner α α = 0 → α = 0
  inner_self_nonneg : ∀ {k : ℕ} (α : DiffForm n k), 0 ≤ inner α α
  inner_symm : ∀ {k : ℕ} (α β : DiffForm n k), inner α β = inner β α
  inner_add_left : ∀ {k : ℕ} (α β γ : DiffForm n k),
    inner (α + β) γ = inner α γ + inner β γ
  inner_smul_left : ∀ {k : ℕ} (r : ℝ) (α β : DiffForm n k),
    inner (r • α) β = r * inner α β


/-- Mathlib `Inner` instance built from the axiomatic $L^2$ inner product. -/
@[reducible]
def L2InnerProduct.toInner {n : ℕ} (ip : L2InnerProduct n) (k : ℕ) :
    Inner ℝ (DiffForm n k) where
  inner := ip.inner

/-- Build a `PreInnerProductSpace.Core` from an `L2InnerProduct`, giving access to Mathlib's
inner-product-space machinery. -/
@[reducible]
noncomputable def L2InnerProduct.toPreCore {n : ℕ} (ip : L2InnerProduct n) (k : ℕ) :
    PreInnerProductSpace.Core ℝ (DiffForm n k) where
  inner := ip.inner
  conj_inner_symm x y := by
    change ip.inner y x = ip.inner x y
    exact ip.inner_symm y x
  re_inner_nonneg x := by
    change 0 ≤ ip.inner x x
    exact ip.inner_self_nonneg x
  add_left x y z := ip.inner_add_left x y z
  smul_left x y r := by
    change ip.inner (r • x) y = r * ip.inner x y
    exact ip.inner_smul_left r x y

/-- The seminormed group structure on $\Omega^k$ induced by the $L^2$ inner product. -/
@[reducible]
noncomputable def L2InnerProduct.toSeminormedAddCommGroup {n : ℕ}
    (ip : L2InnerProduct n) (k : ℕ) : SeminormedAddCommGroup (DiffForm n k) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ (DiffForm n k) _ _ _ (ip.toPreCore k)

/-- The Mathlib `InnerProductSpace` structure on $\Omega^k$ induced by the $L^2$ inner product. -/
@[reducible]
noncomputable def L2InnerProduct.toInnerProductSpace {n : ℕ}
    (ip : L2InnerProduct n) (k : ℕ) :
    @InnerProductSpace ℝ (DiffForm n k) _
      (ip.toSeminormedAddCommGroup k) :=
  @InnerProductSpace.ofCore ℝ (DiffForm n k) _ _ _ (ip.toPreCore k)

/-- Compatibility: the explicit `ip.inner` equals the Mathlib-derived `Inner.inner`. -/
theorem L2InnerProduct.inner_eq_mathlibInner {n : ℕ}
    (ip : L2InnerProduct n) {k : ℕ} (α β : DiffForm n k) :
    ip.inner α β =
      @Inner.inner ℝ (DiffForm n k)
        (ip.toInnerProductSpace k).toInner α β := by
  rfl

/-- Axiomatic Dolbeault data: the operators $\bar\partial$, its formal adjoint $\bar\partial^*$,
and the $\bar\partial$-Laplacian $\bar\square = \bar\partial \bar\partial^* + \bar\partial^*
\bar\partial$, satisfying $\bar\partial^2 = 0$ and linearity. -/
structure DolbeaultData (n : ℕ) where
  delbar : ∀ {k : ℕ}, DiffForm n k → DiffForm n (k + 1)
  delbar_star : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n k
  box_bar : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  delbar_sq : ∀ {k : ℕ} (α : DiffForm n k), delbar (delbar α) = 0
  delbar_add : ∀ {k : ℕ} (α β : DiffForm n k), delbar (α + β) = delbar α + delbar β
  delbar_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n k), delbar (r • α) = r • delbar α
  box_bar_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)),
    box_bar α = delbar (delbar_star α) + delbar_star (delbar α)
  delbar_star_add : ∀ {k : ℕ} (α β : DiffForm n (k + 1)),
    delbar_star (α + β) = delbar_star α + delbar_star β
  delbar_star_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n (k + 1)),
    delbar_star (r • α) = r • delbar_star α

/-- The adjointness relation $\langle \bar\partial \alpha, \beta \rangle = \langle \alpha,
\bar\partial^* \beta \rangle$ between $\bar\partial$ and $\bar\partial^*$. -/
structure HasDelbarAdjoint {n : ℕ} (ip : L2InnerProduct n) (dol : DolbeaultData n) : Prop where
  adj : ∀ {k : ℕ} (α : DiffForm n k) (β : DiffForm n (k + 1)),
    ip.inner (dol.delbar α) β = ip.inner α (dol.delbar_star β)


/-- A $\bar\square$-harmonic form is $\bar\partial$-closed: $\bar\square h = 0 \Rightarrow
\bar\partial h = 0$. -/
theorem harmonic_is_delbar_closed {n : ℕ}
    (ip : L2InnerProduct n) (dol : DolbeaultData n)
    (hadj : HasDelbarAdjoint ip dol)
    {k : ℕ} (h : DiffForm n (k + 1))
    (hBox : dol.box_bar h = 0) :
    dol.delbar h = 0 := by
  have hzero : ip.inner (dol.box_bar h) h = 0 := by
    rw [hBox]
    have : (0 : DiffForm n (k + 1)) = (0 : ℝ) • h := by simp [zero_smul]
    rw [this, ip.inner_smul_left]; ring
  rw [dol.box_bar_eq, ip.inner_add_left] at hzero
  have e1 := hadj.adj (dol.delbar_star h) h
  have e2 : ip.inner (dol.delbar_star (dol.delbar h)) h =
    ip.inner (dol.delbar h) (dol.delbar h) := by
    rw [ip.inner_symm]; exact (hadj.adj h (dol.delbar h)).symm
  rw [e1, e2] at hzero
  have n1 : (0 : ℝ) ≤ ip.inner (dol.delbar_star h) (dol.delbar_star h) :=
    ip.inner_self_nonneg _
  have n2 : (0 : ℝ) ≤ ip.inner (dol.delbar h) (dol.delbar h) := ip.inner_self_nonneg _
  exact ip.inner_self_eq_zero _ (by linarith)

/-- A $\bar\square$-harmonic form is annihilated by $\bar\partial^*$: $\bar\square h = 0
\Rightarrow \bar\partial^* h = 0$. -/
theorem harmonic_is_delbar_star_zero {n : ℕ}
    (ip : L2InnerProduct n) (dol : DolbeaultData n)
    (hadj : HasDelbarAdjoint ip dol)
    {k : ℕ} (h : DiffForm n (k + 1))
    (hBox : dol.box_bar h = 0) :
    dol.delbar_star h = 0 := by
  have hzero : ip.inner (dol.box_bar h) h = 0 := by
    rw [hBox]
    have : (0 : DiffForm n (k + 1)) = (0 : ℝ) • h := by simp [zero_smul]
    rw [this, ip.inner_smul_left]; ring
  rw [dol.box_bar_eq, ip.inner_add_left] at hzero
  have e1 := hadj.adj (dol.delbar_star h) h
  have e2 : ip.inner (dol.delbar_star (dol.delbar h)) h =
    ip.inner (dol.delbar h) (dol.delbar h) := by
    rw [ip.inner_symm]; exact (hadj.adj h (dol.delbar h)).symm
  rw [e1, e2] at hzero
  have n1 : (0 : ℝ) ≤ ip.inner (dol.delbar_star h) (dol.delbar_star h) :=
    ip.inner_self_nonneg _
  have n2 : (0 : ℝ) ≤ ip.inner (dol.delbar h) (dol.delbar h) := ip.inner_self_nonneg _
  exact ip.inner_self_eq_zero _ (by linarith)


/-- Uniqueness of the harmonic representative: if $h_1 + \bar\partial a = h_2 + \bar\partial b$
with $h_1, h_2$ both $\bar\square$-harmonic, then $h_1 = h_2$. -/
theorem box_bar_harmonic_unique {n : ℕ}
    (ip : L2InnerProduct n) (dol : DolbeaultData n)
    (hadj : HasDelbarAdjoint ip dol)
    {k : ℕ} (h₁ h₂ : DiffForm n (k + 1))
    (hHarm₁ : dol.box_bar h₁ = 0)
    (hHarm₂ : dol.box_bar h₂ = 0)
    (a b : DiffForm n k)
    (hcohom : h₁ + dol.delbar a = h₂ + dol.delbar b) :
    h₁ = h₂ := by
  have hstar1 := harmonic_is_delbar_star_zero ip dol hadj h₁ hHarm₁
  have hstar2 := harmonic_is_delbar_star_zero ip dol hadj h₂ hHarm₂

  have hdiff : h₁ - h₂ = dol.delbar b - dol.delbar a := by
    have h1 : h₁ - h₂ = (h₁ + dol.delbar a) - (h₂ + dol.delbar a) := by abel
    have h2 : dol.delbar b - dol.delbar a = (h₂ + dol.delbar b) - (h₂ + dol.delbar a) := by abel
    rw [h1, h2, hcohom]
  have hdelbar_sub : dol.delbar b - dol.delbar a = dol.delbar (b + (-1 : ℝ) • a) := by
    rw [dol.delbar_add, dol.delbar_smul]; simp [sub_eq_add_neg]

  have hsub_eq : h₁ - h₂ = h₁ + ((-1 : ℝ) • h₂) := by simp [sub_eq_add_neg]
  have hstar_diff : dol.delbar_star (h₁ - h₂) = 0 := by
    rw [hsub_eq, dol.delbar_star_add, dol.delbar_star_smul, hstar1, hstar2, smul_zero, add_zero]

  have hstar_delbar : dol.delbar_star (dol.delbar (b + (-1 : ℝ) • a)) = 0 := by
    rw [← hdelbar_sub, ← hdiff]; exact hstar_diff


  suffices hinner_zero : ip.inner (h₁ - h₂) (h₁ - h₂) = 0 from
    sub_eq_zero.mp (ip.inner_self_eq_zero _ hinner_zero)
  conv_lhs => rw [hdiff, hdelbar_sub]
  rw [ip.inner_symm, hadj.adj, hstar_delbar, ip.inner_symm]
  have : (0 : DiffForm n k) = (0 : ℝ) • (b + (-1 : ℝ) • a) := by simp [zero_smul]
  rw [this, ip.inner_smul_left]; ring





end DolbeaultHodgeMathlib
