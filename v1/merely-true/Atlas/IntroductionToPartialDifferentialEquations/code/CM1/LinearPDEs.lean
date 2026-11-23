/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-- A multi-index in $n$ variables is a function $\alpha : \{1, \ldots, n\} \to \mathbb{N}$
recording the order of differentiation in each coordinate. -/
abbrev MultiIndex' (n : ℕ) := Fin n → ℕ

/-- The order of a multi-index $\alpha = (\alpha_1, \ldots, \alpha_n)$ is
$|\alpha| = \sum_i \alpha_i$, i.e. the total number of derivatives it represents. -/
def multiIndexOrder {n : ℕ} (α : MultiIndex' n) : ℕ := ∑ i, α i

/-- The $i$-th partial derivative $\partial_{x^i} f$ of $f : \mathbb{R}^n \to \mathbb{R}$,
defined via the Fréchet derivative applied to the $i$-th standard basis vector. -/
noncomputable def partialDerivFin {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => fderiv ℝ f x (Pi.single i 1)

/-- Iterated partial derivative along a list of coordinate indices: applies the partial
derivatives $\partial_{x^{i_1}} \partial_{x^{i_2}} \cdots$ from outermost to innermost. -/
noncomputable def iteratedPartialDeriv {n : ℕ} :
    List (Fin n) → ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ)
  | [], f => f
  | i :: is, f => partialDerivFin i (iteratedPartialDeriv is f)

/-- Convert a multi-index $\alpha$ to a list of coordinate indices in which each $i$ is
repeated $\alpha_i$ times — the sequence of partial derivatives encoded by $\alpha$. -/
noncomputable def multiIndexToList {n : ℕ} (α : Fin n → ℕ) : List (Fin n) :=
  (Finset.univ.val.toList).flatMap (fun i => List.replicate (α i) i)

/-- The multi-index derivative $\partial^{\alpha} f = \partial_{x^1}^{\alpha_1} \cdots
\partial_{x^n}^{\alpha_n} f$, obtained by iterating partial derivatives according to the
list encoding of the multi-index $\alpha$. -/
noncomputable def multiIndexDeriv {n : ℕ} (α : Fin n → ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  iteratedPartialDeriv (multiIndexToList α) f

/-- The set of multi-indices of order at most $N$ in $n$ variables is finite. -/
noncomputable instance multiIndexFintype (n N : ℕ) :
    Fintype { α : MultiIndex' n // multiIndexOrder α ≤ N } := by
  classical
  have h : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N }, ∀ i, α.1 i < N + 1 := by
    intro ⟨α, hα⟩ i
    simp only
    have hi : α i ≤ ∑ j : Fin n, α j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Nat.lt_succ_of_le (le_trans hi hα)
  exact Fintype.ofInjective
    (fun ⟨α, hα⟩ => (fun i => ⟨α i, h ⟨α, hα⟩ i⟩ : Fin n → Fin (N + 1)))
    (by
      intro ⟨α₁, h₁⟩ ⟨α₂, h₂⟩ heq
      simp only [Subtype.mk.injEq] at heq ⊢
      funext i
      have := congr_fun heq i
      simp only [Fin.mk.injEq] at this
      exact this)

/-- The $N$-jet of a function at a point: stores the base point $x \in \mathbb{R}^n$ and
the values of all partial derivatives $\partial^{\alpha} u(x)$ with $|\alpha| \le N$.
This is the data on which a PDE of order $N$ acts (Definition 1.0.1). -/
structure PDEJet (n : ℕ) (N : ℕ) where
  point : Fin n → ℝ
  derivatives : { α : MultiIndex' n // multiIndexOrder α ≤ N } → ℝ

/-- The $N$-jet of the function $u$ at the point $x$: bundles $x$ together with
$\{\partial^{\alpha} u(x)\}_{|\alpha| \le N}$. -/
noncomputable def jetOf {n : ℕ} (N : ℕ) (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    PDEJet n N where
  point := x
  derivatives := fun ⟨α, _hα⟩ => multiIndexDeriv α u x

/-- A PDE of order $N$ in $n$ variables (Definition 1.0.1): an equation $F(\text{jet}) = 0$
where $F$ is a real-valued function of the $N$-jet $(u, \partial^{\alpha} u, x)$. -/
structure PDE (n : ℕ) (N : ℕ) where
  F : PDEJet n N → ℝ

/-- A linear differential operator of order at most $N$ on $\mathbb{R}^n$
(Definition 4.0.2): specified by coefficient functions $a_{\alpha}(x)$ for each multi-index
$\alpha$ with $|\alpha| \le N$, acting on a function $u$ as
$\mathcal{L} u = \sum_{|\alpha| \le N} a_{\alpha}(x) \partial^{\alpha} u$. -/
structure LinearDifferentialOperator (n : ℕ) (N : ℕ) where
  coeff : { α : MultiIndex' n // multiIndexOrder α ≤ N } → ((Fin n → ℝ) → ℝ)

namespace LinearDifferentialOperator

/-- Action of a linear differential operator on a function:
$(\mathcal{L} u)(x) = \sum_{|\alpha| \le N} a_{\alpha}(x) \, \partial^{\alpha} u(x)$. -/
noncomputable def apply {n N : ℕ} (L : LinearDifferentialOperator n N)
    (u : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∑ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
    L.coeff α x * multiIndexDeriv α.1 u x

/-- Repackage a linear differential operator as a genuine $\mathbb{R}$-linear map
$\mathcal{L} : C^{\infty}(\mathbb{R}^n) \to C^{\infty}(\mathbb{R}^n)$, given the linearity
of each multi-index derivative supplied via `hlin`. -/
noncomputable def toLinearMap {n N : ℕ} (L : LinearDifferentialOperator n N)
    (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
      ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
        multiIndexDeriv α.1 (a • u + b • v) x =
          a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x) :
    ((Fin n → ℝ) → ℝ) →ₗ[ℝ] ((Fin n → ℝ) → ℝ) where
  toFun := L.apply
  map_add' := by
    intro u v
    funext x
    simp only [apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    congr 1
    funext α
    have := hlin α 1 1 u v x
    simp only [one_smul, one_mul] at this
    rw [this]
    ring
  map_smul' := by
    intro c u
    funext x
    simp only [apply, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    funext α
    have := hlin α c 0 u 0 x
    simp only [zero_smul, add_zero, zero_mul, add_zero] at this
    rw [this]
    ring

/-- The underlying function of `L.toLinearMap` agrees with `L.apply`. -/
@[simp]
theorem toLinearMap_apply {n N : ℕ} (L : LinearDifferentialOperator n N)
    (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
      ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
        multiIndexDeriv α.1 (a • u + b • v) x =
          a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x)
    (f : (Fin n → ℝ) → ℝ) :
    (L.toLinearMap hlin) f = L.apply f := rfl

/-- Additivity: $\mathcal{L}(u + v) = \mathcal{L} u + \mathcal{L} v$. -/
theorem apply_add {n N : ℕ} (L : LinearDifferentialOperator n N)
    (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
      ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
        multiIndexDeriv α.1 (a • u + b • v) x =
          a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x)
    (u v : (Fin n → ℝ) → ℝ) :
    L.apply (u + v) = L.apply u + L.apply v := by
  have := (L.toLinearMap hlin).map_add u v
  simp only [toLinearMap_apply] at this
  exact this

/-- Homogeneity: $\mathcal{L}(c u) = c \mathcal{L} u$ for any scalar $c \in \mathbb{R}$. -/
theorem apply_smul {n N : ℕ} (L : LinearDifferentialOperator n N)
    (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
      ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
        multiIndexDeriv α.1 (a • u + b • v) x =
          a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x)
    (c : ℝ) (u : (Fin n → ℝ) → ℝ) :
    L.apply (c • u) = c • L.apply u := by
  have := (L.toLinearMap hlin).map_smul c u
  simp only [toLinearMap_apply] at this
  exact this

/-- A linear operator commutes with finite sums:
$\mathcal{L}\left(\sum_{i \in s} f_i\right) = \sum_{i \in s} \mathcal{L} f_i$. -/
theorem apply_sum {n N : ℕ} (L : LinearDifferentialOperator n N)
    (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
      ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
        multiIndexDeriv α.1 (a • u + b • v) x =
          a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x)
    {ι : Type*} (s : Finset ι) (f : ι → ((Fin n → ℝ) → ℝ)) :
    L.apply (∑ i ∈ s, f i) = ∑ i ∈ s, L.apply (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    funext x
    simp only [apply, Pi.zero_apply]
    have h0 : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
        multiIndexDeriv α.1 (0 : (Fin n → ℝ) → ℝ) x = 0 := by
      intro α
      have := hlin α 0 0 (0 : (Fin n → ℝ) → ℝ) 0 x
      simp only [zero_smul, add_zero, zero_mul] at this
      linarith
    simp only [h0, mul_zero, Finset.sum_const_zero]

  | @insert a s hna ih =>
    rw [Finset.sum_insert hna, L.apply_add hlin, ih, Finset.sum_insert hna]

/-- Subtractivity: $\mathcal{L}(u - v) = \mathcal{L} u - \mathcal{L} v$. -/
theorem apply_sub {n N : ℕ} (L : LinearDifferentialOperator n N)
    (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
      ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
        multiIndexDeriv α.1 (a • u + b • v) x =
          a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x)
    (u v : (Fin n → ℝ) → ℝ) :
    L.apply (u - v) = L.apply u - L.apply v := by
  have : u - v = u + (-1 : ℝ) • v := by simp [sub_eq_add_neg, neg_smul, one_smul]
  rw [this, L.apply_add hlin, L.apply_smul hlin]
  simp [sub_eq_add_neg, neg_smul, one_smul]

/-- Defining linearity of a linear differential operator (Definition 4.0.2, pointwise form):
$\mathcal{L}(a u + b v)(x) = a \, \mathcal{L} u(x) + b \, \mathcal{L} v(x)$
for all constants $a, b \in \mathbb{R}$, all functions $u, v$, and all $x$. -/
theorem linearity {n N : ℕ} (L : LinearDifferentialOperator n N)
    (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
      ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
        multiIndexDeriv α.1 (a • u + b • v) x =
          a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x)
    (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    L.apply (a • u + b • v) x = a * L.apply u x + b * L.apply v x := by
  simp only [apply]
  simp_rw [hlin _ a b u v x, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> (congr 1; funext α; ring)

end LinearDifferentialOperator

/-- A linear PDE of order $N$ on $\mathbb{R}^n$ (Definition 4.0.3): an equation
$\mathcal{L} u = f(x)$ specified by a linear differential operator $\mathcal{L}$ and a
source function $f$. -/
structure LinearPDE (n : ℕ) (N : ℕ) where
  L : LinearDifferentialOperator n N
  f : (Fin n → ℝ) → ℝ

/-- A linear PDE is homogeneous (Definition 4.0.4) iff its source term $f$ is identically
zero; otherwise it is called inhomogeneous. -/
def LinearPDE.IsHomogeneous {n N : ℕ} (P : LinearPDE n N) : Prop := P.f = 0

/-- Superposition principle (Proposition 4.0.1): if $u_1, \ldots, u_M$ are solutions to
the homogeneous linear PDE $\mathcal{L} u = 0$ and $c_1, \ldots, c_M \in \mathbb{R}$ are
any scalars, then $\sum_{i=1}^{M} c_i u_i$ is also a solution. -/
theorem superposition_principle {n N : ℕ}
    (L : LinearDifferentialOperator n N)
    (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
      ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
        multiIndexDeriv α.1 (a • u + b • v) x =
          a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x)
    {M : ℕ} (u : Fin M → ((Fin n → ℝ) → ℝ)) (c : Fin M → ℝ)
    (hsol : ∀ i, L.apply (u i) = 0) :
    L.apply (∑ i, c i • u i) = 0 := by
  rw [L.apply_sum hlin]
  simp only [L.apply_smul hlin, hsol, smul_zero, Finset.sum_const_zero]

/-- Relationship between inhomogeneous and homogeneous solutions (Proposition 4.0.2):
given a fixed inhomogeneous solution $u_I$ with $\mathcal{L} u_I = f$, the set $S_I$ of all
solutions to $\mathcal{L} u = f$ equals the translate of the homogeneous solution set
$S_H = \{u_H \mid \mathcal{L} u_H = 0\}$ by $u_I$, i.e.
$S_I = \{u_I + u_H \mid u_H \in S_H\}$. -/
theorem inhomogeneous_solution_set {n N : ℕ}
    (L : LinearDifferentialOperator n N)
    (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
      ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
        multiIndexDeriv α.1 (a • u + b • v) x =
          a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x)
    (f : (Fin n → ℝ) → ℝ) (u_I : (Fin n → ℝ) → ℝ) (hI : L.apply u_I = f) :
    {w : (Fin n → ℝ) → ℝ | L.apply w = f} =
      {w | ∃ u_H, L.apply u_H = 0 ∧ w = u_I + u_H} := by
  ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hw
    refine ⟨w - u_I, ?_, ?_⟩
    · have hsub := L.apply_sub hlin w u_I
      rw [hw, hI, sub_self] at hsub
      exact hsub
    · abel
  · rintro ⟨u_H, hH, rfl⟩
    have hadd := L.apply_add hlin u_I u_H
    rw [hI, hH, add_zero] at hadd
    exact hadd
